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
% DateTime   : Thu Dec  3 11:48:40 EST 2020

% Result     : Theorem 15.76s
% Output     : CNFRefutation 15.76s
% Verified   : 
% Statistics : Number of formulae       :   46 (  69 expanded)
%              Number of clauses        :   21 (  25 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :   11
%              Number of atoms          :   76 ( 120 expanded)
%              Number of equality atoms :   45 (  67 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f30,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f33])).

fof(f56,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f40,f38])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f49,f38])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f55,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_15,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_352,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_358,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_368,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_358,c_7])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_354,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1965,plain,
    ( k1_relat_1(k7_relat_1(X0,k6_subset_1(k1_relat_1(X0),X1))) = k6_subset_1(k1_relat_1(X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_368,c_354])).

cnf(c_49693,plain,
    ( k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
    inference(superposition,[status(thm)],[c_352,c_1965])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_353,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_829,plain,
    ( k7_relat_1(sK1,k1_relat_1(sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_352,c_353])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_357,plain,
    ( k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2345,plain,
    ( k6_subset_1(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)) = k7_relat_1(sK1,k6_subset_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_352,c_357])).

cnf(c_2654,plain,
    ( k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) = k6_subset_1(sK1,k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_829,c_2345])).

cnf(c_49694,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
    inference(light_normalisation,[status(thm)],[c_49693,c_2654])).

cnf(c_14,negated_conjecture,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_52062,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_49694,c_14])).

cnf(c_52095,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_52062])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:08:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 15.76/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.76/2.49  
% 15.76/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.76/2.49  
% 15.76/2.49  ------  iProver source info
% 15.76/2.49  
% 15.76/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.76/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.76/2.49  git: non_committed_changes: false
% 15.76/2.49  git: last_make_outside_of_git: false
% 15.76/2.49  
% 15.76/2.49  ------ 
% 15.76/2.49  ------ Parsing...
% 15.76/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.76/2.49  
% 15.76/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.76/2.49  
% 15.76/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.76/2.49  
% 15.76/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.76/2.49  ------ Proving...
% 15.76/2.49  ------ Problem Properties 
% 15.76/2.49  
% 15.76/2.49  
% 15.76/2.49  clauses                                 15
% 15.76/2.49  conjectures                             2
% 15.76/2.49  EPR                                     4
% 15.76/2.49  Horn                                    15
% 15.76/2.49  unary                                   8
% 15.76/2.49  binary                                  4
% 15.76/2.49  lits                                    25
% 15.76/2.49  lits eq                                 10
% 15.76/2.49  fd_pure                                 0
% 15.76/2.49  fd_pseudo                               0
% 15.76/2.49  fd_cond                                 0
% 15.76/2.49  fd_pseudo_cond                          1
% 15.76/2.49  AC symbols                              0
% 15.76/2.49  
% 15.76/2.49  ------ Input Options Time Limit: Unbounded
% 15.76/2.49  
% 15.76/2.49  
% 15.76/2.49  ------ 
% 15.76/2.49  Current options:
% 15.76/2.49  ------ 
% 15.76/2.49  
% 15.76/2.49  
% 15.76/2.49  
% 15.76/2.49  
% 15.76/2.49  ------ Proving...
% 15.76/2.49  
% 15.76/2.49  
% 15.76/2.49  % SZS status Theorem for theBenchmark.p
% 15.76/2.49  
% 15.76/2.49   Resolution empty clause
% 15.76/2.49  
% 15.76/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.76/2.49  
% 15.76/2.49  fof(f20,conjecture,(
% 15.76/2.49    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 15.76/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.76/2.49  
% 15.76/2.49  fof(f21,negated_conjecture,(
% 15.76/2.49    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 15.76/2.49    inference(negated_conjecture,[],[f20])).
% 15.76/2.49  
% 15.76/2.49  fof(f30,plain,(
% 15.76/2.49    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 15.76/2.49    inference(ennf_transformation,[],[f21])).
% 15.76/2.49  
% 15.76/2.49  fof(f33,plain,(
% 15.76/2.49    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 15.76/2.49    introduced(choice_axiom,[])).
% 15.76/2.49  
% 15.76/2.49  fof(f34,plain,(
% 15.76/2.49    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 15.76/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f33])).
% 15.76/2.49  
% 15.76/2.49  fof(f56,plain,(
% 15.76/2.49    v1_relat_1(sK1)),
% 15.76/2.49    inference(cnf_transformation,[],[f34])).
% 15.76/2.49  
% 15.76/2.49  fof(f4,axiom,(
% 15.76/2.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 15.76/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.76/2.49  
% 15.76/2.49  fof(f40,plain,(
% 15.76/2.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.76/2.49    inference(cnf_transformation,[],[f4])).
% 15.76/2.49  
% 15.76/2.49  fof(f2,axiom,(
% 15.76/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.76/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.76/2.49  
% 15.76/2.49  fof(f38,plain,(
% 15.76/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.76/2.49    inference(cnf_transformation,[],[f2])).
% 15.76/2.49  
% 15.76/2.49  fof(f64,plain,(
% 15.76/2.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 15.76/2.49    inference(definition_unfolding,[],[f40,f38])).
% 15.76/2.49  
% 15.76/2.49  fof(f13,axiom,(
% 15.76/2.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 15.76/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.76/2.49  
% 15.76/2.49  fof(f49,plain,(
% 15.76/2.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 15.76/2.49    inference(cnf_transformation,[],[f13])).
% 15.76/2.49  
% 15.76/2.49  fof(f66,plain,(
% 15.76/2.49    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1)) )),
% 15.76/2.49    inference(definition_unfolding,[],[f49,f38])).
% 15.76/2.49  
% 15.76/2.49  fof(f18,axiom,(
% 15.76/2.49    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 15.76/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.76/2.49  
% 15.76/2.49  fof(f27,plain,(
% 15.76/2.49    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 15.76/2.49    inference(ennf_transformation,[],[f18])).
% 15.76/2.49  
% 15.76/2.49  fof(f28,plain,(
% 15.76/2.49    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 15.76/2.50    inference(flattening,[],[f27])).
% 15.76/2.50  
% 15.76/2.50  fof(f54,plain,(
% 15.76/2.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 15.76/2.50    inference(cnf_transformation,[],[f28])).
% 15.76/2.50  
% 15.76/2.50  fof(f19,axiom,(
% 15.76/2.50    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 15.76/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.76/2.50  
% 15.76/2.50  fof(f29,plain,(
% 15.76/2.50    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 15.76/2.50    inference(ennf_transformation,[],[f19])).
% 15.76/2.50  
% 15.76/2.50  fof(f55,plain,(
% 15.76/2.50    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 15.76/2.50    inference(cnf_transformation,[],[f29])).
% 15.76/2.50  
% 15.76/2.50  fof(f15,axiom,(
% 15.76/2.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)))),
% 15.76/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.76/2.50  
% 15.76/2.50  fof(f24,plain,(
% 15.76/2.50    ! [X0,X1,X2] : (k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_relat_1(X2))),
% 15.76/2.50    inference(ennf_transformation,[],[f15])).
% 15.76/2.50  
% 15.76/2.50  fof(f51,plain,(
% 15.76/2.50    ( ! [X2,X0,X1] : (k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_relat_1(X2)) )),
% 15.76/2.50    inference(cnf_transformation,[],[f24])).
% 15.76/2.50  
% 15.76/2.50  fof(f57,plain,(
% 15.76/2.50    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))),
% 15.76/2.50    inference(cnf_transformation,[],[f34])).
% 15.76/2.50  
% 15.76/2.50  cnf(c_15,negated_conjecture,
% 15.76/2.50      ( v1_relat_1(sK1) ),
% 15.76/2.50      inference(cnf_transformation,[],[f56]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_352,plain,
% 15.76/2.50      ( v1_relat_1(sK1) = iProver_top ),
% 15.76/2.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_5,plain,
% 15.76/2.50      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 15.76/2.50      inference(cnf_transformation,[],[f64]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_358,plain,
% 15.76/2.50      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 15.76/2.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_7,plain,
% 15.76/2.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
% 15.76/2.50      inference(cnf_transformation,[],[f66]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_368,plain,
% 15.76/2.50      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 15.76/2.50      inference(light_normalisation,[status(thm)],[c_358,c_7]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_12,plain,
% 15.76/2.50      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 15.76/2.50      | ~ v1_relat_1(X1)
% 15.76/2.50      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 15.76/2.50      inference(cnf_transformation,[],[f54]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_354,plain,
% 15.76/2.50      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 15.76/2.50      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 15.76/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.76/2.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_1965,plain,
% 15.76/2.50      ( k1_relat_1(k7_relat_1(X0,k6_subset_1(k1_relat_1(X0),X1))) = k6_subset_1(k1_relat_1(X0),X1)
% 15.76/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.76/2.50      inference(superposition,[status(thm)],[c_368,c_354]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_49693,plain,
% 15.76/2.50      ( k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
% 15.76/2.50      inference(superposition,[status(thm)],[c_352,c_1965]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_13,plain,
% 15.76/2.50      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 15.76/2.50      inference(cnf_transformation,[],[f55]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_353,plain,
% 15.76/2.50      ( k7_relat_1(X0,k1_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 15.76/2.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_829,plain,
% 15.76/2.50      ( k7_relat_1(sK1,k1_relat_1(sK1)) = sK1 ),
% 15.76/2.50      inference(superposition,[status(thm)],[c_352,c_353]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_9,plain,
% 15.76/2.50      ( ~ v1_relat_1(X0)
% 15.76/2.50      | k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2)) ),
% 15.76/2.50      inference(cnf_transformation,[],[f51]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_357,plain,
% 15.76/2.50      ( k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2))
% 15.76/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.76/2.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_2345,plain,
% 15.76/2.50      ( k6_subset_1(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)) = k7_relat_1(sK1,k6_subset_1(X0,X1)) ),
% 15.76/2.50      inference(superposition,[status(thm)],[c_352,c_357]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_2654,plain,
% 15.76/2.50      ( k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) = k6_subset_1(sK1,k7_relat_1(sK1,X0)) ),
% 15.76/2.50      inference(superposition,[status(thm)],[c_829,c_2345]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_49694,plain,
% 15.76/2.50      ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
% 15.76/2.50      inference(light_normalisation,[status(thm)],[c_49693,c_2654]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_14,negated_conjecture,
% 15.76/2.50      ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
% 15.76/2.50      inference(cnf_transformation,[],[f57]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_52062,plain,
% 15.76/2.50      ( k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0) ),
% 15.76/2.50      inference(demodulation,[status(thm)],[c_49694,c_14]) ).
% 15.76/2.50  
% 15.76/2.50  cnf(c_52095,plain,
% 15.76/2.50      ( $false ),
% 15.76/2.50      inference(equality_resolution_simp,[status(thm)],[c_52062]) ).
% 15.76/2.50  
% 15.76/2.50  
% 15.76/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.76/2.50  
% 15.76/2.50  ------                               Statistics
% 15.76/2.50  
% 15.76/2.50  ------ Selected
% 15.76/2.50  
% 15.76/2.50  total_time:                             1.919
% 15.76/2.50  
%------------------------------------------------------------------------------
