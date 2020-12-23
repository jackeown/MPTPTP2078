%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:48:40 EST 2020

% Result     : Theorem 7.01s
% Output     : CNFRefutation 7.01s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 120 expanded)
%              Number of clauses        :   24 (  28 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :   17
%              Number of atoms          :  127 ( 192 expanded)
%              Number of equality atoms :   77 ( 120 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f46,f58])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f60])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f43,f61])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f50,f62])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f39,f63])).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f42,f64])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f49,f64])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_14,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_434,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_440,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_459,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_440,c_7])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_436,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1917,plain,
    ( k1_relat_1(k7_relat_1(X0,k6_subset_1(k1_relat_1(X0),X1))) = k6_subset_1(k1_relat_1(X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_459,c_436])).

cnf(c_19331,plain,
    ( k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
    inference(superposition,[status(thm)],[c_434,c_1917])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_443,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_435,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_855,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_443,c_435])).

cnf(c_2216,plain,
    ( k7_relat_1(sK1,k1_relat_1(sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_434,c_855])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_438,plain,
    ( k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1068,plain,
    ( k6_subset_1(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)) = k7_relat_1(sK1,k6_subset_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_434,c_438])).

cnf(c_2235,plain,
    ( k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) = k6_subset_1(sK1,k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_2216,c_1068])).

cnf(c_19359,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
    inference(light_normalisation,[status(thm)],[c_19331,c_2235])).

cnf(c_13,negated_conjecture,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_19826,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_19359,c_13])).

cnf(c_19830,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_19826])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:33:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.01/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.01/1.48  
% 7.01/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.01/1.48  
% 7.01/1.48  ------  iProver source info
% 7.01/1.48  
% 7.01/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.01/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.01/1.48  git: non_committed_changes: false
% 7.01/1.48  git: last_make_outside_of_git: false
% 7.01/1.48  
% 7.01/1.48  ------ 
% 7.01/1.48  
% 7.01/1.48  ------ Input Options
% 7.01/1.48  
% 7.01/1.48  --out_options                           all
% 7.01/1.48  --tptp_safe_out                         true
% 7.01/1.48  --problem_path                          ""
% 7.01/1.48  --include_path                          ""
% 7.01/1.48  --clausifier                            res/vclausify_rel
% 7.01/1.48  --clausifier_options                    --mode clausify
% 7.01/1.48  --stdin                                 false
% 7.01/1.48  --stats_out                             all
% 7.01/1.48  
% 7.01/1.48  ------ General Options
% 7.01/1.48  
% 7.01/1.48  --fof                                   false
% 7.01/1.48  --time_out_real                         305.
% 7.01/1.48  --time_out_virtual                      -1.
% 7.01/1.48  --symbol_type_check                     false
% 7.01/1.48  --clausify_out                          false
% 7.01/1.48  --sig_cnt_out                           false
% 7.01/1.48  --trig_cnt_out                          false
% 7.01/1.48  --trig_cnt_out_tolerance                1.
% 7.01/1.48  --trig_cnt_out_sk_spl                   false
% 7.01/1.48  --abstr_cl_out                          false
% 7.01/1.48  
% 7.01/1.48  ------ Global Options
% 7.01/1.48  
% 7.01/1.48  --schedule                              default
% 7.01/1.48  --add_important_lit                     false
% 7.01/1.48  --prop_solver_per_cl                    1000
% 7.01/1.48  --min_unsat_core                        false
% 7.01/1.48  --soft_assumptions                      false
% 7.01/1.48  --soft_lemma_size                       3
% 7.01/1.48  --prop_impl_unit_size                   0
% 7.01/1.48  --prop_impl_unit                        []
% 7.01/1.48  --share_sel_clauses                     true
% 7.01/1.48  --reset_solvers                         false
% 7.01/1.48  --bc_imp_inh                            [conj_cone]
% 7.01/1.48  --conj_cone_tolerance                   3.
% 7.01/1.48  --extra_neg_conj                        none
% 7.01/1.48  --large_theory_mode                     true
% 7.01/1.48  --prolific_symb_bound                   200
% 7.01/1.48  --lt_threshold                          2000
% 7.01/1.48  --clause_weak_htbl                      true
% 7.01/1.48  --gc_record_bc_elim                     false
% 7.01/1.48  
% 7.01/1.48  ------ Preprocessing Options
% 7.01/1.48  
% 7.01/1.48  --preprocessing_flag                    true
% 7.01/1.48  --time_out_prep_mult                    0.1
% 7.01/1.48  --splitting_mode                        input
% 7.01/1.48  --splitting_grd                         true
% 7.01/1.48  --splitting_cvd                         false
% 7.01/1.48  --splitting_cvd_svl                     false
% 7.01/1.48  --splitting_nvd                         32
% 7.01/1.48  --sub_typing                            true
% 7.01/1.48  --prep_gs_sim                           true
% 7.01/1.48  --prep_unflatten                        true
% 7.01/1.48  --prep_res_sim                          true
% 7.01/1.48  --prep_upred                            true
% 7.01/1.48  --prep_sem_filter                       exhaustive
% 7.01/1.48  --prep_sem_filter_out                   false
% 7.01/1.48  --pred_elim                             true
% 7.01/1.48  --res_sim_input                         true
% 7.01/1.48  --eq_ax_congr_red                       true
% 7.01/1.48  --pure_diseq_elim                       true
% 7.01/1.48  --brand_transform                       false
% 7.01/1.48  --non_eq_to_eq                          false
% 7.01/1.48  --prep_def_merge                        true
% 7.01/1.48  --prep_def_merge_prop_impl              false
% 7.01/1.48  --prep_def_merge_mbd                    true
% 7.01/1.48  --prep_def_merge_tr_red                 false
% 7.01/1.48  --prep_def_merge_tr_cl                  false
% 7.01/1.48  --smt_preprocessing                     true
% 7.01/1.48  --smt_ac_axioms                         fast
% 7.01/1.48  --preprocessed_out                      false
% 7.01/1.48  --preprocessed_stats                    false
% 7.01/1.48  
% 7.01/1.48  ------ Abstraction refinement Options
% 7.01/1.48  
% 7.01/1.48  --abstr_ref                             []
% 7.01/1.48  --abstr_ref_prep                        false
% 7.01/1.48  --abstr_ref_until_sat                   false
% 7.01/1.48  --abstr_ref_sig_restrict                funpre
% 7.01/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.01/1.48  --abstr_ref_under                       []
% 7.01/1.48  
% 7.01/1.48  ------ SAT Options
% 7.01/1.48  
% 7.01/1.48  --sat_mode                              false
% 7.01/1.48  --sat_fm_restart_options                ""
% 7.01/1.48  --sat_gr_def                            false
% 7.01/1.48  --sat_epr_types                         true
% 7.01/1.48  --sat_non_cyclic_types                  false
% 7.01/1.48  --sat_finite_models                     false
% 7.01/1.48  --sat_fm_lemmas                         false
% 7.01/1.48  --sat_fm_prep                           false
% 7.01/1.48  --sat_fm_uc_incr                        true
% 7.01/1.48  --sat_out_model                         small
% 7.01/1.48  --sat_out_clauses                       false
% 7.01/1.48  
% 7.01/1.48  ------ QBF Options
% 7.01/1.48  
% 7.01/1.48  --qbf_mode                              false
% 7.01/1.48  --qbf_elim_univ                         false
% 7.01/1.48  --qbf_dom_inst                          none
% 7.01/1.48  --qbf_dom_pre_inst                      false
% 7.01/1.48  --qbf_sk_in                             false
% 7.01/1.48  --qbf_pred_elim                         true
% 7.01/1.48  --qbf_split                             512
% 7.01/1.48  
% 7.01/1.48  ------ BMC1 Options
% 7.01/1.48  
% 7.01/1.48  --bmc1_incremental                      false
% 7.01/1.48  --bmc1_axioms                           reachable_all
% 7.01/1.48  --bmc1_min_bound                        0
% 7.01/1.48  --bmc1_max_bound                        -1
% 7.01/1.48  --bmc1_max_bound_default                -1
% 7.01/1.48  --bmc1_symbol_reachability              true
% 7.01/1.48  --bmc1_property_lemmas                  false
% 7.01/1.48  --bmc1_k_induction                      false
% 7.01/1.48  --bmc1_non_equiv_states                 false
% 7.01/1.48  --bmc1_deadlock                         false
% 7.01/1.48  --bmc1_ucm                              false
% 7.01/1.48  --bmc1_add_unsat_core                   none
% 7.01/1.48  --bmc1_unsat_core_children              false
% 7.01/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.01/1.48  --bmc1_out_stat                         full
% 7.01/1.48  --bmc1_ground_init                      false
% 7.01/1.48  --bmc1_pre_inst_next_state              false
% 7.01/1.48  --bmc1_pre_inst_state                   false
% 7.01/1.48  --bmc1_pre_inst_reach_state             false
% 7.01/1.48  --bmc1_out_unsat_core                   false
% 7.01/1.48  --bmc1_aig_witness_out                  false
% 7.01/1.48  --bmc1_verbose                          false
% 7.01/1.48  --bmc1_dump_clauses_tptp                false
% 7.01/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.01/1.48  --bmc1_dump_file                        -
% 7.01/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.01/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.01/1.48  --bmc1_ucm_extend_mode                  1
% 7.01/1.48  --bmc1_ucm_init_mode                    2
% 7.01/1.48  --bmc1_ucm_cone_mode                    none
% 7.01/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.01/1.48  --bmc1_ucm_relax_model                  4
% 7.01/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.01/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.01/1.48  --bmc1_ucm_layered_model                none
% 7.01/1.48  --bmc1_ucm_max_lemma_size               10
% 7.01/1.48  
% 7.01/1.48  ------ AIG Options
% 7.01/1.48  
% 7.01/1.48  --aig_mode                              false
% 7.01/1.48  
% 7.01/1.48  ------ Instantiation Options
% 7.01/1.48  
% 7.01/1.48  --instantiation_flag                    true
% 7.01/1.48  --inst_sos_flag                         false
% 7.01/1.48  --inst_sos_phase                        true
% 7.01/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.01/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.01/1.48  --inst_lit_sel_side                     num_symb
% 7.01/1.48  --inst_solver_per_active                1400
% 7.01/1.48  --inst_solver_calls_frac                1.
% 7.01/1.48  --inst_passive_queue_type               priority_queues
% 7.01/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.01/1.48  --inst_passive_queues_freq              [25;2]
% 7.01/1.48  --inst_dismatching                      true
% 7.01/1.48  --inst_eager_unprocessed_to_passive     true
% 7.01/1.48  --inst_prop_sim_given                   true
% 7.01/1.48  --inst_prop_sim_new                     false
% 7.01/1.48  --inst_subs_new                         false
% 7.01/1.48  --inst_eq_res_simp                      false
% 7.01/1.48  --inst_subs_given                       false
% 7.01/1.48  --inst_orphan_elimination               true
% 7.01/1.48  --inst_learning_loop_flag               true
% 7.01/1.48  --inst_learning_start                   3000
% 7.01/1.48  --inst_learning_factor                  2
% 7.01/1.48  --inst_start_prop_sim_after_learn       3
% 7.01/1.48  --inst_sel_renew                        solver
% 7.01/1.48  --inst_lit_activity_flag                true
% 7.01/1.48  --inst_restr_to_given                   false
% 7.01/1.48  --inst_activity_threshold               500
% 7.01/1.48  --inst_out_proof                        true
% 7.01/1.48  
% 7.01/1.48  ------ Resolution Options
% 7.01/1.48  
% 7.01/1.48  --resolution_flag                       true
% 7.01/1.48  --res_lit_sel                           adaptive
% 7.01/1.48  --res_lit_sel_side                      none
% 7.01/1.48  --res_ordering                          kbo
% 7.01/1.48  --res_to_prop_solver                    active
% 7.01/1.48  --res_prop_simpl_new                    false
% 7.01/1.48  --res_prop_simpl_given                  true
% 7.01/1.48  --res_passive_queue_type                priority_queues
% 7.01/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.01/1.48  --res_passive_queues_freq               [15;5]
% 7.01/1.48  --res_forward_subs                      full
% 7.01/1.48  --res_backward_subs                     full
% 7.01/1.48  --res_forward_subs_resolution           true
% 7.01/1.48  --res_backward_subs_resolution          true
% 7.01/1.48  --res_orphan_elimination                true
% 7.01/1.48  --res_time_limit                        2.
% 7.01/1.48  --res_out_proof                         true
% 7.01/1.48  
% 7.01/1.48  ------ Superposition Options
% 7.01/1.48  
% 7.01/1.48  --superposition_flag                    true
% 7.01/1.48  --sup_passive_queue_type                priority_queues
% 7.01/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.01/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.01/1.48  --demod_completeness_check              fast
% 7.01/1.48  --demod_use_ground                      true
% 7.01/1.48  --sup_to_prop_solver                    passive
% 7.01/1.48  --sup_prop_simpl_new                    true
% 7.01/1.48  --sup_prop_simpl_given                  true
% 7.01/1.48  --sup_fun_splitting                     false
% 7.01/1.48  --sup_smt_interval                      50000
% 7.01/1.48  
% 7.01/1.48  ------ Superposition Simplification Setup
% 7.01/1.48  
% 7.01/1.48  --sup_indices_passive                   []
% 7.01/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.01/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.01/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.01/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.01/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.01/1.48  --sup_full_bw                           [BwDemod]
% 7.01/1.48  --sup_immed_triv                        [TrivRules]
% 7.01/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.01/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.01/1.48  --sup_immed_bw_main                     []
% 7.01/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.01/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.01/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.01/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.01/1.48  
% 7.01/1.48  ------ Combination Options
% 7.01/1.48  
% 7.01/1.48  --comb_res_mult                         3
% 7.01/1.48  --comb_sup_mult                         2
% 7.01/1.48  --comb_inst_mult                        10
% 7.01/1.48  
% 7.01/1.48  ------ Debug Options
% 7.01/1.48  
% 7.01/1.48  --dbg_backtrace                         false
% 7.01/1.48  --dbg_dump_prop_clauses                 false
% 7.01/1.48  --dbg_dump_prop_clauses_file            -
% 7.01/1.48  --dbg_out_stat                          false
% 7.01/1.48  ------ Parsing...
% 7.01/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.01/1.48  
% 7.01/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.01/1.48  
% 7.01/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.01/1.48  
% 7.01/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.01/1.48  ------ Proving...
% 7.01/1.48  ------ Problem Properties 
% 7.01/1.48  
% 7.01/1.48  
% 7.01/1.48  clauses                                 14
% 7.01/1.48  conjectures                             2
% 7.01/1.48  EPR                                     3
% 7.01/1.48  Horn                                    14
% 7.01/1.48  unary                                   7
% 7.01/1.48  binary                                  4
% 7.01/1.48  lits                                    24
% 7.01/1.48  lits eq                                 9
% 7.01/1.48  fd_pure                                 0
% 7.01/1.48  fd_pseudo                               0
% 7.01/1.48  fd_cond                                 0
% 7.01/1.48  fd_pseudo_cond                          1
% 7.01/1.48  AC symbols                              0
% 7.01/1.48  
% 7.01/1.48  ------ Schedule dynamic 5 is on 
% 7.01/1.48  
% 7.01/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.01/1.48  
% 7.01/1.48  
% 7.01/1.48  ------ 
% 7.01/1.48  Current options:
% 7.01/1.48  ------ 
% 7.01/1.48  
% 7.01/1.48  ------ Input Options
% 7.01/1.48  
% 7.01/1.48  --out_options                           all
% 7.01/1.48  --tptp_safe_out                         true
% 7.01/1.48  --problem_path                          ""
% 7.01/1.48  --include_path                          ""
% 7.01/1.48  --clausifier                            res/vclausify_rel
% 7.01/1.48  --clausifier_options                    --mode clausify
% 7.01/1.48  --stdin                                 false
% 7.01/1.48  --stats_out                             all
% 7.01/1.48  
% 7.01/1.48  ------ General Options
% 7.01/1.48  
% 7.01/1.48  --fof                                   false
% 7.01/1.48  --time_out_real                         305.
% 7.01/1.48  --time_out_virtual                      -1.
% 7.01/1.48  --symbol_type_check                     false
% 7.01/1.48  --clausify_out                          false
% 7.01/1.48  --sig_cnt_out                           false
% 7.01/1.48  --trig_cnt_out                          false
% 7.01/1.48  --trig_cnt_out_tolerance                1.
% 7.01/1.48  --trig_cnt_out_sk_spl                   false
% 7.01/1.48  --abstr_cl_out                          false
% 7.01/1.48  
% 7.01/1.48  ------ Global Options
% 7.01/1.48  
% 7.01/1.48  --schedule                              default
% 7.01/1.48  --add_important_lit                     false
% 7.01/1.48  --prop_solver_per_cl                    1000
% 7.01/1.48  --min_unsat_core                        false
% 7.01/1.48  --soft_assumptions                      false
% 7.01/1.48  --soft_lemma_size                       3
% 7.01/1.48  --prop_impl_unit_size                   0
% 7.01/1.48  --prop_impl_unit                        []
% 7.01/1.48  --share_sel_clauses                     true
% 7.01/1.48  --reset_solvers                         false
% 7.01/1.48  --bc_imp_inh                            [conj_cone]
% 7.01/1.48  --conj_cone_tolerance                   3.
% 7.01/1.48  --extra_neg_conj                        none
% 7.01/1.48  --large_theory_mode                     true
% 7.01/1.48  --prolific_symb_bound                   200
% 7.01/1.48  --lt_threshold                          2000
% 7.01/1.48  --clause_weak_htbl                      true
% 7.01/1.48  --gc_record_bc_elim                     false
% 7.01/1.48  
% 7.01/1.48  ------ Preprocessing Options
% 7.01/1.48  
% 7.01/1.48  --preprocessing_flag                    true
% 7.01/1.48  --time_out_prep_mult                    0.1
% 7.01/1.48  --splitting_mode                        input
% 7.01/1.48  --splitting_grd                         true
% 7.01/1.48  --splitting_cvd                         false
% 7.01/1.48  --splitting_cvd_svl                     false
% 7.01/1.48  --splitting_nvd                         32
% 7.01/1.48  --sub_typing                            true
% 7.01/1.48  --prep_gs_sim                           true
% 7.01/1.48  --prep_unflatten                        true
% 7.01/1.48  --prep_res_sim                          true
% 7.01/1.48  --prep_upred                            true
% 7.01/1.48  --prep_sem_filter                       exhaustive
% 7.01/1.48  --prep_sem_filter_out                   false
% 7.01/1.48  --pred_elim                             true
% 7.01/1.48  --res_sim_input                         true
% 7.01/1.48  --eq_ax_congr_red                       true
% 7.01/1.48  --pure_diseq_elim                       true
% 7.01/1.48  --brand_transform                       false
% 7.01/1.48  --non_eq_to_eq                          false
% 7.01/1.48  --prep_def_merge                        true
% 7.01/1.48  --prep_def_merge_prop_impl              false
% 7.01/1.48  --prep_def_merge_mbd                    true
% 7.01/1.48  --prep_def_merge_tr_red                 false
% 7.01/1.48  --prep_def_merge_tr_cl                  false
% 7.01/1.48  --smt_preprocessing                     true
% 7.01/1.48  --smt_ac_axioms                         fast
% 7.01/1.48  --preprocessed_out                      false
% 7.01/1.48  --preprocessed_stats                    false
% 7.01/1.48  
% 7.01/1.48  ------ Abstraction refinement Options
% 7.01/1.48  
% 7.01/1.48  --abstr_ref                             []
% 7.01/1.48  --abstr_ref_prep                        false
% 7.01/1.48  --abstr_ref_until_sat                   false
% 7.01/1.48  --abstr_ref_sig_restrict                funpre
% 7.01/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.01/1.48  --abstr_ref_under                       []
% 7.01/1.48  
% 7.01/1.48  ------ SAT Options
% 7.01/1.48  
% 7.01/1.48  --sat_mode                              false
% 7.01/1.48  --sat_fm_restart_options                ""
% 7.01/1.48  --sat_gr_def                            false
% 7.01/1.48  --sat_epr_types                         true
% 7.01/1.48  --sat_non_cyclic_types                  false
% 7.01/1.48  --sat_finite_models                     false
% 7.01/1.48  --sat_fm_lemmas                         false
% 7.01/1.48  --sat_fm_prep                           false
% 7.01/1.48  --sat_fm_uc_incr                        true
% 7.01/1.48  --sat_out_model                         small
% 7.01/1.48  --sat_out_clauses                       false
% 7.01/1.48  
% 7.01/1.48  ------ QBF Options
% 7.01/1.48  
% 7.01/1.48  --qbf_mode                              false
% 7.01/1.48  --qbf_elim_univ                         false
% 7.01/1.48  --qbf_dom_inst                          none
% 7.01/1.48  --qbf_dom_pre_inst                      false
% 7.01/1.48  --qbf_sk_in                             false
% 7.01/1.48  --qbf_pred_elim                         true
% 7.01/1.48  --qbf_split                             512
% 7.01/1.48  
% 7.01/1.48  ------ BMC1 Options
% 7.01/1.48  
% 7.01/1.48  --bmc1_incremental                      false
% 7.01/1.48  --bmc1_axioms                           reachable_all
% 7.01/1.48  --bmc1_min_bound                        0
% 7.01/1.48  --bmc1_max_bound                        -1
% 7.01/1.48  --bmc1_max_bound_default                -1
% 7.01/1.48  --bmc1_symbol_reachability              true
% 7.01/1.48  --bmc1_property_lemmas                  false
% 7.01/1.48  --bmc1_k_induction                      false
% 7.01/1.48  --bmc1_non_equiv_states                 false
% 7.01/1.48  --bmc1_deadlock                         false
% 7.01/1.48  --bmc1_ucm                              false
% 7.01/1.48  --bmc1_add_unsat_core                   none
% 7.01/1.48  --bmc1_unsat_core_children              false
% 7.01/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.01/1.48  --bmc1_out_stat                         full
% 7.01/1.48  --bmc1_ground_init                      false
% 7.01/1.48  --bmc1_pre_inst_next_state              false
% 7.01/1.48  --bmc1_pre_inst_state                   false
% 7.01/1.48  --bmc1_pre_inst_reach_state             false
% 7.01/1.48  --bmc1_out_unsat_core                   false
% 7.01/1.48  --bmc1_aig_witness_out                  false
% 7.01/1.48  --bmc1_verbose                          false
% 7.01/1.48  --bmc1_dump_clauses_tptp                false
% 7.01/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.01/1.48  --bmc1_dump_file                        -
% 7.01/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.01/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.01/1.48  --bmc1_ucm_extend_mode                  1
% 7.01/1.48  --bmc1_ucm_init_mode                    2
% 7.01/1.48  --bmc1_ucm_cone_mode                    none
% 7.01/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.01/1.48  --bmc1_ucm_relax_model                  4
% 7.01/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.01/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.01/1.48  --bmc1_ucm_layered_model                none
% 7.01/1.48  --bmc1_ucm_max_lemma_size               10
% 7.01/1.48  
% 7.01/1.48  ------ AIG Options
% 7.01/1.48  
% 7.01/1.48  --aig_mode                              false
% 7.01/1.48  
% 7.01/1.48  ------ Instantiation Options
% 7.01/1.48  
% 7.01/1.48  --instantiation_flag                    true
% 7.01/1.48  --inst_sos_flag                         false
% 7.01/1.48  --inst_sos_phase                        true
% 7.01/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.01/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.01/1.48  --inst_lit_sel_side                     none
% 7.01/1.48  --inst_solver_per_active                1400
% 7.01/1.48  --inst_solver_calls_frac                1.
% 7.01/1.48  --inst_passive_queue_type               priority_queues
% 7.01/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.01/1.48  --inst_passive_queues_freq              [25;2]
% 7.01/1.48  --inst_dismatching                      true
% 7.01/1.48  --inst_eager_unprocessed_to_passive     true
% 7.01/1.48  --inst_prop_sim_given                   true
% 7.01/1.48  --inst_prop_sim_new                     false
% 7.01/1.48  --inst_subs_new                         false
% 7.01/1.48  --inst_eq_res_simp                      false
% 7.01/1.48  --inst_subs_given                       false
% 7.01/1.48  --inst_orphan_elimination               true
% 7.01/1.48  --inst_learning_loop_flag               true
% 7.01/1.48  --inst_learning_start                   3000
% 7.01/1.48  --inst_learning_factor                  2
% 7.01/1.48  --inst_start_prop_sim_after_learn       3
% 7.01/1.48  --inst_sel_renew                        solver
% 7.01/1.48  --inst_lit_activity_flag                true
% 7.01/1.48  --inst_restr_to_given                   false
% 7.01/1.48  --inst_activity_threshold               500
% 7.01/1.48  --inst_out_proof                        true
% 7.01/1.48  
% 7.01/1.48  ------ Resolution Options
% 7.01/1.48  
% 7.01/1.48  --resolution_flag                       false
% 7.01/1.48  --res_lit_sel                           adaptive
% 7.01/1.48  --res_lit_sel_side                      none
% 7.01/1.48  --res_ordering                          kbo
% 7.01/1.48  --res_to_prop_solver                    active
% 7.01/1.48  --res_prop_simpl_new                    false
% 7.01/1.48  --res_prop_simpl_given                  true
% 7.01/1.48  --res_passive_queue_type                priority_queues
% 7.01/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.01/1.48  --res_passive_queues_freq               [15;5]
% 7.01/1.48  --res_forward_subs                      full
% 7.01/1.48  --res_backward_subs                     full
% 7.01/1.48  --res_forward_subs_resolution           true
% 7.01/1.48  --res_backward_subs_resolution          true
% 7.01/1.48  --res_orphan_elimination                true
% 7.01/1.48  --res_time_limit                        2.
% 7.01/1.48  --res_out_proof                         true
% 7.01/1.48  
% 7.01/1.48  ------ Superposition Options
% 7.01/1.48  
% 7.01/1.48  --superposition_flag                    true
% 7.01/1.48  --sup_passive_queue_type                priority_queues
% 7.01/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.01/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.01/1.48  --demod_completeness_check              fast
% 7.01/1.48  --demod_use_ground                      true
% 7.01/1.48  --sup_to_prop_solver                    passive
% 7.01/1.48  --sup_prop_simpl_new                    true
% 7.01/1.48  --sup_prop_simpl_given                  true
% 7.01/1.48  --sup_fun_splitting                     false
% 7.01/1.48  --sup_smt_interval                      50000
% 7.01/1.48  
% 7.01/1.48  ------ Superposition Simplification Setup
% 7.01/1.48  
% 7.01/1.48  --sup_indices_passive                   []
% 7.01/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.01/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.01/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.01/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.01/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.01/1.48  --sup_full_bw                           [BwDemod]
% 7.01/1.48  --sup_immed_triv                        [TrivRules]
% 7.01/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.01/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.01/1.48  --sup_immed_bw_main                     []
% 7.01/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.01/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.01/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.01/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.01/1.48  
% 7.01/1.48  ------ Combination Options
% 7.01/1.48  
% 7.01/1.48  --comb_res_mult                         3
% 7.01/1.48  --comb_sup_mult                         2
% 7.01/1.48  --comb_inst_mult                        10
% 7.01/1.48  
% 7.01/1.48  ------ Debug Options
% 7.01/1.48  
% 7.01/1.48  --dbg_backtrace                         false
% 7.01/1.48  --dbg_dump_prop_clauses                 false
% 7.01/1.48  --dbg_dump_prop_clauses_file            -
% 7.01/1.48  --dbg_out_stat                          false
% 7.01/1.48  
% 7.01/1.48  
% 7.01/1.48  
% 7.01/1.48  
% 7.01/1.48  ------ Proving...
% 7.01/1.48  
% 7.01/1.48  
% 7.01/1.48  % SZS status Theorem for theBenchmark.p
% 7.01/1.48  
% 7.01/1.48   Resolution empty clause
% 7.01/1.48  
% 7.01/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.01/1.48  
% 7.01/1.48  fof(f20,conjecture,(
% 7.01/1.48    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 7.01/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.48  
% 7.01/1.48  fof(f21,negated_conjecture,(
% 7.01/1.48    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 7.01/1.48    inference(negated_conjecture,[],[f20])).
% 7.01/1.48  
% 7.01/1.48  fof(f30,plain,(
% 7.01/1.48    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 7.01/1.48    inference(ennf_transformation,[],[f21])).
% 7.01/1.48  
% 7.01/1.48  fof(f33,plain,(
% 7.01/1.48    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 7.01/1.48    introduced(choice_axiom,[])).
% 7.01/1.48  
% 7.01/1.48  fof(f34,plain,(
% 7.01/1.48    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 7.01/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f33])).
% 7.01/1.48  
% 7.01/1.48  fof(f56,plain,(
% 7.01/1.48    v1_relat_1(sK1)),
% 7.01/1.48    inference(cnf_transformation,[],[f34])).
% 7.01/1.48  
% 7.01/1.48  fof(f6,axiom,(
% 7.01/1.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.01/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.48  
% 7.01/1.48  fof(f42,plain,(
% 7.01/1.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.01/1.48    inference(cnf_transformation,[],[f6])).
% 7.01/1.48  
% 7.01/1.48  fof(f3,axiom,(
% 7.01/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.01/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.48  
% 7.01/1.48  fof(f39,plain,(
% 7.01/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.01/1.48    inference(cnf_transformation,[],[f3])).
% 7.01/1.48  
% 7.01/1.48  fof(f14,axiom,(
% 7.01/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 7.01/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.48  
% 7.01/1.48  fof(f50,plain,(
% 7.01/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 7.01/1.48    inference(cnf_transformation,[],[f14])).
% 7.01/1.48  
% 7.01/1.48  fof(f7,axiom,(
% 7.01/1.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 7.01/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.48  
% 7.01/1.48  fof(f43,plain,(
% 7.01/1.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 7.01/1.48    inference(cnf_transformation,[],[f7])).
% 7.01/1.48  
% 7.01/1.48  fof(f8,axiom,(
% 7.01/1.48    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.01/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.48  
% 7.01/1.48  fof(f44,plain,(
% 7.01/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.01/1.48    inference(cnf_transformation,[],[f8])).
% 7.01/1.48  
% 7.01/1.48  fof(f9,axiom,(
% 7.01/1.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 7.01/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.48  
% 7.01/1.48  fof(f45,plain,(
% 7.01/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 7.01/1.48    inference(cnf_transformation,[],[f9])).
% 7.01/1.48  
% 7.01/1.48  fof(f10,axiom,(
% 7.01/1.48    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 7.01/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.48  
% 7.01/1.48  fof(f46,plain,(
% 7.01/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 7.01/1.48    inference(cnf_transformation,[],[f10])).
% 7.01/1.48  
% 7.01/1.48  fof(f11,axiom,(
% 7.01/1.48    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 7.01/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.48  
% 7.01/1.48  fof(f47,plain,(
% 7.01/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 7.01/1.48    inference(cnf_transformation,[],[f11])).
% 7.01/1.48  
% 7.01/1.48  fof(f12,axiom,(
% 7.01/1.48    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 7.01/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.48  
% 7.01/1.48  fof(f48,plain,(
% 7.01/1.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 7.01/1.48    inference(cnf_transformation,[],[f12])).
% 7.01/1.48  
% 7.01/1.48  fof(f58,plain,(
% 7.01/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 7.01/1.48    inference(definition_unfolding,[],[f47,f48])).
% 7.01/1.48  
% 7.01/1.48  fof(f59,plain,(
% 7.01/1.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 7.01/1.48    inference(definition_unfolding,[],[f46,f58])).
% 7.01/1.48  
% 7.01/1.48  fof(f60,plain,(
% 7.01/1.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 7.01/1.48    inference(definition_unfolding,[],[f45,f59])).
% 7.01/1.48  
% 7.01/1.48  fof(f61,plain,(
% 7.01/1.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 7.01/1.48    inference(definition_unfolding,[],[f44,f60])).
% 7.01/1.48  
% 7.01/1.48  fof(f62,plain,(
% 7.01/1.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 7.01/1.48    inference(definition_unfolding,[],[f43,f61])).
% 7.01/1.48  
% 7.01/1.48  fof(f63,plain,(
% 7.01/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 7.01/1.48    inference(definition_unfolding,[],[f50,f62])).
% 7.01/1.48  
% 7.01/1.48  fof(f64,plain,(
% 7.01/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 7.01/1.48    inference(definition_unfolding,[],[f39,f63])).
% 7.01/1.48  
% 7.01/1.48  fof(f68,plain,(
% 7.01/1.48    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 7.01/1.48    inference(definition_unfolding,[],[f42,f64])).
% 7.01/1.48  
% 7.01/1.48  fof(f13,axiom,(
% 7.01/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.01/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.48  
% 7.01/1.48  fof(f49,plain,(
% 7.01/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.01/1.48    inference(cnf_transformation,[],[f13])).
% 7.01/1.48  
% 7.01/1.48  fof(f69,plain,(
% 7.01/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1)) )),
% 7.01/1.48    inference(definition_unfolding,[],[f49,f64])).
% 7.01/1.48  
% 7.01/1.48  fof(f18,axiom,(
% 7.01/1.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 7.01/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.48  
% 7.01/1.48  fof(f26,plain,(
% 7.01/1.48    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 7.01/1.48    inference(ennf_transformation,[],[f18])).
% 7.01/1.48  
% 7.01/1.48  fof(f27,plain,(
% 7.01/1.48    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.01/1.48    inference(flattening,[],[f26])).
% 7.01/1.48  
% 7.01/1.48  fof(f54,plain,(
% 7.01/1.48    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.01/1.48    inference(cnf_transformation,[],[f27])).
% 7.01/1.48  
% 7.01/1.48  fof(f2,axiom,(
% 7.01/1.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.01/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.48  
% 7.01/1.48  fof(f31,plain,(
% 7.01/1.48    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.01/1.48    inference(nnf_transformation,[],[f2])).
% 7.01/1.48  
% 7.01/1.48  fof(f32,plain,(
% 7.01/1.48    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.01/1.48    inference(flattening,[],[f31])).
% 7.01/1.48  
% 7.01/1.48  fof(f36,plain,(
% 7.01/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.01/1.48    inference(cnf_transformation,[],[f32])).
% 7.01/1.48  
% 7.01/1.48  fof(f72,plain,(
% 7.01/1.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.01/1.48    inference(equality_resolution,[],[f36])).
% 7.01/1.48  
% 7.01/1.48  fof(f19,axiom,(
% 7.01/1.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 7.01/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.48  
% 7.01/1.48  fof(f28,plain,(
% 7.01/1.48    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.01/1.48    inference(ennf_transformation,[],[f19])).
% 7.01/1.48  
% 7.01/1.48  fof(f29,plain,(
% 7.01/1.48    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.01/1.48    inference(flattening,[],[f28])).
% 7.01/1.48  
% 7.01/1.48  fof(f55,plain,(
% 7.01/1.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.01/1.48    inference(cnf_transformation,[],[f29])).
% 7.01/1.48  
% 7.01/1.48  fof(f16,axiom,(
% 7.01/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)))),
% 7.01/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.01/1.48  
% 7.01/1.48  fof(f24,plain,(
% 7.01/1.48    ! [X0,X1,X2] : (k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_relat_1(X2))),
% 7.01/1.48    inference(ennf_transformation,[],[f16])).
% 7.01/1.48  
% 7.01/1.48  fof(f52,plain,(
% 7.01/1.48    ( ! [X2,X0,X1] : (k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_relat_1(X2)) )),
% 7.01/1.48    inference(cnf_transformation,[],[f24])).
% 7.01/1.48  
% 7.01/1.48  fof(f57,plain,(
% 7.01/1.48    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))),
% 7.01/1.48    inference(cnf_transformation,[],[f34])).
% 7.01/1.48  
% 7.01/1.48  cnf(c_14,negated_conjecture,
% 7.01/1.48      ( v1_relat_1(sK1) ),
% 7.01/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_434,plain,
% 7.01/1.48      ( v1_relat_1(sK1) = iProver_top ),
% 7.01/1.48      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_6,plain,
% 7.01/1.48      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
% 7.01/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_440,plain,
% 7.01/1.48      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) = iProver_top ),
% 7.01/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_7,plain,
% 7.01/1.48      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1) ),
% 7.01/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_459,plain,
% 7.01/1.48      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 7.01/1.48      inference(light_normalisation,[status(thm)],[c_440,c_7]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_11,plain,
% 7.01/1.48      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.01/1.48      | ~ v1_relat_1(X1)
% 7.01/1.48      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 7.01/1.48      inference(cnf_transformation,[],[f54]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_436,plain,
% 7.01/1.48      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 7.01/1.48      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 7.01/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.01/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_1917,plain,
% 7.01/1.48      ( k1_relat_1(k7_relat_1(X0,k6_subset_1(k1_relat_1(X0),X1))) = k6_subset_1(k1_relat_1(X0),X1)
% 7.01/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.01/1.48      inference(superposition,[status(thm)],[c_459,c_436]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_19331,plain,
% 7.01/1.48      ( k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
% 7.01/1.48      inference(superposition,[status(thm)],[c_434,c_1917]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f72]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_443,plain,
% 7.01/1.48      ( r1_tarski(X0,X0) = iProver_top ),
% 7.01/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_12,plain,
% 7.01/1.48      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 7.01/1.48      | ~ v1_relat_1(X0)
% 7.01/1.48      | k7_relat_1(X0,X1) = X0 ),
% 7.01/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_435,plain,
% 7.01/1.48      ( k7_relat_1(X0,X1) = X0
% 7.01/1.48      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.01/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.01/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_855,plain,
% 7.01/1.48      ( k7_relat_1(X0,k1_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 7.01/1.48      inference(superposition,[status(thm)],[c_443,c_435]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_2216,plain,
% 7.01/1.48      ( k7_relat_1(sK1,k1_relat_1(sK1)) = sK1 ),
% 7.01/1.48      inference(superposition,[status(thm)],[c_434,c_855]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_9,plain,
% 7.01/1.48      ( ~ v1_relat_1(X0)
% 7.01/1.48      | k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2)) ),
% 7.01/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_438,plain,
% 7.01/1.48      ( k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2))
% 7.01/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.01/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_1068,plain,
% 7.01/1.48      ( k6_subset_1(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)) = k7_relat_1(sK1,k6_subset_1(X0,X1)) ),
% 7.01/1.48      inference(superposition,[status(thm)],[c_434,c_438]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_2235,plain,
% 7.01/1.48      ( k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) = k6_subset_1(sK1,k7_relat_1(sK1,X0)) ),
% 7.01/1.48      inference(superposition,[status(thm)],[c_2216,c_1068]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_19359,plain,
% 7.01/1.48      ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
% 7.01/1.48      inference(light_normalisation,[status(thm)],[c_19331,c_2235]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_13,negated_conjecture,
% 7.01/1.48      ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
% 7.01/1.48      inference(cnf_transformation,[],[f57]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_19826,plain,
% 7.01/1.48      ( k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0) ),
% 7.01/1.48      inference(demodulation,[status(thm)],[c_19359,c_13]) ).
% 7.01/1.48  
% 7.01/1.48  cnf(c_19830,plain,
% 7.01/1.48      ( $false ),
% 7.01/1.48      inference(equality_resolution_simp,[status(thm)],[c_19826]) ).
% 7.01/1.48  
% 7.01/1.48  
% 7.01/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.01/1.48  
% 7.01/1.48  ------                               Statistics
% 7.01/1.48  
% 7.01/1.48  ------ General
% 7.01/1.48  
% 7.01/1.48  abstr_ref_over_cycles:                  0
% 7.01/1.48  abstr_ref_under_cycles:                 0
% 7.01/1.48  gc_basic_clause_elim:                   0
% 7.01/1.48  forced_gc_time:                         0
% 7.01/1.48  parsing_time:                           0.008
% 7.01/1.48  unif_index_cands_time:                  0.
% 7.01/1.48  unif_index_add_time:                    0.
% 7.01/1.48  orderings_time:                         0.
% 7.01/1.48  out_proof_time:                         0.006
% 7.01/1.48  total_time:                             0.75
% 7.01/1.48  num_of_symbols:                         41
% 7.01/1.48  num_of_terms:                           28522
% 7.01/1.48  
% 7.01/1.48  ------ Preprocessing
% 7.01/1.48  
% 7.01/1.48  num_of_splits:                          0
% 7.01/1.48  num_of_split_atoms:                     0
% 7.01/1.48  num_of_reused_defs:                     0
% 7.01/1.48  num_eq_ax_congr_red:                    6
% 7.01/1.48  num_of_sem_filtered_clauses:            1
% 7.01/1.48  num_of_subtypes:                        0
% 7.01/1.48  monotx_restored_types:                  0
% 7.01/1.48  sat_num_of_epr_types:                   0
% 7.01/1.48  sat_num_of_non_cyclic_types:            0
% 7.01/1.48  sat_guarded_non_collapsed_types:        0
% 7.01/1.48  num_pure_diseq_elim:                    0
% 7.01/1.48  simp_replaced_by:                       0
% 7.01/1.48  res_preprocessed:                       77
% 7.01/1.48  prep_upred:                             0
% 7.01/1.48  prep_unflattend:                        0
% 7.01/1.48  smt_new_axioms:                         0
% 7.01/1.48  pred_elim_cands:                        2
% 7.01/1.48  pred_elim:                              0
% 7.01/1.48  pred_elim_cl:                           0
% 7.01/1.48  pred_elim_cycles:                       2
% 7.01/1.48  merged_defs:                            0
% 7.01/1.48  merged_defs_ncl:                        0
% 7.01/1.48  bin_hyper_res:                          0
% 7.01/1.48  prep_cycles:                            4
% 7.01/1.48  pred_elim_time:                         0.
% 7.01/1.48  splitting_time:                         0.
% 7.01/1.48  sem_filter_time:                        0.
% 7.01/1.48  monotx_time:                            0.001
% 7.01/1.48  subtype_inf_time:                       0.
% 7.01/1.48  
% 7.01/1.48  ------ Problem properties
% 7.01/1.48  
% 7.01/1.48  clauses:                                14
% 7.01/1.48  conjectures:                            2
% 7.01/1.48  epr:                                    3
% 7.01/1.48  horn:                                   14
% 7.01/1.48  ground:                                 2
% 7.01/1.48  unary:                                  7
% 7.01/1.48  binary:                                 4
% 7.01/1.48  lits:                                   24
% 7.01/1.48  lits_eq:                                9
% 7.01/1.48  fd_pure:                                0
% 7.01/1.48  fd_pseudo:                              0
% 7.01/1.48  fd_cond:                                0
% 7.01/1.48  fd_pseudo_cond:                         1
% 7.01/1.48  ac_symbols:                             0
% 7.01/1.48  
% 7.01/1.48  ------ Propositional Solver
% 7.01/1.48  
% 7.01/1.48  prop_solver_calls:                      29
% 7.01/1.48  prop_fast_solver_calls:                 482
% 7.01/1.48  smt_solver_calls:                       0
% 7.01/1.48  smt_fast_solver_calls:                  0
% 7.01/1.48  prop_num_of_clauses:                    8244
% 7.01/1.48  prop_preprocess_simplified:             10834
% 7.01/1.48  prop_fo_subsumed:                       7
% 7.01/1.48  prop_solver_time:                       0.
% 7.01/1.48  smt_solver_time:                        0.
% 7.01/1.48  smt_fast_solver_time:                   0.
% 7.01/1.48  prop_fast_solver_time:                  0.
% 7.01/1.48  prop_unsat_core_time:                   0.
% 7.01/1.48  
% 7.01/1.48  ------ QBF
% 7.01/1.48  
% 7.01/1.48  qbf_q_res:                              0
% 7.01/1.48  qbf_num_tautologies:                    0
% 7.01/1.48  qbf_prep_cycles:                        0
% 7.01/1.48  
% 7.01/1.48  ------ BMC1
% 7.01/1.48  
% 7.01/1.48  bmc1_current_bound:                     -1
% 7.01/1.48  bmc1_last_solved_bound:                 -1
% 7.01/1.48  bmc1_unsat_core_size:                   -1
% 7.01/1.48  bmc1_unsat_core_parents_size:           -1
% 7.01/1.48  bmc1_merge_next_fun:                    0
% 7.01/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.01/1.48  
% 7.01/1.48  ------ Instantiation
% 7.01/1.48  
% 7.01/1.48  inst_num_of_clauses:                    1589
% 7.01/1.48  inst_num_in_passive:                    344
% 7.01/1.48  inst_num_in_active:                     557
% 7.01/1.48  inst_num_in_unprocessed:                688
% 7.01/1.48  inst_num_of_loops:                      570
% 7.01/1.48  inst_num_of_learning_restarts:          0
% 7.01/1.48  inst_num_moves_active_passive:          10
% 7.01/1.48  inst_lit_activity:                      0
% 7.01/1.48  inst_lit_activity_moves:                0
% 7.01/1.48  inst_num_tautologies:                   0
% 7.01/1.48  inst_num_prop_implied:                  0
% 7.01/1.48  inst_num_existing_simplified:           0
% 7.01/1.48  inst_num_eq_res_simplified:             0
% 7.01/1.48  inst_num_child_elim:                    0
% 7.01/1.48  inst_num_of_dismatching_blockings:      1143
% 7.01/1.48  inst_num_of_non_proper_insts:           1856
% 7.01/1.48  inst_num_of_duplicates:                 0
% 7.01/1.48  inst_inst_num_from_inst_to_res:         0
% 7.01/1.48  inst_dismatching_checking_time:         0.
% 7.01/1.48  
% 7.01/1.48  ------ Resolution
% 7.01/1.48  
% 7.01/1.48  res_num_of_clauses:                     0
% 7.01/1.48  res_num_in_passive:                     0
% 7.01/1.48  res_num_in_active:                      0
% 7.01/1.48  res_num_of_loops:                       81
% 7.01/1.48  res_forward_subset_subsumed:            237
% 7.01/1.48  res_backward_subset_subsumed:           2
% 7.01/1.48  res_forward_subsumed:                   0
% 7.01/1.48  res_backward_subsumed:                  0
% 7.01/1.48  res_forward_subsumption_resolution:     0
% 7.01/1.48  res_backward_subsumption_resolution:    0
% 7.01/1.48  res_clause_to_clause_subsumption:       4108
% 7.01/1.48  res_orphan_elimination:                 0
% 7.01/1.48  res_tautology_del:                      157
% 7.01/1.48  res_num_eq_res_simplified:              0
% 7.01/1.48  res_num_sel_changes:                    0
% 7.01/1.48  res_moves_from_active_to_pass:          0
% 7.01/1.48  
% 7.01/1.48  ------ Superposition
% 7.01/1.48  
% 7.01/1.48  sup_time_total:                         0.
% 7.01/1.48  sup_time_generating:                    0.
% 7.01/1.48  sup_time_sim_full:                      0.
% 7.01/1.48  sup_time_sim_immed:                     0.
% 7.01/1.48  
% 7.01/1.48  sup_num_of_clauses:                     1291
% 7.01/1.48  sup_num_in_active:                      104
% 7.01/1.48  sup_num_in_passive:                     1187
% 7.01/1.48  sup_num_of_loops:                       112
% 7.01/1.48  sup_fw_superposition:                   819
% 7.01/1.48  sup_bw_superposition:                   1223
% 7.01/1.48  sup_immediate_simplified:               966
% 7.01/1.48  sup_given_eliminated:                   0
% 7.01/1.48  comparisons_done:                       0
% 7.01/1.48  comparisons_avoided:                    0
% 7.01/1.48  
% 7.01/1.48  ------ Simplifications
% 7.01/1.48  
% 7.01/1.48  
% 7.01/1.48  sim_fw_subset_subsumed:                 0
% 7.01/1.48  sim_bw_subset_subsumed:                 21
% 7.01/1.48  sim_fw_subsumed:                        346
% 7.01/1.48  sim_bw_subsumed:                        9
% 7.01/1.48  sim_fw_subsumption_res:                 0
% 7.01/1.48  sim_bw_subsumption_res:                 0
% 7.01/1.48  sim_tautology_del:                      3
% 7.01/1.48  sim_eq_tautology_del:                   45
% 7.01/1.48  sim_eq_res_simp:                        0
% 7.01/1.48  sim_fw_demodulated:                     113
% 7.01/1.48  sim_bw_demodulated:                     14
% 7.01/1.48  sim_light_normalised:                   654
% 7.01/1.48  sim_joinable_taut:                      0
% 7.01/1.48  sim_joinable_simp:                      0
% 7.01/1.48  sim_ac_normalised:                      0
% 7.01/1.48  sim_smt_subsumption:                    0
% 7.01/1.48  
%------------------------------------------------------------------------------
