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
% DateTime   : Thu Dec  3 11:48:41 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 111 expanded)
%              Number of clauses        :   21 (  25 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   17
%              Number of atoms          :   97 ( 162 expanded)
%              Number of equality atoms :   66 ( 109 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0)))
        & v1_relat_1(X1) )
   => ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f29])).

fof(f50,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f39,f53])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f54])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f55])).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f56])).

fof(f58,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f35,f57])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f36,f58])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_372,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_378,plain,
    ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_397,plain,
    ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_378,c_5])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_374,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_695,plain,
    ( k1_relat_1(k7_relat_1(X0,k6_subset_1(k1_relat_1(X0),X1))) = k6_subset_1(k1_relat_1(X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_397,c_374])).

cnf(c_4104,plain,
    ( k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
    inference(superposition,[status(thm)],[c_372,c_695])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_373,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_519,plain,
    ( k7_relat_1(sK1,k1_relat_1(sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_372,c_373])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_376,plain,
    ( k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_932,plain,
    ( k6_subset_1(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)) = k7_relat_1(sK1,k6_subset_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_372,c_376])).

cnf(c_944,plain,
    ( k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) = k6_subset_1(sK1,k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_519,c_932])).

cnf(c_4118,plain,
    ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
    inference(light_normalisation,[status(thm)],[c_4104,c_944])).

cnf(c_11,negated_conjecture,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4752,plain,
    ( k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0) ),
    inference(demodulation,[status(thm)],[c_4118,c_11])).

cnf(c_4756,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_4752])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : iproveropt_run.sh %d %s
% 0.09/0.29  % Computer   : n001.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % WCLimit    : 600
% 0.09/0.29  % DateTime   : Tue Dec  1 16:30:45 EST 2020
% 0.09/0.30  % CPUTime    : 
% 0.09/0.30  % Running in FOF mode
% 2.98/0.94  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.98/0.94  
% 2.98/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.98/0.94  
% 2.98/0.94  ------  iProver source info
% 2.98/0.94  
% 2.98/0.94  git: date: 2020-06-30 10:37:57 +0100
% 2.98/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.98/0.94  git: non_committed_changes: false
% 2.98/0.94  git: last_make_outside_of_git: false
% 2.98/0.94  
% 2.98/0.94  ------ 
% 2.98/0.94  
% 2.98/0.94  ------ Input Options
% 2.98/0.94  
% 2.98/0.94  --out_options                           all
% 2.98/0.94  --tptp_safe_out                         true
% 2.98/0.94  --problem_path                          ""
% 2.98/0.94  --include_path                          ""
% 2.98/0.94  --clausifier                            res/vclausify_rel
% 2.98/0.94  --clausifier_options                    --mode clausify
% 2.98/0.94  --stdin                                 false
% 2.98/0.94  --stats_out                             all
% 2.98/0.94  
% 2.98/0.94  ------ General Options
% 2.98/0.94  
% 2.98/0.94  --fof                                   false
% 2.98/0.94  --time_out_real                         305.
% 2.98/0.94  --time_out_virtual                      -1.
% 2.98/0.94  --symbol_type_check                     false
% 2.98/0.94  --clausify_out                          false
% 2.98/0.94  --sig_cnt_out                           false
% 2.98/0.94  --trig_cnt_out                          false
% 2.98/0.94  --trig_cnt_out_tolerance                1.
% 2.98/0.94  --trig_cnt_out_sk_spl                   false
% 2.98/0.94  --abstr_cl_out                          false
% 2.98/0.94  
% 2.98/0.94  ------ Global Options
% 2.98/0.94  
% 2.98/0.94  --schedule                              default
% 2.98/0.94  --add_important_lit                     false
% 2.98/0.94  --prop_solver_per_cl                    1000
% 2.98/0.94  --min_unsat_core                        false
% 2.98/0.94  --soft_assumptions                      false
% 2.98/0.94  --soft_lemma_size                       3
% 2.98/0.94  --prop_impl_unit_size                   0
% 2.98/0.94  --prop_impl_unit                        []
% 2.98/0.94  --share_sel_clauses                     true
% 2.98/0.94  --reset_solvers                         false
% 2.98/0.94  --bc_imp_inh                            [conj_cone]
% 2.98/0.94  --conj_cone_tolerance                   3.
% 2.98/0.94  --extra_neg_conj                        none
% 2.98/0.94  --large_theory_mode                     true
% 2.98/0.94  --prolific_symb_bound                   200
% 2.98/0.94  --lt_threshold                          2000
% 2.98/0.94  --clause_weak_htbl                      true
% 2.98/0.94  --gc_record_bc_elim                     false
% 2.98/0.94  
% 2.98/0.94  ------ Preprocessing Options
% 2.98/0.94  
% 2.98/0.94  --preprocessing_flag                    true
% 2.98/0.94  --time_out_prep_mult                    0.1
% 2.98/0.94  --splitting_mode                        input
% 2.98/0.94  --splitting_grd                         true
% 2.98/0.94  --splitting_cvd                         false
% 2.98/0.94  --splitting_cvd_svl                     false
% 2.98/0.94  --splitting_nvd                         32
% 2.98/0.94  --sub_typing                            true
% 2.98/0.94  --prep_gs_sim                           true
% 2.98/0.94  --prep_unflatten                        true
% 2.98/0.94  --prep_res_sim                          true
% 2.98/0.94  --prep_upred                            true
% 2.98/0.94  --prep_sem_filter                       exhaustive
% 2.98/0.94  --prep_sem_filter_out                   false
% 2.98/0.94  --pred_elim                             true
% 2.98/0.94  --res_sim_input                         true
% 2.98/0.94  --eq_ax_congr_red                       true
% 2.98/0.94  --pure_diseq_elim                       true
% 2.98/0.94  --brand_transform                       false
% 2.98/0.94  --non_eq_to_eq                          false
% 2.98/0.94  --prep_def_merge                        true
% 2.98/0.94  --prep_def_merge_prop_impl              false
% 2.98/0.94  --prep_def_merge_mbd                    true
% 2.98/0.94  --prep_def_merge_tr_red                 false
% 2.98/0.94  --prep_def_merge_tr_cl                  false
% 2.98/0.94  --smt_preprocessing                     true
% 2.98/0.94  --smt_ac_axioms                         fast
% 2.98/0.94  --preprocessed_out                      false
% 2.98/0.94  --preprocessed_stats                    false
% 2.98/0.94  
% 2.98/0.94  ------ Abstraction refinement Options
% 2.98/0.94  
% 2.98/0.94  --abstr_ref                             []
% 2.98/0.94  --abstr_ref_prep                        false
% 2.98/0.94  --abstr_ref_until_sat                   false
% 2.98/0.94  --abstr_ref_sig_restrict                funpre
% 2.98/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/0.94  --abstr_ref_under                       []
% 2.98/0.94  
% 2.98/0.94  ------ SAT Options
% 2.98/0.94  
% 2.98/0.94  --sat_mode                              false
% 2.98/0.94  --sat_fm_restart_options                ""
% 2.98/0.94  --sat_gr_def                            false
% 2.98/0.94  --sat_epr_types                         true
% 2.98/0.94  --sat_non_cyclic_types                  false
% 2.98/0.94  --sat_finite_models                     false
% 2.98/0.94  --sat_fm_lemmas                         false
% 2.98/0.94  --sat_fm_prep                           false
% 2.98/0.94  --sat_fm_uc_incr                        true
% 2.98/0.94  --sat_out_model                         small
% 2.98/0.94  --sat_out_clauses                       false
% 2.98/0.94  
% 2.98/0.94  ------ QBF Options
% 2.98/0.94  
% 2.98/0.94  --qbf_mode                              false
% 2.98/0.94  --qbf_elim_univ                         false
% 2.98/0.94  --qbf_dom_inst                          none
% 2.98/0.94  --qbf_dom_pre_inst                      false
% 2.98/0.94  --qbf_sk_in                             false
% 2.98/0.94  --qbf_pred_elim                         true
% 2.98/0.94  --qbf_split                             512
% 2.98/0.94  
% 2.98/0.94  ------ BMC1 Options
% 2.98/0.94  
% 2.98/0.94  --bmc1_incremental                      false
% 2.98/0.94  --bmc1_axioms                           reachable_all
% 2.98/0.94  --bmc1_min_bound                        0
% 2.98/0.94  --bmc1_max_bound                        -1
% 2.98/0.94  --bmc1_max_bound_default                -1
% 2.98/0.94  --bmc1_symbol_reachability              true
% 2.98/0.94  --bmc1_property_lemmas                  false
% 2.98/0.94  --bmc1_k_induction                      false
% 2.98/0.94  --bmc1_non_equiv_states                 false
% 2.98/0.94  --bmc1_deadlock                         false
% 2.98/0.94  --bmc1_ucm                              false
% 2.98/0.94  --bmc1_add_unsat_core                   none
% 2.98/0.94  --bmc1_unsat_core_children              false
% 2.98/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/0.94  --bmc1_out_stat                         full
% 2.98/0.94  --bmc1_ground_init                      false
% 2.98/0.94  --bmc1_pre_inst_next_state              false
% 2.98/0.94  --bmc1_pre_inst_state                   false
% 2.98/0.94  --bmc1_pre_inst_reach_state             false
% 2.98/0.94  --bmc1_out_unsat_core                   false
% 2.98/0.94  --bmc1_aig_witness_out                  false
% 2.98/0.94  --bmc1_verbose                          false
% 2.98/0.94  --bmc1_dump_clauses_tptp                false
% 2.98/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.98/0.94  --bmc1_dump_file                        -
% 2.98/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.98/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.98/0.94  --bmc1_ucm_extend_mode                  1
% 2.98/0.94  --bmc1_ucm_init_mode                    2
% 2.98/0.94  --bmc1_ucm_cone_mode                    none
% 2.98/0.94  --bmc1_ucm_reduced_relation_type        0
% 2.98/0.94  --bmc1_ucm_relax_model                  4
% 2.98/0.94  --bmc1_ucm_full_tr_after_sat            true
% 2.98/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/0.94  --bmc1_ucm_layered_model                none
% 2.98/0.94  --bmc1_ucm_max_lemma_size               10
% 2.98/0.94  
% 2.98/0.94  ------ AIG Options
% 2.98/0.94  
% 2.98/0.94  --aig_mode                              false
% 2.98/0.94  
% 2.98/0.94  ------ Instantiation Options
% 2.98/0.94  
% 2.98/0.94  --instantiation_flag                    true
% 2.98/0.94  --inst_sos_flag                         false
% 2.98/0.94  --inst_sos_phase                        true
% 2.98/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/0.94  --inst_lit_sel_side                     num_symb
% 2.98/0.94  --inst_solver_per_active                1400
% 2.98/0.94  --inst_solver_calls_frac                1.
% 2.98/0.94  --inst_passive_queue_type               priority_queues
% 2.98/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/0.94  --inst_passive_queues_freq              [25;2]
% 2.98/0.94  --inst_dismatching                      true
% 2.98/0.94  --inst_eager_unprocessed_to_passive     true
% 2.98/0.94  --inst_prop_sim_given                   true
% 2.98/0.94  --inst_prop_sim_new                     false
% 2.98/0.94  --inst_subs_new                         false
% 2.98/0.94  --inst_eq_res_simp                      false
% 2.98/0.94  --inst_subs_given                       false
% 2.98/0.94  --inst_orphan_elimination               true
% 2.98/0.94  --inst_learning_loop_flag               true
% 2.98/0.94  --inst_learning_start                   3000
% 2.98/0.94  --inst_learning_factor                  2
% 2.98/0.94  --inst_start_prop_sim_after_learn       3
% 2.98/0.94  --inst_sel_renew                        solver
% 2.98/0.94  --inst_lit_activity_flag                true
% 2.98/0.94  --inst_restr_to_given                   false
% 2.98/0.94  --inst_activity_threshold               500
% 2.98/0.94  --inst_out_proof                        true
% 2.98/0.94  
% 2.98/0.94  ------ Resolution Options
% 2.98/0.94  
% 2.98/0.94  --resolution_flag                       true
% 2.98/0.94  --res_lit_sel                           adaptive
% 2.98/0.94  --res_lit_sel_side                      none
% 2.98/0.94  --res_ordering                          kbo
% 2.98/0.94  --res_to_prop_solver                    active
% 2.98/0.94  --res_prop_simpl_new                    false
% 2.98/0.94  --res_prop_simpl_given                  true
% 2.98/0.94  --res_passive_queue_type                priority_queues
% 2.98/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/0.94  --res_passive_queues_freq               [15;5]
% 2.98/0.94  --res_forward_subs                      full
% 2.98/0.94  --res_backward_subs                     full
% 2.98/0.94  --res_forward_subs_resolution           true
% 2.98/0.94  --res_backward_subs_resolution          true
% 2.98/0.94  --res_orphan_elimination                true
% 2.98/0.94  --res_time_limit                        2.
% 2.98/0.94  --res_out_proof                         true
% 2.98/0.94  
% 2.98/0.94  ------ Superposition Options
% 2.98/0.94  
% 2.98/0.94  --superposition_flag                    true
% 2.98/0.94  --sup_passive_queue_type                priority_queues
% 2.98/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.98/0.94  --demod_completeness_check              fast
% 2.98/0.94  --demod_use_ground                      true
% 2.98/0.94  --sup_to_prop_solver                    passive
% 2.98/0.94  --sup_prop_simpl_new                    true
% 2.98/0.94  --sup_prop_simpl_given                  true
% 2.98/0.94  --sup_fun_splitting                     false
% 2.98/0.94  --sup_smt_interval                      50000
% 2.98/0.94  
% 2.98/0.94  ------ Superposition Simplification Setup
% 2.98/0.94  
% 2.98/0.94  --sup_indices_passive                   []
% 2.98/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.94  --sup_full_bw                           [BwDemod]
% 2.98/0.94  --sup_immed_triv                        [TrivRules]
% 2.98/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.94  --sup_immed_bw_main                     []
% 2.98/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.94  
% 2.98/0.94  ------ Combination Options
% 2.98/0.94  
% 2.98/0.94  --comb_res_mult                         3
% 2.98/0.94  --comb_sup_mult                         2
% 2.98/0.94  --comb_inst_mult                        10
% 2.98/0.94  
% 2.98/0.94  ------ Debug Options
% 2.98/0.94  
% 2.98/0.94  --dbg_backtrace                         false
% 2.98/0.94  --dbg_dump_prop_clauses                 false
% 2.98/0.94  --dbg_dump_prop_clauses_file            -
% 2.98/0.94  --dbg_out_stat                          false
% 2.98/0.94  ------ Parsing...
% 2.98/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.98/0.94  
% 2.98/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.98/0.94  
% 2.98/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.98/0.94  
% 2.98/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.98/0.94  ------ Proving...
% 2.98/0.94  ------ Problem Properties 
% 2.98/0.94  
% 2.98/0.94  
% 2.98/0.94  clauses                                 12
% 2.98/0.94  conjectures                             2
% 2.98/0.94  EPR                                     3
% 2.98/0.94  Horn                                    12
% 2.98/0.94  unary                                   6
% 2.98/0.94  binary                                  4
% 2.98/0.94  lits                                    20
% 2.98/0.94  lits eq                                 8
% 2.98/0.94  fd_pure                                 0
% 2.98/0.94  fd_pseudo                               0
% 2.98/0.94  fd_cond                                 0
% 2.98/0.94  fd_pseudo_cond                          1
% 2.98/0.94  AC symbols                              0
% 2.98/0.94  
% 2.98/0.94  ------ Schedule dynamic 5 is on 
% 2.98/0.94  
% 2.98/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.98/0.94  
% 2.98/0.94  
% 2.98/0.94  ------ 
% 2.98/0.94  Current options:
% 2.98/0.94  ------ 
% 2.98/0.94  
% 2.98/0.94  ------ Input Options
% 2.98/0.94  
% 2.98/0.94  --out_options                           all
% 2.98/0.94  --tptp_safe_out                         true
% 2.98/0.94  --problem_path                          ""
% 2.98/0.94  --include_path                          ""
% 2.98/0.94  --clausifier                            res/vclausify_rel
% 2.98/0.94  --clausifier_options                    --mode clausify
% 2.98/0.94  --stdin                                 false
% 2.98/0.94  --stats_out                             all
% 2.98/0.94  
% 2.98/0.94  ------ General Options
% 2.98/0.94  
% 2.98/0.94  --fof                                   false
% 2.98/0.94  --time_out_real                         305.
% 2.98/0.94  --time_out_virtual                      -1.
% 2.98/0.94  --symbol_type_check                     false
% 2.98/0.94  --clausify_out                          false
% 2.98/0.94  --sig_cnt_out                           false
% 2.98/0.94  --trig_cnt_out                          false
% 2.98/0.94  --trig_cnt_out_tolerance                1.
% 2.98/0.94  --trig_cnt_out_sk_spl                   false
% 2.98/0.94  --abstr_cl_out                          false
% 2.98/0.94  
% 2.98/0.94  ------ Global Options
% 2.98/0.94  
% 2.98/0.94  --schedule                              default
% 2.98/0.94  --add_important_lit                     false
% 2.98/0.94  --prop_solver_per_cl                    1000
% 2.98/0.94  --min_unsat_core                        false
% 2.98/0.94  --soft_assumptions                      false
% 2.98/0.94  --soft_lemma_size                       3
% 2.98/0.94  --prop_impl_unit_size                   0
% 2.98/0.94  --prop_impl_unit                        []
% 2.98/0.94  --share_sel_clauses                     true
% 2.98/0.94  --reset_solvers                         false
% 2.98/0.94  --bc_imp_inh                            [conj_cone]
% 2.98/0.94  --conj_cone_tolerance                   3.
% 2.98/0.94  --extra_neg_conj                        none
% 2.98/0.94  --large_theory_mode                     true
% 2.98/0.94  --prolific_symb_bound                   200
% 2.98/0.94  --lt_threshold                          2000
% 2.98/0.94  --clause_weak_htbl                      true
% 2.98/0.94  --gc_record_bc_elim                     false
% 2.98/0.94  
% 2.98/0.94  ------ Preprocessing Options
% 2.98/0.94  
% 2.98/0.94  --preprocessing_flag                    true
% 2.98/0.94  --time_out_prep_mult                    0.1
% 2.98/0.94  --splitting_mode                        input
% 2.98/0.94  --splitting_grd                         true
% 2.98/0.94  --splitting_cvd                         false
% 2.98/0.94  --splitting_cvd_svl                     false
% 2.98/0.94  --splitting_nvd                         32
% 2.98/0.94  --sub_typing                            true
% 2.98/0.94  --prep_gs_sim                           true
% 2.98/0.94  --prep_unflatten                        true
% 2.98/0.94  --prep_res_sim                          true
% 2.98/0.94  --prep_upred                            true
% 2.98/0.94  --prep_sem_filter                       exhaustive
% 2.98/0.94  --prep_sem_filter_out                   false
% 2.98/0.94  --pred_elim                             true
% 2.98/0.94  --res_sim_input                         true
% 2.98/0.94  --eq_ax_congr_red                       true
% 2.98/0.94  --pure_diseq_elim                       true
% 2.98/0.94  --brand_transform                       false
% 2.98/0.94  --non_eq_to_eq                          false
% 2.98/0.94  --prep_def_merge                        true
% 2.98/0.94  --prep_def_merge_prop_impl              false
% 2.98/0.94  --prep_def_merge_mbd                    true
% 2.98/0.94  --prep_def_merge_tr_red                 false
% 2.98/0.94  --prep_def_merge_tr_cl                  false
% 2.98/0.94  --smt_preprocessing                     true
% 2.98/0.94  --smt_ac_axioms                         fast
% 2.98/0.94  --preprocessed_out                      false
% 2.98/0.94  --preprocessed_stats                    false
% 2.98/0.94  
% 2.98/0.94  ------ Abstraction refinement Options
% 2.98/0.94  
% 2.98/0.94  --abstr_ref                             []
% 2.98/0.94  --abstr_ref_prep                        false
% 2.98/0.94  --abstr_ref_until_sat                   false
% 2.98/0.94  --abstr_ref_sig_restrict                funpre
% 2.98/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.98/0.94  --abstr_ref_under                       []
% 2.98/0.94  
% 2.98/0.94  ------ SAT Options
% 2.98/0.94  
% 2.98/0.94  --sat_mode                              false
% 2.98/0.94  --sat_fm_restart_options                ""
% 2.98/0.94  --sat_gr_def                            false
% 2.98/0.94  --sat_epr_types                         true
% 2.98/0.94  --sat_non_cyclic_types                  false
% 2.98/0.94  --sat_finite_models                     false
% 2.98/0.94  --sat_fm_lemmas                         false
% 2.98/0.94  --sat_fm_prep                           false
% 2.98/0.94  --sat_fm_uc_incr                        true
% 2.98/0.94  --sat_out_model                         small
% 2.98/0.94  --sat_out_clauses                       false
% 2.98/0.94  
% 2.98/0.94  ------ QBF Options
% 2.98/0.94  
% 2.98/0.94  --qbf_mode                              false
% 2.98/0.94  --qbf_elim_univ                         false
% 2.98/0.94  --qbf_dom_inst                          none
% 2.98/0.94  --qbf_dom_pre_inst                      false
% 2.98/0.94  --qbf_sk_in                             false
% 2.98/0.94  --qbf_pred_elim                         true
% 2.98/0.94  --qbf_split                             512
% 2.98/0.94  
% 2.98/0.94  ------ BMC1 Options
% 2.98/0.94  
% 2.98/0.94  --bmc1_incremental                      false
% 2.98/0.94  --bmc1_axioms                           reachable_all
% 2.98/0.94  --bmc1_min_bound                        0
% 2.98/0.94  --bmc1_max_bound                        -1
% 2.98/0.94  --bmc1_max_bound_default                -1
% 2.98/0.94  --bmc1_symbol_reachability              true
% 2.98/0.94  --bmc1_property_lemmas                  false
% 2.98/0.94  --bmc1_k_induction                      false
% 2.98/0.94  --bmc1_non_equiv_states                 false
% 2.98/0.94  --bmc1_deadlock                         false
% 2.98/0.94  --bmc1_ucm                              false
% 2.98/0.94  --bmc1_add_unsat_core                   none
% 2.98/0.94  --bmc1_unsat_core_children              false
% 2.98/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.98/0.94  --bmc1_out_stat                         full
% 2.98/0.94  --bmc1_ground_init                      false
% 2.98/0.94  --bmc1_pre_inst_next_state              false
% 2.98/0.94  --bmc1_pre_inst_state                   false
% 2.98/0.94  --bmc1_pre_inst_reach_state             false
% 2.98/0.94  --bmc1_out_unsat_core                   false
% 2.98/0.94  --bmc1_aig_witness_out                  false
% 2.98/0.94  --bmc1_verbose                          false
% 2.98/0.94  --bmc1_dump_clauses_tptp                false
% 2.98/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.98/0.94  --bmc1_dump_file                        -
% 2.98/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.98/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.98/0.94  --bmc1_ucm_extend_mode                  1
% 2.98/0.94  --bmc1_ucm_init_mode                    2
% 2.98/0.94  --bmc1_ucm_cone_mode                    none
% 2.98/0.94  --bmc1_ucm_reduced_relation_type        0
% 2.98/0.94  --bmc1_ucm_relax_model                  4
% 2.98/0.94  --bmc1_ucm_full_tr_after_sat            true
% 2.98/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 2.98/0.94  --bmc1_ucm_layered_model                none
% 2.98/0.94  --bmc1_ucm_max_lemma_size               10
% 2.98/0.94  
% 2.98/0.94  ------ AIG Options
% 2.98/0.94  
% 2.98/0.94  --aig_mode                              false
% 2.98/0.94  
% 2.98/0.94  ------ Instantiation Options
% 2.98/0.94  
% 2.98/0.94  --instantiation_flag                    true
% 2.98/0.94  --inst_sos_flag                         false
% 2.98/0.94  --inst_sos_phase                        true
% 2.98/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.98/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.98/0.94  --inst_lit_sel_side                     none
% 2.98/0.94  --inst_solver_per_active                1400
% 2.98/0.94  --inst_solver_calls_frac                1.
% 2.98/0.94  --inst_passive_queue_type               priority_queues
% 2.98/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.98/0.94  --inst_passive_queues_freq              [25;2]
% 2.98/0.94  --inst_dismatching                      true
% 2.98/0.94  --inst_eager_unprocessed_to_passive     true
% 2.98/0.94  --inst_prop_sim_given                   true
% 2.98/0.94  --inst_prop_sim_new                     false
% 2.98/0.94  --inst_subs_new                         false
% 2.98/0.94  --inst_eq_res_simp                      false
% 2.98/0.94  --inst_subs_given                       false
% 2.98/0.94  --inst_orphan_elimination               true
% 2.98/0.94  --inst_learning_loop_flag               true
% 2.98/0.94  --inst_learning_start                   3000
% 2.98/0.94  --inst_learning_factor                  2
% 2.98/0.94  --inst_start_prop_sim_after_learn       3
% 2.98/0.94  --inst_sel_renew                        solver
% 2.98/0.94  --inst_lit_activity_flag                true
% 2.98/0.94  --inst_restr_to_given                   false
% 2.98/0.94  --inst_activity_threshold               500
% 2.98/0.94  --inst_out_proof                        true
% 2.98/0.94  
% 2.98/0.94  ------ Resolution Options
% 2.98/0.94  
% 2.98/0.94  --resolution_flag                       false
% 2.98/0.94  --res_lit_sel                           adaptive
% 2.98/0.94  --res_lit_sel_side                      none
% 2.98/0.94  --res_ordering                          kbo
% 2.98/0.94  --res_to_prop_solver                    active
% 2.98/0.94  --res_prop_simpl_new                    false
% 2.98/0.94  --res_prop_simpl_given                  true
% 2.98/0.94  --res_passive_queue_type                priority_queues
% 2.98/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.98/0.94  --res_passive_queues_freq               [15;5]
% 2.98/0.94  --res_forward_subs                      full
% 2.98/0.94  --res_backward_subs                     full
% 2.98/0.94  --res_forward_subs_resolution           true
% 2.98/0.94  --res_backward_subs_resolution          true
% 2.98/0.94  --res_orphan_elimination                true
% 2.98/0.94  --res_time_limit                        2.
% 2.98/0.94  --res_out_proof                         true
% 2.98/0.94  
% 2.98/0.94  ------ Superposition Options
% 2.98/0.94  
% 2.98/0.94  --superposition_flag                    true
% 2.98/0.94  --sup_passive_queue_type                priority_queues
% 2.98/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.98/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.98/0.94  --demod_completeness_check              fast
% 2.98/0.94  --demod_use_ground                      true
% 2.98/0.94  --sup_to_prop_solver                    passive
% 2.98/0.94  --sup_prop_simpl_new                    true
% 2.98/0.94  --sup_prop_simpl_given                  true
% 2.98/0.94  --sup_fun_splitting                     false
% 2.98/0.94  --sup_smt_interval                      50000
% 2.98/0.94  
% 2.98/0.94  ------ Superposition Simplification Setup
% 2.98/0.94  
% 2.98/0.94  --sup_indices_passive                   []
% 2.98/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.98/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.98/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.94  --sup_full_bw                           [BwDemod]
% 2.98/0.94  --sup_immed_triv                        [TrivRules]
% 2.98/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.98/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.94  --sup_immed_bw_main                     []
% 2.98/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.98/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.98/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.98/0.94  
% 2.98/0.94  ------ Combination Options
% 2.98/0.94  
% 2.98/0.94  --comb_res_mult                         3
% 2.98/0.94  --comb_sup_mult                         2
% 2.98/0.94  --comb_inst_mult                        10
% 2.98/0.94  
% 2.98/0.94  ------ Debug Options
% 2.98/0.94  
% 2.98/0.94  --dbg_backtrace                         false
% 2.98/0.94  --dbg_dump_prop_clauses                 false
% 2.98/0.94  --dbg_dump_prop_clauses_file            -
% 2.98/0.94  --dbg_out_stat                          false
% 2.98/0.94  
% 2.98/0.94  
% 2.98/0.94  
% 2.98/0.94  
% 2.98/0.94  ------ Proving...
% 2.98/0.94  
% 2.98/0.94  
% 2.98/0.94  % SZS status Theorem for theBenchmark.p
% 2.98/0.94  
% 2.98/0.94   Resolution empty clause
% 2.98/0.94  
% 2.98/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 2.98/0.94  
% 2.98/0.94  fof(f18,conjecture,(
% 2.98/0.94    ! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 2.98/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.94  
% 2.98/0.94  fof(f19,negated_conjecture,(
% 2.98/0.94    ~! [X0,X1] : (v1_relat_1(X1) => k6_subset_1(k1_relat_1(X1),X0) = k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))))),
% 2.98/0.94    inference(negated_conjecture,[],[f18])).
% 2.98/0.94  
% 2.98/0.94  fof(f26,plain,(
% 2.98/0.94    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 2.98/0.94    inference(ennf_transformation,[],[f19])).
% 2.98/0.94  
% 2.98/0.94  fof(f29,plain,(
% 2.98/0.94    ? [X0,X1] : (k6_subset_1(k1_relat_1(X1),X0) != k1_relat_1(k6_subset_1(X1,k7_relat_1(X1,X0))) & v1_relat_1(X1)) => (k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1))),
% 2.98/0.94    introduced(choice_axiom,[])).
% 2.98/0.94  
% 2.98/0.94  fof(f30,plain,(
% 2.98/0.94    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) & v1_relat_1(sK1)),
% 2.98/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f29])).
% 2.98/0.94  
% 2.98/0.94  fof(f50,plain,(
% 2.98/0.94    v1_relat_1(sK1)),
% 2.98/0.94    inference(cnf_transformation,[],[f30])).
% 2.98/0.94  
% 2.98/0.94  fof(f4,axiom,(
% 2.98/0.94    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.98/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.94  
% 2.98/0.94  fof(f36,plain,(
% 2.98/0.94    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.98/0.94    inference(cnf_transformation,[],[f4])).
% 2.98/0.94  
% 2.98/0.94  fof(f3,axiom,(
% 2.98/0.94    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.98/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.94  
% 2.98/0.94  fof(f35,plain,(
% 2.98/0.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.98/0.94    inference(cnf_transformation,[],[f3])).
% 2.98/0.94  
% 2.98/0.94  fof(f12,axiom,(
% 2.98/0.94    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.98/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.94  
% 2.98/0.94  fof(f44,plain,(
% 2.98/0.94    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.98/0.94    inference(cnf_transformation,[],[f12])).
% 2.98/0.94  
% 2.98/0.94  fof(f5,axiom,(
% 2.98/0.94    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.98/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.94  
% 2.98/0.94  fof(f37,plain,(
% 2.98/0.94    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.98/0.94    inference(cnf_transformation,[],[f5])).
% 2.98/0.94  
% 2.98/0.94  fof(f6,axiom,(
% 2.98/0.94    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.98/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.94  
% 2.98/0.94  fof(f38,plain,(
% 2.98/0.94    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.98/0.94    inference(cnf_transformation,[],[f6])).
% 2.98/0.94  
% 2.98/0.94  fof(f7,axiom,(
% 2.98/0.94    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.98/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.94  
% 2.98/0.94  fof(f39,plain,(
% 2.98/0.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.98/0.94    inference(cnf_transformation,[],[f7])).
% 2.98/0.94  
% 2.98/0.94  fof(f8,axiom,(
% 2.98/0.94    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.98/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.94  
% 2.98/0.94  fof(f40,plain,(
% 2.98/0.94    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.98/0.94    inference(cnf_transformation,[],[f8])).
% 2.98/0.94  
% 2.98/0.94  fof(f9,axiom,(
% 2.98/0.94    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.98/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.94  
% 2.98/0.94  fof(f41,plain,(
% 2.98/0.94    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.98/0.94    inference(cnf_transformation,[],[f9])).
% 2.98/0.94  
% 2.98/0.94  fof(f10,axiom,(
% 2.98/0.94    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.98/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.94  
% 2.98/0.94  fof(f42,plain,(
% 2.98/0.94    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.98/0.94    inference(cnf_transformation,[],[f10])).
% 2.98/0.94  
% 2.98/0.94  fof(f52,plain,(
% 2.98/0.94    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.98/0.94    inference(definition_unfolding,[],[f41,f42])).
% 2.98/0.94  
% 2.98/0.94  fof(f53,plain,(
% 2.98/0.94    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.98/0.94    inference(definition_unfolding,[],[f40,f52])).
% 2.98/0.94  
% 2.98/0.94  fof(f54,plain,(
% 2.98/0.94    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.98/0.94    inference(definition_unfolding,[],[f39,f53])).
% 2.98/0.94  
% 2.98/0.94  fof(f55,plain,(
% 2.98/0.94    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.98/0.94    inference(definition_unfolding,[],[f38,f54])).
% 2.98/0.94  
% 2.98/0.94  fof(f56,plain,(
% 2.98/0.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.98/0.94    inference(definition_unfolding,[],[f37,f55])).
% 2.98/0.94  
% 2.98/0.94  fof(f57,plain,(
% 2.98/0.94    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.98/0.94    inference(definition_unfolding,[],[f44,f56])).
% 2.98/0.94  
% 2.98/0.94  fof(f58,plain,(
% 2.98/0.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.98/0.94    inference(definition_unfolding,[],[f35,f57])).
% 2.98/0.94  
% 2.98/0.94  fof(f60,plain,(
% 2.98/0.94    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 2.98/0.94    inference(definition_unfolding,[],[f36,f58])).
% 2.98/0.94  
% 2.98/0.94  fof(f11,axiom,(
% 2.98/0.94    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.98/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.94  
% 2.98/0.94  fof(f43,plain,(
% 2.98/0.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.98/0.94    inference(cnf_transformation,[],[f11])).
% 2.98/0.94  
% 2.98/0.94  fof(f61,plain,(
% 2.98/0.94    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1)) )),
% 2.98/0.94    inference(definition_unfolding,[],[f43,f58])).
% 2.98/0.94  
% 2.98/0.94  fof(f16,axiom,(
% 2.98/0.94    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.98/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.94  
% 2.98/0.94  fof(f23,plain,(
% 2.98/0.94    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.98/0.94    inference(ennf_transformation,[],[f16])).
% 2.98/0.94  
% 2.98/0.94  fof(f24,plain,(
% 2.98/0.94    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.98/0.94    inference(flattening,[],[f23])).
% 2.98/0.94  
% 2.98/0.94  fof(f48,plain,(
% 2.98/0.94    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.98/0.94    inference(cnf_transformation,[],[f24])).
% 2.98/0.94  
% 2.98/0.94  fof(f17,axiom,(
% 2.98/0.94    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 2.98/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.94  
% 2.98/0.94  fof(f25,plain,(
% 2.98/0.94    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.98/0.94    inference(ennf_transformation,[],[f17])).
% 2.98/0.94  
% 2.98/0.94  fof(f49,plain,(
% 2.98/0.94    ( ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 2.98/0.94    inference(cnf_transformation,[],[f25])).
% 2.98/0.94  
% 2.98/0.94  fof(f14,axiom,(
% 2.98/0.94    ! [X0,X1,X2] : (v1_relat_1(X2) => k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)))),
% 2.98/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.98/0.94  
% 2.98/0.94  fof(f21,plain,(
% 2.98/0.94    ! [X0,X1,X2] : (k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_relat_1(X2))),
% 2.98/0.94    inference(ennf_transformation,[],[f14])).
% 2.98/0.94  
% 2.98/0.94  fof(f46,plain,(
% 2.98/0.94    ( ! [X2,X0,X1] : (k6_subset_1(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) = k7_relat_1(X2,k6_subset_1(X0,X1)) | ~v1_relat_1(X2)) )),
% 2.98/0.94    inference(cnf_transformation,[],[f21])).
% 2.98/0.94  
% 2.98/0.94  fof(f51,plain,(
% 2.98/0.94    k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0)))),
% 2.98/0.94    inference(cnf_transformation,[],[f30])).
% 2.98/0.94  
% 2.98/0.94  cnf(c_12,negated_conjecture,
% 2.98/0.94      ( v1_relat_1(sK1) ),
% 2.98/0.94      inference(cnf_transformation,[],[f50]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_372,plain,
% 2.98/0.94      ( v1_relat_1(sK1) = iProver_top ),
% 2.98/0.94      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_4,plain,
% 2.98/0.94      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
% 2.98/0.94      inference(cnf_transformation,[],[f60]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_378,plain,
% 2.98/0.94      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) = iProver_top ),
% 2.98/0.94      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_5,plain,
% 2.98/0.94      ( k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) = k6_subset_1(X0,X1) ),
% 2.98/0.94      inference(cnf_transformation,[],[f61]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_397,plain,
% 2.98/0.94      ( r1_tarski(k6_subset_1(X0,X1),X0) = iProver_top ),
% 2.98/0.94      inference(light_normalisation,[status(thm)],[c_378,c_5]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_9,plain,
% 2.98/0.94      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 2.98/0.94      | ~ v1_relat_1(X1)
% 2.98/0.94      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 2.98/0.94      inference(cnf_transformation,[],[f48]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_374,plain,
% 2.98/0.94      ( k1_relat_1(k7_relat_1(X0,X1)) = X1
% 2.98/0.94      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 2.98/0.94      | v1_relat_1(X0) != iProver_top ),
% 2.98/0.94      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_695,plain,
% 2.98/0.94      ( k1_relat_1(k7_relat_1(X0,k6_subset_1(k1_relat_1(X0),X1))) = k6_subset_1(k1_relat_1(X0),X1)
% 2.98/0.94      | v1_relat_1(X0) != iProver_top ),
% 2.98/0.94      inference(superposition,[status(thm)],[c_397,c_374]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_4104,plain,
% 2.98/0.94      ( k1_relat_1(k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
% 2.98/0.94      inference(superposition,[status(thm)],[c_372,c_695]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_10,plain,
% 2.98/0.94      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0 ),
% 2.98/0.94      inference(cnf_transformation,[],[f49]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_373,plain,
% 2.98/0.94      ( k7_relat_1(X0,k1_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 2.98/0.94      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_519,plain,
% 2.98/0.94      ( k7_relat_1(sK1,k1_relat_1(sK1)) = sK1 ),
% 2.98/0.94      inference(superposition,[status(thm)],[c_372,c_373]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_7,plain,
% 2.98/0.94      ( ~ v1_relat_1(X0)
% 2.98/0.94      | k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2)) ),
% 2.98/0.94      inference(cnf_transformation,[],[f46]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_376,plain,
% 2.98/0.94      ( k6_subset_1(k7_relat_1(X0,X1),k7_relat_1(X0,X2)) = k7_relat_1(X0,k6_subset_1(X1,X2))
% 2.98/0.94      | v1_relat_1(X0) != iProver_top ),
% 2.98/0.94      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_932,plain,
% 2.98/0.94      ( k6_subset_1(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)) = k7_relat_1(sK1,k6_subset_1(X0,X1)) ),
% 2.98/0.94      inference(superposition,[status(thm)],[c_372,c_376]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_944,plain,
% 2.98/0.94      ( k7_relat_1(sK1,k6_subset_1(k1_relat_1(sK1),X0)) = k6_subset_1(sK1,k7_relat_1(sK1,X0)) ),
% 2.98/0.94      inference(superposition,[status(thm)],[c_519,c_932]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_4118,plain,
% 2.98/0.94      ( k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,X0))) = k6_subset_1(k1_relat_1(sK1),X0) ),
% 2.98/0.94      inference(light_normalisation,[status(thm)],[c_4104,c_944]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_11,negated_conjecture,
% 2.98/0.94      ( k6_subset_1(k1_relat_1(sK1),sK0) != k1_relat_1(k6_subset_1(sK1,k7_relat_1(sK1,sK0))) ),
% 2.98/0.94      inference(cnf_transformation,[],[f51]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_4752,plain,
% 2.98/0.94      ( k6_subset_1(k1_relat_1(sK1),sK0) != k6_subset_1(k1_relat_1(sK1),sK0) ),
% 2.98/0.94      inference(demodulation,[status(thm)],[c_4118,c_11]) ).
% 2.98/0.94  
% 2.98/0.94  cnf(c_4756,plain,
% 2.98/0.94      ( $false ),
% 2.98/0.94      inference(equality_resolution_simp,[status(thm)],[c_4752]) ).
% 2.98/0.94  
% 2.98/0.94  
% 2.98/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 2.98/0.94  
% 2.98/0.94  ------                               Statistics
% 2.98/0.94  
% 2.98/0.94  ------ General
% 2.98/0.94  
% 2.98/0.94  abstr_ref_over_cycles:                  0
% 2.98/0.94  abstr_ref_under_cycles:                 0
% 2.98/0.94  gc_basic_clause_elim:                   0
% 2.98/0.94  forced_gc_time:                         0
% 2.98/0.94  parsing_time:                           0.006
% 2.98/0.94  unif_index_cands_time:                  0.
% 2.98/0.94  unif_index_add_time:                    0.
% 2.98/0.94  orderings_time:                         0.
% 2.98/0.94  out_proof_time:                         0.005
% 2.98/0.94  total_time:                             0.216
% 2.98/0.94  num_of_symbols:                         41
% 2.98/0.94  num_of_terms:                           6597
% 2.98/0.94  
% 2.98/0.94  ------ Preprocessing
% 2.98/0.94  
% 2.98/0.94  num_of_splits:                          0
% 2.98/0.94  num_of_split_atoms:                     0
% 2.98/0.94  num_of_reused_defs:                     0
% 2.98/0.94  num_eq_ax_congr_red:                    6
% 2.98/0.94  num_of_sem_filtered_clauses:            1
% 2.98/0.94  num_of_subtypes:                        0
% 2.98/0.94  monotx_restored_types:                  0
% 2.98/0.94  sat_num_of_epr_types:                   0
% 2.98/0.94  sat_num_of_non_cyclic_types:            0
% 2.98/0.94  sat_guarded_non_collapsed_types:        0
% 2.98/0.94  num_pure_diseq_elim:                    0
% 2.98/0.94  simp_replaced_by:                       0
% 2.98/0.94  res_preprocessed:                       69
% 2.98/0.94  prep_upred:                             0
% 2.98/0.94  prep_unflattend:                        0
% 2.98/0.94  smt_new_axioms:                         0
% 2.98/0.94  pred_elim_cands:                        2
% 2.98/0.94  pred_elim:                              0
% 2.98/0.94  pred_elim_cl:                           0
% 2.98/0.94  pred_elim_cycles:                       2
% 2.98/0.94  merged_defs:                            0
% 2.98/0.94  merged_defs_ncl:                        0
% 2.98/0.94  bin_hyper_res:                          0
% 2.98/0.94  prep_cycles:                            4
% 2.98/0.94  pred_elim_time:                         0.
% 2.98/0.94  splitting_time:                         0.
% 2.98/0.94  sem_filter_time:                        0.
% 2.98/0.94  monotx_time:                            0.
% 2.98/0.94  subtype_inf_time:                       0.
% 2.98/0.94  
% 2.98/0.94  ------ Problem properties
% 2.98/0.94  
% 2.98/0.94  clauses:                                12
% 2.98/0.94  conjectures:                            2
% 2.98/0.94  epr:                                    3
% 2.98/0.94  horn:                                   12
% 2.98/0.94  ground:                                 2
% 2.98/0.94  unary:                                  6
% 2.98/0.94  binary:                                 4
% 2.98/0.94  lits:                                   20
% 2.98/0.94  lits_eq:                                8
% 2.98/0.94  fd_pure:                                0
% 2.98/0.94  fd_pseudo:                              0
% 2.98/0.94  fd_cond:                                0
% 2.98/0.94  fd_pseudo_cond:                         1
% 2.98/0.94  ac_symbols:                             0
% 2.98/0.94  
% 2.98/0.94  ------ Propositional Solver
% 2.98/0.94  
% 2.98/0.94  prop_solver_calls:                      29
% 2.98/0.94  prop_fast_solver_calls:                 360
% 2.98/0.94  smt_solver_calls:                       0
% 2.98/0.94  smt_fast_solver_calls:                  0
% 2.98/0.94  prop_num_of_clauses:                    2001
% 2.98/0.94  prop_preprocess_simplified:             3709
% 2.98/0.94  prop_fo_subsumed:                       4
% 2.98/0.94  prop_solver_time:                       0.
% 2.98/0.94  smt_solver_time:                        0.
% 2.98/0.94  smt_fast_solver_time:                   0.
% 2.98/0.94  prop_fast_solver_time:                  0.
% 2.98/0.94  prop_unsat_core_time:                   0.
% 2.98/0.94  
% 2.98/0.94  ------ QBF
% 2.98/0.94  
% 2.98/0.94  qbf_q_res:                              0
% 2.98/0.94  qbf_num_tautologies:                    0
% 2.98/0.94  qbf_prep_cycles:                        0
% 2.98/0.94  
% 2.98/0.94  ------ BMC1
% 2.98/0.94  
% 2.98/0.94  bmc1_current_bound:                     -1
% 2.98/0.94  bmc1_last_solved_bound:                 -1
% 2.98/0.94  bmc1_unsat_core_size:                   -1
% 2.98/0.94  bmc1_unsat_core_parents_size:           -1
% 2.98/0.94  bmc1_merge_next_fun:                    0
% 2.98/0.94  bmc1_unsat_core_clauses_time:           0.
% 2.98/0.94  
% 2.98/0.94  ------ Instantiation
% 2.98/0.94  
% 2.98/0.94  inst_num_of_clauses:                    561
% 2.98/0.94  inst_num_in_passive:                    149
% 2.98/0.94  inst_num_in_active:                     257
% 2.98/0.94  inst_num_in_unprocessed:                155
% 2.98/0.94  inst_num_of_loops:                      270
% 2.98/0.94  inst_num_of_learning_restarts:          0
% 2.98/0.94  inst_num_moves_active_passive:          8
% 2.98/0.94  inst_lit_activity:                      0
% 2.98/0.94  inst_lit_activity_moves:                0
% 2.98/0.94  inst_num_tautologies:                   0
% 2.98/0.94  inst_num_prop_implied:                  0
% 2.98/0.94  inst_num_existing_simplified:           0
% 2.98/0.94  inst_num_eq_res_simplified:             0
% 2.98/0.94  inst_num_child_elim:                    0
% 2.98/0.94  inst_num_of_dismatching_blockings:      278
% 2.98/0.94  inst_num_of_non_proper_insts:           660
% 2.98/0.94  inst_num_of_duplicates:                 0
% 2.98/0.94  inst_inst_num_from_inst_to_res:         0
% 2.98/0.94  inst_dismatching_checking_time:         0.
% 2.98/0.94  
% 2.98/0.94  ------ Resolution
% 2.98/0.94  
% 2.98/0.94  res_num_of_clauses:                     0
% 2.98/0.94  res_num_in_passive:                     0
% 2.98/0.94  res_num_in_active:                      0
% 2.98/0.94  res_num_of_loops:                       73
% 2.98/0.94  res_forward_subset_subsumed:            121
% 2.98/0.94  res_backward_subset_subsumed:           2
% 2.98/0.94  res_forward_subsumed:                   0
% 2.98/0.94  res_backward_subsumed:                  0
% 2.98/0.94  res_forward_subsumption_resolution:     0
% 2.98/0.94  res_backward_subsumption_resolution:    0
% 2.98/0.94  res_clause_to_clause_subsumption:       523
% 2.98/0.94  res_orphan_elimination:                 0
% 2.98/0.94  res_tautology_del:                      71
% 2.98/0.94  res_num_eq_res_simplified:              0
% 2.98/0.94  res_num_sel_changes:                    0
% 2.98/0.94  res_moves_from_active_to_pass:          0
% 2.98/0.94  
% 2.98/0.94  ------ Superposition
% 2.98/0.94  
% 2.98/0.94  sup_time_total:                         0.
% 2.98/0.94  sup_time_generating:                    0.
% 2.98/0.94  sup_time_sim_full:                      0.
% 2.98/0.94  sup_time_sim_immed:                     0.
% 2.98/0.94  
% 2.98/0.94  sup_num_of_clauses:                     251
% 2.98/0.94  sup_num_in_active:                      47
% 2.98/0.94  sup_num_in_passive:                     204
% 2.98/0.94  sup_num_of_loops:                       52
% 2.98/0.94  sup_fw_superposition:                   159
% 2.98/0.94  sup_bw_superposition:                   213
% 2.98/0.94  sup_immediate_simplified:               103
% 2.98/0.94  sup_given_eliminated:                   0
% 2.98/0.94  comparisons_done:                       0
% 2.98/0.94  comparisons_avoided:                    0
% 2.98/0.94  
% 2.98/0.94  ------ Simplifications
% 2.98/0.94  
% 2.98/0.94  
% 2.98/0.94  sim_fw_subset_subsumed:                 7
% 2.98/0.94  sim_bw_subset_subsumed:                 0
% 2.98/0.94  sim_fw_subsumed:                        33
% 2.98/0.94  sim_bw_subsumed:                        0
% 2.98/0.94  sim_fw_subsumption_res:                 0
% 2.98/0.94  sim_bw_subsumption_res:                 0
% 2.98/0.94  sim_tautology_del:                      2
% 2.98/0.94  sim_eq_tautology_del:                   21
% 2.98/0.94  sim_eq_res_simp:                        0
% 2.98/0.94  sim_fw_demodulated:                     10
% 2.98/0.94  sim_bw_demodulated:                     10
% 2.98/0.94  sim_light_normalised:                   69
% 2.98/0.94  sim_joinable_taut:                      0
% 2.98/0.94  sim_joinable_simp:                      0
% 2.98/0.94  sim_ac_normalised:                      0
% 2.98/0.94  sim_smt_subsumption:                    0
% 2.98/0.94  
%------------------------------------------------------------------------------
