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
% DateTime   : Thu Dec  3 11:25:05 EST 2020

% Result     : Theorem 11.92s
% Output     : CNFRefutation 11.92s
% Verified   : 
% Statistics : Number of formulae       :   50 (  79 expanded)
%              Number of clauses        :   20 (  24 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   51 (  80 expanded)
%              Number of equality atoms :   50 (  79 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f27,f39,f39])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f34,f39])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f19])).

fof(f23,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f20])).

fof(f24,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).

fof(f44,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f55,plain,(
    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f44,f39,f28,f28])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f28,f39])).

cnf(c_9,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_481,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_9,c_1])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_169,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_7,c_11])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_381,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_11])).

cnf(c_486,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
    inference(light_normalisation,[status(thm)],[c_481,c_169,c_381])).

cnf(c_10,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1095,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
    inference(superposition,[status(thm)],[c_486,c_10])).

cnf(c_16,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_266,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_0,c_16])).

cnf(c_50223,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_1095,c_266])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_15,plain,
    ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1266,plain,
    ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15,c_11])).

cnf(c_50224,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_50223,c_6,c_1266])).

cnf(c_421,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_50224,c_421])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.92/2.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.92/2.00  
% 11.92/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.92/2.00  
% 11.92/2.00  ------  iProver source info
% 11.92/2.00  
% 11.92/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.92/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.92/2.00  git: non_committed_changes: false
% 11.92/2.00  git: last_make_outside_of_git: false
% 11.92/2.00  
% 11.92/2.00  ------ 
% 11.92/2.00  
% 11.92/2.00  ------ Input Options
% 11.92/2.00  
% 11.92/2.00  --out_options                           all
% 11.92/2.00  --tptp_safe_out                         true
% 11.92/2.00  --problem_path                          ""
% 11.92/2.00  --include_path                          ""
% 11.92/2.00  --clausifier                            res/vclausify_rel
% 11.92/2.00  --clausifier_options                    ""
% 11.92/2.00  --stdin                                 false
% 11.92/2.00  --stats_out                             all
% 11.92/2.00  
% 11.92/2.00  ------ General Options
% 11.92/2.00  
% 11.92/2.00  --fof                                   false
% 11.92/2.00  --time_out_real                         305.
% 11.92/2.00  --time_out_virtual                      -1.
% 11.92/2.00  --symbol_type_check                     false
% 11.92/2.00  --clausify_out                          false
% 11.92/2.00  --sig_cnt_out                           false
% 11.92/2.00  --trig_cnt_out                          false
% 11.92/2.00  --trig_cnt_out_tolerance                1.
% 11.92/2.00  --trig_cnt_out_sk_spl                   false
% 11.92/2.00  --abstr_cl_out                          false
% 11.92/2.00  
% 11.92/2.00  ------ Global Options
% 11.92/2.00  
% 11.92/2.00  --schedule                              default
% 11.92/2.00  --add_important_lit                     false
% 11.92/2.00  --prop_solver_per_cl                    1000
% 11.92/2.00  --min_unsat_core                        false
% 11.92/2.00  --soft_assumptions                      false
% 11.92/2.00  --soft_lemma_size                       3
% 11.92/2.00  --prop_impl_unit_size                   0
% 11.92/2.00  --prop_impl_unit                        []
% 11.92/2.00  --share_sel_clauses                     true
% 11.92/2.00  --reset_solvers                         false
% 11.92/2.00  --bc_imp_inh                            [conj_cone]
% 11.92/2.00  --conj_cone_tolerance                   3.
% 11.92/2.00  --extra_neg_conj                        none
% 11.92/2.00  --large_theory_mode                     true
% 11.92/2.00  --prolific_symb_bound                   200
% 11.92/2.00  --lt_threshold                          2000
% 11.92/2.00  --clause_weak_htbl                      true
% 11.92/2.00  --gc_record_bc_elim                     false
% 11.92/2.00  
% 11.92/2.00  ------ Preprocessing Options
% 11.92/2.00  
% 11.92/2.00  --preprocessing_flag                    true
% 11.92/2.00  --time_out_prep_mult                    0.1
% 11.92/2.00  --splitting_mode                        input
% 11.92/2.00  --splitting_grd                         true
% 11.92/2.00  --splitting_cvd                         false
% 11.92/2.00  --splitting_cvd_svl                     false
% 11.92/2.00  --splitting_nvd                         32
% 11.92/2.00  --sub_typing                            true
% 11.92/2.00  --prep_gs_sim                           true
% 11.92/2.00  --prep_unflatten                        true
% 11.92/2.00  --prep_res_sim                          true
% 11.92/2.00  --prep_upred                            true
% 11.92/2.00  --prep_sem_filter                       exhaustive
% 11.92/2.00  --prep_sem_filter_out                   false
% 11.92/2.00  --pred_elim                             true
% 11.92/2.00  --res_sim_input                         true
% 11.92/2.00  --eq_ax_congr_red                       true
% 11.92/2.00  --pure_diseq_elim                       true
% 11.92/2.00  --brand_transform                       false
% 11.92/2.00  --non_eq_to_eq                          false
% 11.92/2.00  --prep_def_merge                        true
% 11.92/2.00  --prep_def_merge_prop_impl              false
% 11.92/2.00  --prep_def_merge_mbd                    true
% 11.92/2.00  --prep_def_merge_tr_red                 false
% 11.92/2.00  --prep_def_merge_tr_cl                  false
% 11.92/2.00  --smt_preprocessing                     true
% 11.92/2.00  --smt_ac_axioms                         fast
% 11.92/2.00  --preprocessed_out                      false
% 11.92/2.00  --preprocessed_stats                    false
% 11.92/2.00  
% 11.92/2.00  ------ Abstraction refinement Options
% 11.92/2.00  
% 11.92/2.00  --abstr_ref                             []
% 11.92/2.00  --abstr_ref_prep                        false
% 11.92/2.00  --abstr_ref_until_sat                   false
% 11.92/2.00  --abstr_ref_sig_restrict                funpre
% 11.92/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.92/2.00  --abstr_ref_under                       []
% 11.92/2.00  
% 11.92/2.00  ------ SAT Options
% 11.92/2.00  
% 11.92/2.00  --sat_mode                              false
% 11.92/2.00  --sat_fm_restart_options                ""
% 11.92/2.00  --sat_gr_def                            false
% 11.92/2.00  --sat_epr_types                         true
% 11.92/2.00  --sat_non_cyclic_types                  false
% 11.92/2.00  --sat_finite_models                     false
% 11.92/2.00  --sat_fm_lemmas                         false
% 11.92/2.00  --sat_fm_prep                           false
% 11.92/2.00  --sat_fm_uc_incr                        true
% 11.92/2.00  --sat_out_model                         small
% 11.92/2.00  --sat_out_clauses                       false
% 11.92/2.00  
% 11.92/2.00  ------ QBF Options
% 11.92/2.00  
% 11.92/2.00  --qbf_mode                              false
% 11.92/2.00  --qbf_elim_univ                         false
% 11.92/2.00  --qbf_dom_inst                          none
% 11.92/2.00  --qbf_dom_pre_inst                      false
% 11.92/2.00  --qbf_sk_in                             false
% 11.92/2.00  --qbf_pred_elim                         true
% 11.92/2.00  --qbf_split                             512
% 11.92/2.00  
% 11.92/2.00  ------ BMC1 Options
% 11.92/2.00  
% 11.92/2.00  --bmc1_incremental                      false
% 11.92/2.00  --bmc1_axioms                           reachable_all
% 11.92/2.00  --bmc1_min_bound                        0
% 11.92/2.00  --bmc1_max_bound                        -1
% 11.92/2.00  --bmc1_max_bound_default                -1
% 11.92/2.00  --bmc1_symbol_reachability              true
% 11.92/2.00  --bmc1_property_lemmas                  false
% 11.92/2.00  --bmc1_k_induction                      false
% 11.92/2.00  --bmc1_non_equiv_states                 false
% 11.92/2.00  --bmc1_deadlock                         false
% 11.92/2.00  --bmc1_ucm                              false
% 11.92/2.00  --bmc1_add_unsat_core                   none
% 11.92/2.00  --bmc1_unsat_core_children              false
% 11.92/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.92/2.00  --bmc1_out_stat                         full
% 11.92/2.00  --bmc1_ground_init                      false
% 11.92/2.00  --bmc1_pre_inst_next_state              false
% 11.92/2.00  --bmc1_pre_inst_state                   false
% 11.92/2.00  --bmc1_pre_inst_reach_state             false
% 11.92/2.00  --bmc1_out_unsat_core                   false
% 11.92/2.00  --bmc1_aig_witness_out                  false
% 11.92/2.00  --bmc1_verbose                          false
% 11.92/2.00  --bmc1_dump_clauses_tptp                false
% 11.92/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.92/2.00  --bmc1_dump_file                        -
% 11.92/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.92/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.92/2.00  --bmc1_ucm_extend_mode                  1
% 11.92/2.00  --bmc1_ucm_init_mode                    2
% 11.92/2.00  --bmc1_ucm_cone_mode                    none
% 11.92/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.92/2.00  --bmc1_ucm_relax_model                  4
% 11.92/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.92/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.92/2.00  --bmc1_ucm_layered_model                none
% 11.92/2.00  --bmc1_ucm_max_lemma_size               10
% 11.92/2.00  
% 11.92/2.00  ------ AIG Options
% 11.92/2.00  
% 11.92/2.00  --aig_mode                              false
% 11.92/2.00  
% 11.92/2.00  ------ Instantiation Options
% 11.92/2.00  
% 11.92/2.00  --instantiation_flag                    true
% 11.92/2.00  --inst_sos_flag                         true
% 11.92/2.00  --inst_sos_phase                        true
% 11.92/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.92/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.92/2.00  --inst_lit_sel_side                     num_symb
% 11.92/2.00  --inst_solver_per_active                1400
% 11.92/2.00  --inst_solver_calls_frac                1.
% 11.92/2.00  --inst_passive_queue_type               priority_queues
% 11.92/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.92/2.00  --inst_passive_queues_freq              [25;2]
% 11.92/2.00  --inst_dismatching                      true
% 11.92/2.00  --inst_eager_unprocessed_to_passive     true
% 11.92/2.00  --inst_prop_sim_given                   true
% 11.92/2.00  --inst_prop_sim_new                     false
% 11.92/2.00  --inst_subs_new                         false
% 11.92/2.00  --inst_eq_res_simp                      false
% 11.92/2.00  --inst_subs_given                       false
% 11.92/2.00  --inst_orphan_elimination               true
% 11.92/2.00  --inst_learning_loop_flag               true
% 11.92/2.00  --inst_learning_start                   3000
% 11.92/2.00  --inst_learning_factor                  2
% 11.92/2.00  --inst_start_prop_sim_after_learn       3
% 11.92/2.00  --inst_sel_renew                        solver
% 11.92/2.00  --inst_lit_activity_flag                true
% 11.92/2.00  --inst_restr_to_given                   false
% 11.92/2.00  --inst_activity_threshold               500
% 11.92/2.00  --inst_out_proof                        true
% 11.92/2.00  
% 11.92/2.00  ------ Resolution Options
% 11.92/2.00  
% 11.92/2.00  --resolution_flag                       true
% 11.92/2.00  --res_lit_sel                           adaptive
% 11.92/2.00  --res_lit_sel_side                      none
% 11.92/2.00  --res_ordering                          kbo
% 11.92/2.00  --res_to_prop_solver                    active
% 11.92/2.00  --res_prop_simpl_new                    false
% 11.92/2.00  --res_prop_simpl_given                  true
% 11.92/2.00  --res_passive_queue_type                priority_queues
% 11.92/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.92/2.00  --res_passive_queues_freq               [15;5]
% 11.92/2.00  --res_forward_subs                      full
% 11.92/2.00  --res_backward_subs                     full
% 11.92/2.00  --res_forward_subs_resolution           true
% 11.92/2.00  --res_backward_subs_resolution          true
% 11.92/2.00  --res_orphan_elimination                true
% 11.92/2.00  --res_time_limit                        2.
% 11.92/2.00  --res_out_proof                         true
% 11.92/2.00  
% 11.92/2.00  ------ Superposition Options
% 11.92/2.00  
% 11.92/2.00  --superposition_flag                    true
% 11.92/2.00  --sup_passive_queue_type                priority_queues
% 11.92/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.92/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.92/2.00  --demod_completeness_check              fast
% 11.92/2.00  --demod_use_ground                      true
% 11.92/2.00  --sup_to_prop_solver                    passive
% 11.92/2.00  --sup_prop_simpl_new                    true
% 11.92/2.00  --sup_prop_simpl_given                  true
% 11.92/2.00  --sup_fun_splitting                     true
% 11.92/2.00  --sup_smt_interval                      50000
% 11.92/2.00  
% 11.92/2.00  ------ Superposition Simplification Setup
% 11.92/2.00  
% 11.92/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.92/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.92/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.92/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.92/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.92/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.92/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.92/2.00  --sup_immed_triv                        [TrivRules]
% 11.92/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.92/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.92/2.00  --sup_immed_bw_main                     []
% 11.92/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.92/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.92/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.92/2.00  --sup_input_bw                          []
% 11.92/2.00  
% 11.92/2.00  ------ Combination Options
% 11.92/2.00  
% 11.92/2.00  --comb_res_mult                         3
% 11.92/2.00  --comb_sup_mult                         2
% 11.92/2.00  --comb_inst_mult                        10
% 11.92/2.00  
% 11.92/2.00  ------ Debug Options
% 11.92/2.00  
% 11.92/2.00  --dbg_backtrace                         false
% 11.92/2.00  --dbg_dump_prop_clauses                 false
% 11.92/2.00  --dbg_dump_prop_clauses_file            -
% 11.92/2.00  --dbg_out_stat                          false
% 11.92/2.00  ------ Parsing...
% 11.92/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.92/2.00  
% 11.92/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.92/2.00  
% 11.92/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.92/2.00  
% 11.92/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.92/2.00  ------ Proving...
% 11.92/2.00  ------ Problem Properties 
% 11.92/2.00  
% 11.92/2.00  
% 11.92/2.00  clauses                                 16
% 11.92/2.00  conjectures                             1
% 11.92/2.00  EPR                                     0
% 11.92/2.00  Horn                                    16
% 11.92/2.00  unary                                   15
% 11.92/2.00  binary                                  1
% 11.92/2.00  lits                                    17
% 11.92/2.00  lits eq                                 15
% 11.92/2.00  fd_pure                                 0
% 11.92/2.00  fd_pseudo                               0
% 11.92/2.00  fd_cond                                 0
% 11.92/2.00  fd_pseudo_cond                          0
% 11.92/2.00  AC symbols                              0
% 11.92/2.00  
% 11.92/2.00  ------ Schedule dynamic 5 is on 
% 11.92/2.00  
% 11.92/2.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.92/2.00  
% 11.92/2.00  
% 11.92/2.00  ------ 
% 11.92/2.00  Current options:
% 11.92/2.00  ------ 
% 11.92/2.00  
% 11.92/2.00  ------ Input Options
% 11.92/2.00  
% 11.92/2.00  --out_options                           all
% 11.92/2.00  --tptp_safe_out                         true
% 11.92/2.00  --problem_path                          ""
% 11.92/2.00  --include_path                          ""
% 11.92/2.00  --clausifier                            res/vclausify_rel
% 11.92/2.00  --clausifier_options                    ""
% 11.92/2.00  --stdin                                 false
% 11.92/2.00  --stats_out                             all
% 11.92/2.00  
% 11.92/2.00  ------ General Options
% 11.92/2.00  
% 11.92/2.00  --fof                                   false
% 11.92/2.00  --time_out_real                         305.
% 11.92/2.00  --time_out_virtual                      -1.
% 11.92/2.00  --symbol_type_check                     false
% 11.92/2.00  --clausify_out                          false
% 11.92/2.00  --sig_cnt_out                           false
% 11.92/2.00  --trig_cnt_out                          false
% 11.92/2.00  --trig_cnt_out_tolerance                1.
% 11.92/2.00  --trig_cnt_out_sk_spl                   false
% 11.92/2.00  --abstr_cl_out                          false
% 11.92/2.00  
% 11.92/2.00  ------ Global Options
% 11.92/2.00  
% 11.92/2.00  --schedule                              default
% 11.92/2.00  --add_important_lit                     false
% 11.92/2.00  --prop_solver_per_cl                    1000
% 11.92/2.00  --min_unsat_core                        false
% 11.92/2.00  --soft_assumptions                      false
% 11.92/2.00  --soft_lemma_size                       3
% 11.92/2.00  --prop_impl_unit_size                   0
% 11.92/2.00  --prop_impl_unit                        []
% 11.92/2.00  --share_sel_clauses                     true
% 11.92/2.00  --reset_solvers                         false
% 11.92/2.00  --bc_imp_inh                            [conj_cone]
% 11.92/2.00  --conj_cone_tolerance                   3.
% 11.92/2.00  --extra_neg_conj                        none
% 11.92/2.00  --large_theory_mode                     true
% 11.92/2.00  --prolific_symb_bound                   200
% 11.92/2.00  --lt_threshold                          2000
% 11.92/2.00  --clause_weak_htbl                      true
% 11.92/2.00  --gc_record_bc_elim                     false
% 11.92/2.00  
% 11.92/2.00  ------ Preprocessing Options
% 11.92/2.00  
% 11.92/2.00  --preprocessing_flag                    true
% 11.92/2.00  --time_out_prep_mult                    0.1
% 11.92/2.00  --splitting_mode                        input
% 11.92/2.00  --splitting_grd                         true
% 11.92/2.00  --splitting_cvd                         false
% 11.92/2.00  --splitting_cvd_svl                     false
% 11.92/2.00  --splitting_nvd                         32
% 11.92/2.00  --sub_typing                            true
% 11.92/2.00  --prep_gs_sim                           true
% 11.92/2.00  --prep_unflatten                        true
% 11.92/2.00  --prep_res_sim                          true
% 11.92/2.00  --prep_upred                            true
% 11.92/2.00  --prep_sem_filter                       exhaustive
% 11.92/2.00  --prep_sem_filter_out                   false
% 11.92/2.00  --pred_elim                             true
% 11.92/2.00  --res_sim_input                         true
% 11.92/2.00  --eq_ax_congr_red                       true
% 11.92/2.00  --pure_diseq_elim                       true
% 11.92/2.00  --brand_transform                       false
% 11.92/2.00  --non_eq_to_eq                          false
% 11.92/2.00  --prep_def_merge                        true
% 11.92/2.00  --prep_def_merge_prop_impl              false
% 11.92/2.00  --prep_def_merge_mbd                    true
% 11.92/2.00  --prep_def_merge_tr_red                 false
% 11.92/2.00  --prep_def_merge_tr_cl                  false
% 11.92/2.00  --smt_preprocessing                     true
% 11.92/2.00  --smt_ac_axioms                         fast
% 11.92/2.00  --preprocessed_out                      false
% 11.92/2.00  --preprocessed_stats                    false
% 11.92/2.00  
% 11.92/2.00  ------ Abstraction refinement Options
% 11.92/2.00  
% 11.92/2.00  --abstr_ref                             []
% 11.92/2.00  --abstr_ref_prep                        false
% 11.92/2.00  --abstr_ref_until_sat                   false
% 11.92/2.00  --abstr_ref_sig_restrict                funpre
% 11.92/2.00  --abstr_ref_af_restrict_to_split_sk     false
% 11.92/2.00  --abstr_ref_under                       []
% 11.92/2.00  
% 11.92/2.00  ------ SAT Options
% 11.92/2.00  
% 11.92/2.00  --sat_mode                              false
% 11.92/2.00  --sat_fm_restart_options                ""
% 11.92/2.00  --sat_gr_def                            false
% 11.92/2.00  --sat_epr_types                         true
% 11.92/2.00  --sat_non_cyclic_types                  false
% 11.92/2.00  --sat_finite_models                     false
% 11.92/2.00  --sat_fm_lemmas                         false
% 11.92/2.00  --sat_fm_prep                           false
% 11.92/2.00  --sat_fm_uc_incr                        true
% 11.92/2.00  --sat_out_model                         small
% 11.92/2.00  --sat_out_clauses                       false
% 11.92/2.00  
% 11.92/2.00  ------ QBF Options
% 11.92/2.00  
% 11.92/2.00  --qbf_mode                              false
% 11.92/2.00  --qbf_elim_univ                         false
% 11.92/2.00  --qbf_dom_inst                          none
% 11.92/2.00  --qbf_dom_pre_inst                      false
% 11.92/2.00  --qbf_sk_in                             false
% 11.92/2.00  --qbf_pred_elim                         true
% 11.92/2.00  --qbf_split                             512
% 11.92/2.00  
% 11.92/2.00  ------ BMC1 Options
% 11.92/2.00  
% 11.92/2.00  --bmc1_incremental                      false
% 11.92/2.00  --bmc1_axioms                           reachable_all
% 11.92/2.00  --bmc1_min_bound                        0
% 11.92/2.00  --bmc1_max_bound                        -1
% 11.92/2.00  --bmc1_max_bound_default                -1
% 11.92/2.00  --bmc1_symbol_reachability              true
% 11.92/2.00  --bmc1_property_lemmas                  false
% 11.92/2.00  --bmc1_k_induction                      false
% 11.92/2.00  --bmc1_non_equiv_states                 false
% 11.92/2.00  --bmc1_deadlock                         false
% 11.92/2.00  --bmc1_ucm                              false
% 11.92/2.00  --bmc1_add_unsat_core                   none
% 11.92/2.00  --bmc1_unsat_core_children              false
% 11.92/2.00  --bmc1_unsat_core_extrapolate_axioms    false
% 11.92/2.00  --bmc1_out_stat                         full
% 11.92/2.00  --bmc1_ground_init                      false
% 11.92/2.00  --bmc1_pre_inst_next_state              false
% 11.92/2.00  --bmc1_pre_inst_state                   false
% 11.92/2.00  --bmc1_pre_inst_reach_state             false
% 11.92/2.00  --bmc1_out_unsat_core                   false
% 11.92/2.00  --bmc1_aig_witness_out                  false
% 11.92/2.00  --bmc1_verbose                          false
% 11.92/2.00  --bmc1_dump_clauses_tptp                false
% 11.92/2.00  --bmc1_dump_unsat_core_tptp             false
% 11.92/2.00  --bmc1_dump_file                        -
% 11.92/2.00  --bmc1_ucm_expand_uc_limit              128
% 11.92/2.00  --bmc1_ucm_n_expand_iterations          6
% 11.92/2.00  --bmc1_ucm_extend_mode                  1
% 11.92/2.00  --bmc1_ucm_init_mode                    2
% 11.92/2.00  --bmc1_ucm_cone_mode                    none
% 11.92/2.00  --bmc1_ucm_reduced_relation_type        0
% 11.92/2.00  --bmc1_ucm_relax_model                  4
% 11.92/2.00  --bmc1_ucm_full_tr_after_sat            true
% 11.92/2.00  --bmc1_ucm_expand_neg_assumptions       false
% 11.92/2.00  --bmc1_ucm_layered_model                none
% 11.92/2.00  --bmc1_ucm_max_lemma_size               10
% 11.92/2.00  
% 11.92/2.00  ------ AIG Options
% 11.92/2.00  
% 11.92/2.00  --aig_mode                              false
% 11.92/2.00  
% 11.92/2.00  ------ Instantiation Options
% 11.92/2.00  
% 11.92/2.00  --instantiation_flag                    true
% 11.92/2.00  --inst_sos_flag                         true
% 11.92/2.00  --inst_sos_phase                        true
% 11.92/2.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.92/2.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.92/2.00  --inst_lit_sel_side                     none
% 11.92/2.00  --inst_solver_per_active                1400
% 11.92/2.00  --inst_solver_calls_frac                1.
% 11.92/2.00  --inst_passive_queue_type               priority_queues
% 11.92/2.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.92/2.00  --inst_passive_queues_freq              [25;2]
% 11.92/2.00  --inst_dismatching                      true
% 11.92/2.00  --inst_eager_unprocessed_to_passive     true
% 11.92/2.00  --inst_prop_sim_given                   true
% 11.92/2.00  --inst_prop_sim_new                     false
% 11.92/2.00  --inst_subs_new                         false
% 11.92/2.00  --inst_eq_res_simp                      false
% 11.92/2.00  --inst_subs_given                       false
% 11.92/2.00  --inst_orphan_elimination               true
% 11.92/2.00  --inst_learning_loop_flag               true
% 11.92/2.00  --inst_learning_start                   3000
% 11.92/2.00  --inst_learning_factor                  2
% 11.92/2.00  --inst_start_prop_sim_after_learn       3
% 11.92/2.00  --inst_sel_renew                        solver
% 11.92/2.00  --inst_lit_activity_flag                true
% 11.92/2.00  --inst_restr_to_given                   false
% 11.92/2.00  --inst_activity_threshold               500
% 11.92/2.00  --inst_out_proof                        true
% 11.92/2.00  
% 11.92/2.00  ------ Resolution Options
% 11.92/2.00  
% 11.92/2.00  --resolution_flag                       false
% 11.92/2.00  --res_lit_sel                           adaptive
% 11.92/2.00  --res_lit_sel_side                      none
% 11.92/2.00  --res_ordering                          kbo
% 11.92/2.00  --res_to_prop_solver                    active
% 11.92/2.00  --res_prop_simpl_new                    false
% 11.92/2.00  --res_prop_simpl_given                  true
% 11.92/2.00  --res_passive_queue_type                priority_queues
% 11.92/2.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.92/2.00  --res_passive_queues_freq               [15;5]
% 11.92/2.00  --res_forward_subs                      full
% 11.92/2.00  --res_backward_subs                     full
% 11.92/2.00  --res_forward_subs_resolution           true
% 11.92/2.00  --res_backward_subs_resolution          true
% 11.92/2.00  --res_orphan_elimination                true
% 11.92/2.00  --res_time_limit                        2.
% 11.92/2.00  --res_out_proof                         true
% 11.92/2.00  
% 11.92/2.00  ------ Superposition Options
% 11.92/2.00  
% 11.92/2.00  --superposition_flag                    true
% 11.92/2.00  --sup_passive_queue_type                priority_queues
% 11.92/2.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.92/2.00  --sup_passive_queues_freq               [8;1;4]
% 11.92/2.00  --demod_completeness_check              fast
% 11.92/2.00  --demod_use_ground                      true
% 11.92/2.00  --sup_to_prop_solver                    passive
% 11.92/2.00  --sup_prop_simpl_new                    true
% 11.92/2.00  --sup_prop_simpl_given                  true
% 11.92/2.00  --sup_fun_splitting                     true
% 11.92/2.00  --sup_smt_interval                      50000
% 11.92/2.00  
% 11.92/2.00  ------ Superposition Simplification Setup
% 11.92/2.00  
% 11.92/2.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.92/2.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.92/2.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.92/2.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.92/2.00  --sup_full_triv                         [TrivRules;PropSubs]
% 11.92/2.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.92/2.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.92/2.00  --sup_immed_triv                        [TrivRules]
% 11.92/2.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.92/2.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.92/2.00  --sup_immed_bw_main                     []
% 11.92/2.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.92/2.00  --sup_input_triv                        [Unflattening;TrivRules]
% 11.92/2.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.92/2.00  --sup_input_bw                          []
% 11.92/2.00  
% 11.92/2.00  ------ Combination Options
% 11.92/2.00  
% 11.92/2.00  --comb_res_mult                         3
% 11.92/2.00  --comb_sup_mult                         2
% 11.92/2.00  --comb_inst_mult                        10
% 11.92/2.00  
% 11.92/2.00  ------ Debug Options
% 11.92/2.00  
% 11.92/2.00  --dbg_backtrace                         false
% 11.92/2.00  --dbg_dump_prop_clauses                 false
% 11.92/2.00  --dbg_dump_prop_clauses_file            -
% 11.92/2.00  --dbg_out_stat                          false
% 11.92/2.00  
% 11.92/2.00  
% 11.92/2.00  
% 11.92/2.00  
% 11.92/2.00  ------ Proving...
% 11.92/2.00  
% 11.92/2.00  
% 11.92/2.00  % SZS status Theorem for theBenchmark.p
% 11.92/2.00  
% 11.92/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.92/2.00  
% 11.92/2.00  fof(f11,axiom,(
% 11.92/2.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 11.92/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/2.00  
% 11.92/2.00  fof(f36,plain,(
% 11.92/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 11.92/2.00    inference(cnf_transformation,[],[f11])).
% 11.92/2.00  
% 11.92/2.00  fof(f2,axiom,(
% 11.92/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.92/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/2.00  
% 11.92/2.00  fof(f27,plain,(
% 11.92/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.92/2.00    inference(cnf_transformation,[],[f2])).
% 11.92/2.00  
% 11.92/2.00  fof(f14,axiom,(
% 11.92/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.92/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/2.00  
% 11.92/2.00  fof(f39,plain,(
% 11.92/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.92/2.00    inference(cnf_transformation,[],[f14])).
% 11.92/2.00  
% 11.92/2.00  fof(f45,plain,(
% 11.92/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.92/2.00    inference(definition_unfolding,[],[f27,f39,f39])).
% 11.92/2.00  
% 11.92/2.00  fof(f9,axiom,(
% 11.92/2.00    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 11.92/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/2.00  
% 11.92/2.00  fof(f34,plain,(
% 11.92/2.00    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 11.92/2.00    inference(cnf_transformation,[],[f9])).
% 11.92/2.00  
% 11.92/2.00  fof(f49,plain,(
% 11.92/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 11.92/2.00    inference(definition_unfolding,[],[f34,f39])).
% 11.92/2.00  
% 11.92/2.00  fof(f13,axiom,(
% 11.92/2.00    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 11.92/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/2.00  
% 11.92/2.00  fof(f38,plain,(
% 11.92/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 11.92/2.00    inference(cnf_transformation,[],[f13])).
% 11.92/2.00  
% 11.92/2.00  fof(f1,axiom,(
% 11.92/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.92/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/2.00  
% 11.92/2.00  fof(f26,plain,(
% 11.92/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.92/2.00    inference(cnf_transformation,[],[f1])).
% 11.92/2.00  
% 11.92/2.00  fof(f12,axiom,(
% 11.92/2.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 11.92/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/2.00  
% 11.92/2.00  fof(f37,plain,(
% 11.92/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 11.92/2.00    inference(cnf_transformation,[],[f12])).
% 11.92/2.00  
% 11.92/2.00  fof(f19,conjecture,(
% 11.92/2.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.92/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/2.00  
% 11.92/2.00  fof(f20,negated_conjecture,(
% 11.92/2.00    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.92/2.00    inference(negated_conjecture,[],[f19])).
% 11.92/2.00  
% 11.92/2.00  fof(f23,plain,(
% 11.92/2.00    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 11.92/2.00    inference(ennf_transformation,[],[f20])).
% 11.92/2.00  
% 11.92/2.00  fof(f24,plain,(
% 11.92/2.00    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.92/2.00    introduced(choice_axiom,[])).
% 11.92/2.00  
% 11.92/2.00  fof(f25,plain,(
% 11.92/2.00    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.92/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).
% 11.92/2.00  
% 11.92/2.00  fof(f44,plain,(
% 11.92/2.00    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 11.92/2.00    inference(cnf_transformation,[],[f25])).
% 11.92/2.00  
% 11.92/2.00  fof(f3,axiom,(
% 11.92/2.00    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 11.92/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/2.00  
% 11.92/2.00  fof(f28,plain,(
% 11.92/2.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 11.92/2.00    inference(cnf_transformation,[],[f3])).
% 11.92/2.00  
% 11.92/2.00  fof(f55,plain,(
% 11.92/2.00    k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 11.92/2.00    inference(definition_unfolding,[],[f44,f39,f28,f28])).
% 11.92/2.00  
% 11.92/2.00  fof(f8,axiom,(
% 11.92/2.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.92/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/2.00  
% 11.92/2.00  fof(f33,plain,(
% 11.92/2.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.92/2.00    inference(cnf_transformation,[],[f8])).
% 11.92/2.00  
% 11.92/2.00  fof(f18,axiom,(
% 11.92/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 11.92/2.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/2.00  
% 11.92/2.00  fof(f43,plain,(
% 11.92/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 11.92/2.00    inference(cnf_transformation,[],[f18])).
% 11.92/2.00  
% 11.92/2.00  fof(f54,plain,(
% 11.92/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.92/2.00    inference(definition_unfolding,[],[f43,f28,f39])).
% 11.92/2.00  
% 11.92/2.00  cnf(c_9,plain,
% 11.92/2.00      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 11.92/2.00      inference(cnf_transformation,[],[f36]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(c_1,plain,
% 11.92/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 11.92/2.00      inference(cnf_transformation,[],[f45]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(c_481,plain,
% 11.92/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X1,X0))) = k4_xboole_0(k2_xboole_0(X1,X0),k4_xboole_0(X1,X0)) ),
% 11.92/2.00      inference(superposition,[status(thm)],[c_9,c_1]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(c_7,plain,
% 11.92/2.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
% 11.92/2.00      inference(cnf_transformation,[],[f49]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(c_11,plain,
% 11.92/2.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.92/2.00      inference(cnf_transformation,[],[f38]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(c_169,plain,
% 11.92/2.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.92/2.00      inference(light_normalisation,[status(thm)],[c_7,c_11]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(c_0,plain,
% 11.92/2.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.92/2.00      inference(cnf_transformation,[],[f26]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(c_381,plain,
% 11.92/2.00      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 11.92/2.00      inference(superposition,[status(thm)],[c_0,c_11]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(c_486,plain,
% 11.92/2.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X1 ),
% 11.92/2.00      inference(light_normalisation,[status(thm)],[c_481,c_169,c_381]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(c_10,plain,
% 11.92/2.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.92/2.00      inference(cnf_transformation,[],[f37]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(c_1095,plain,
% 11.92/2.00      ( k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X1,X2) ),
% 11.92/2.00      inference(superposition,[status(thm)],[c_486,c_10]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(c_16,negated_conjecture,
% 11.92/2.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.92/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(c_266,plain,
% 11.92/2.00      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.92/2.00      inference(demodulation,[status(thm)],[c_0,c_16]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(c_50223,plain,
% 11.92/2.00      ( k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k2_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.92/2.00      inference(demodulation,[status(thm)],[c_1095,c_266]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(c_6,plain,
% 11.92/2.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.92/2.00      inference(cnf_transformation,[],[f33]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(c_15,plain,
% 11.92/2.00      ( k2_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
% 11.92/2.00      inference(cnf_transformation,[],[f54]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(c_1266,plain,
% 11.92/2.00      ( k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)),k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.92/2.00      inference(superposition,[status(thm)],[c_15,c_11]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(c_50224,plain,
% 11.92/2.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.92/2.00      inference(demodulation,[status(thm)],[c_50223,c_6,c_1266]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(c_421,plain,
% 11.92/2.00      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
% 11.92/2.00      inference(instantiation,[status(thm)],[c_1]) ).
% 11.92/2.00  
% 11.92/2.00  cnf(contradiction,plain,
% 11.92/2.00      ( $false ),
% 11.92/2.00      inference(minisat,[status(thm)],[c_50224,c_421]) ).
% 11.92/2.00  
% 11.92/2.00  
% 11.92/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.92/2.00  
% 11.92/2.00  ------                               Statistics
% 11.92/2.00  
% 11.92/2.00  ------ General
% 11.92/2.00  
% 11.92/2.00  abstr_ref_over_cycles:                  0
% 11.92/2.00  abstr_ref_under_cycles:                 0
% 11.92/2.00  gc_basic_clause_elim:                   0
% 11.92/2.00  forced_gc_time:                         0
% 11.92/2.00  parsing_time:                           0.008
% 11.92/2.00  unif_index_cands_time:                  0.
% 11.92/2.00  unif_index_add_time:                    0.
% 11.92/2.00  orderings_time:                         0.
% 11.92/2.00  out_proof_time:                         0.008
% 11.92/2.00  total_time:                             1.487
% 11.92/2.00  num_of_symbols:                         40
% 11.92/2.00  num_of_terms:                           75486
% 11.92/2.00  
% 11.92/2.00  ------ Preprocessing
% 11.92/2.00  
% 11.92/2.00  num_of_splits:                          0
% 11.92/2.00  num_of_split_atoms:                     2
% 11.92/2.00  num_of_reused_defs:                     0
% 11.92/2.00  num_eq_ax_congr_red:                    1
% 11.92/2.00  num_of_sem_filtered_clauses:            1
% 11.92/2.00  num_of_subtypes:                        0
% 11.92/2.00  monotx_restored_types:                  0
% 11.92/2.00  sat_num_of_epr_types:                   0
% 11.92/2.00  sat_num_of_non_cyclic_types:            0
% 11.92/2.00  sat_guarded_non_collapsed_types:        0
% 11.92/2.00  num_pure_diseq_elim:                    0
% 11.92/2.00  simp_replaced_by:                       0
% 11.92/2.00  res_preprocessed:                       76
% 11.92/2.00  prep_upred:                             0
% 11.92/2.00  prep_unflattend:                        6
% 11.92/2.00  smt_new_axioms:                         0
% 11.92/2.00  pred_elim_cands:                        1
% 11.92/2.00  pred_elim:                              1
% 11.92/2.00  pred_elim_cl:                           1
% 11.92/2.00  pred_elim_cycles:                       4
% 11.92/2.00  merged_defs:                            0
% 11.92/2.00  merged_defs_ncl:                        0
% 11.92/2.00  bin_hyper_res:                          0
% 11.92/2.00  prep_cycles:                            4
% 11.92/2.00  pred_elim_time:                         0.
% 11.92/2.00  splitting_time:                         0.
% 11.92/2.00  sem_filter_time:                        0.
% 11.92/2.00  monotx_time:                            0.
% 11.92/2.00  subtype_inf_time:                       0.
% 11.92/2.00  
% 11.92/2.00  ------ Problem properties
% 11.92/2.00  
% 11.92/2.00  clauses:                                16
% 11.92/2.00  conjectures:                            1
% 11.92/2.00  epr:                                    0
% 11.92/2.00  horn:                                   16
% 11.92/2.00  ground:                                 1
% 11.92/2.00  unary:                                  15
% 11.92/2.00  binary:                                 1
% 11.92/2.00  lits:                                   17
% 11.92/2.00  lits_eq:                                15
% 11.92/2.00  fd_pure:                                0
% 11.92/2.00  fd_pseudo:                              0
% 11.92/2.00  fd_cond:                                0
% 11.92/2.00  fd_pseudo_cond:                         0
% 11.92/2.00  ac_symbols:                             0
% 11.92/2.00  
% 11.92/2.00  ------ Propositional Solver
% 11.92/2.00  
% 11.92/2.00  prop_solver_calls:                      34
% 11.92/2.00  prop_fast_solver_calls:                 411
% 11.92/2.00  smt_solver_calls:                       0
% 11.92/2.00  smt_fast_solver_calls:                  0
% 11.92/2.00  prop_num_of_clauses:                    10767
% 11.92/2.00  prop_preprocess_simplified:             10426
% 11.92/2.00  prop_fo_subsumed:                       0
% 11.92/2.00  prop_solver_time:                       0.
% 11.92/2.00  smt_solver_time:                        0.
% 11.92/2.00  smt_fast_solver_time:                   0.
% 11.92/2.00  prop_fast_solver_time:                  0.
% 11.92/2.00  prop_unsat_core_time:                   0.001
% 11.92/2.00  
% 11.92/2.00  ------ QBF
% 11.92/2.00  
% 11.92/2.00  qbf_q_res:                              0
% 11.92/2.00  qbf_num_tautologies:                    0
% 11.92/2.00  qbf_prep_cycles:                        0
% 11.92/2.00  
% 11.92/2.00  ------ BMC1
% 11.92/2.00  
% 11.92/2.00  bmc1_current_bound:                     -1
% 11.92/2.00  bmc1_last_solved_bound:                 -1
% 11.92/2.00  bmc1_unsat_core_size:                   -1
% 11.92/2.00  bmc1_unsat_core_parents_size:           -1
% 11.92/2.00  bmc1_merge_next_fun:                    0
% 11.92/2.00  bmc1_unsat_core_clauses_time:           0.
% 11.92/2.00  
% 11.92/2.00  ------ Instantiation
% 11.92/2.00  
% 11.92/2.00  inst_num_of_clauses:                    2643
% 11.92/2.00  inst_num_in_passive:                    725
% 11.92/2.00  inst_num_in_active:                     741
% 11.92/2.00  inst_num_in_unprocessed:                1177
% 11.92/2.00  inst_num_of_loops:                      920
% 11.92/2.00  inst_num_of_learning_restarts:          0
% 11.92/2.00  inst_num_moves_active_passive:          175
% 11.92/2.00  inst_lit_activity:                      0
% 11.92/2.00  inst_lit_activity_moves:                1
% 11.92/2.00  inst_num_tautologies:                   0
% 11.92/2.00  inst_num_prop_implied:                  0
% 11.92/2.00  inst_num_existing_simplified:           0
% 11.92/2.00  inst_num_eq_res_simplified:             0
% 11.92/2.00  inst_num_child_elim:                    0
% 11.92/2.00  inst_num_of_dismatching_blockings:      1214
% 11.92/2.00  inst_num_of_non_proper_insts:           3329
% 11.92/2.00  inst_num_of_duplicates:                 0
% 11.92/2.00  inst_inst_num_from_inst_to_res:         0
% 11.92/2.00  inst_dismatching_checking_time:         0.
% 11.92/2.00  
% 11.92/2.00  ------ Resolution
% 11.92/2.00  
% 11.92/2.00  res_num_of_clauses:                     0
% 11.92/2.00  res_num_in_passive:                     0
% 11.92/2.00  res_num_in_active:                      0
% 11.92/2.00  res_num_of_loops:                       80
% 11.92/2.00  res_forward_subset_subsumed:            758
% 11.92/2.00  res_backward_subset_subsumed:           4
% 11.92/2.00  res_forward_subsumed:                   0
% 11.92/2.00  res_backward_subsumed:                  0
% 11.92/2.00  res_forward_subsumption_resolution:     0
% 11.92/2.00  res_backward_subsumption_resolution:    0
% 11.92/2.00  res_clause_to_clause_subsumption:       80337
% 11.92/2.00  res_orphan_elimination:                 0
% 11.92/2.00  res_tautology_del:                      498
% 11.92/2.00  res_num_eq_res_simplified:              0
% 11.92/2.00  res_num_sel_changes:                    0
% 11.92/2.00  res_moves_from_active_to_pass:          0
% 11.92/2.00  
% 11.92/2.00  ------ Superposition
% 11.92/2.00  
% 11.92/2.00  sup_time_total:                         0.
% 11.92/2.00  sup_time_generating:                    0.
% 11.92/2.00  sup_time_sim_full:                      0.
% 11.92/2.00  sup_time_sim_immed:                     0.
% 11.92/2.00  
% 11.92/2.00  sup_num_of_clauses:                     3408
% 11.92/2.00  sup_num_in_active:                      154
% 11.92/2.00  sup_num_in_passive:                     3254
% 11.92/2.00  sup_num_of_loops:                       183
% 11.92/2.00  sup_fw_superposition:                   14188
% 11.92/2.00  sup_bw_superposition:                   10521
% 11.92/2.00  sup_immediate_simplified:               11645
% 11.92/2.00  sup_given_eliminated:                   4
% 11.92/2.00  comparisons_done:                       0
% 11.92/2.00  comparisons_avoided:                    0
% 11.92/2.00  
% 11.92/2.00  ------ Simplifications
% 11.92/2.00  
% 11.92/2.00  
% 11.92/2.00  sim_fw_subset_subsumed:                 0
% 11.92/2.00  sim_bw_subset_subsumed:                 0
% 11.92/2.00  sim_fw_subsumed:                        2114
% 11.92/2.00  sim_bw_subsumed:                        54
% 11.92/2.00  sim_fw_subsumption_res:                 0
% 11.92/2.00  sim_bw_subsumption_res:                 0
% 11.92/2.00  sim_tautology_del:                      0
% 11.92/2.00  sim_eq_tautology_del:                   3034
% 11.92/2.00  sim_eq_res_simp:                        0
% 11.92/2.00  sim_fw_demodulated:                     7637
% 11.92/2.00  sim_bw_demodulated:                     87
% 11.92/2.00  sim_light_normalised:                   4723
% 11.92/2.00  sim_joinable_taut:                      0
% 11.92/2.00  sim_joinable_simp:                      0
% 11.92/2.00  sim_ac_normalised:                      0
% 11.92/2.00  sim_smt_subsumption:                    0
% 11.92/2.00  
%------------------------------------------------------------------------------
