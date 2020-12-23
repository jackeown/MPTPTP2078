%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:58:37 EST 2020

% Result     : Theorem 0.54s
% Output     : CNFRefutation 0.54s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----WARNING: Could not form TPTP format derivation
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.54/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.54/0.99  
% 0.54/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.54/0.99  
% 0.54/0.99  ------  iProver source info
% 0.54/0.99  
% 0.54/0.99  git: date: 2020-06-30 10:37:57 +0100
% 0.54/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.54/0.99  git: non_committed_changes: false
% 0.54/0.99  git: last_make_outside_of_git: false
% 0.54/0.99  
% 0.54/0.99  ------ 
% 0.54/0.99  
% 0.54/0.99  ------ Input Options
% 0.54/0.99  
% 0.54/0.99  --out_options                           all
% 0.54/0.99  --tptp_safe_out                         true
% 0.54/0.99  --problem_path                          ""
% 0.54/0.99  --include_path                          ""
% 0.54/0.99  --clausifier                            res/vclausify_rel
% 0.54/0.99  --clausifier_options                    --mode clausify
% 0.54/0.99  --stdin                                 false
% 0.54/0.99  --stats_out                             all
% 0.54/0.99  
% 0.54/0.99  ------ General Options
% 0.54/0.99  
% 0.54/0.99  --fof                                   false
% 0.54/0.99  --time_out_real                         305.
% 0.54/0.99  --time_out_virtual                      -1.
% 0.54/0.99  --symbol_type_check                     false
% 0.54/0.99  --clausify_out                          false
% 0.54/0.99  --sig_cnt_out                           false
% 0.54/0.99  --trig_cnt_out                          false
% 0.54/0.99  --trig_cnt_out_tolerance                1.
% 0.54/0.99  --trig_cnt_out_sk_spl                   false
% 0.54/0.99  --abstr_cl_out                          false
% 0.54/0.99  
% 0.54/0.99  ------ Global Options
% 0.54/0.99  
% 0.54/0.99  --schedule                              default
% 0.54/0.99  --add_important_lit                     false
% 0.54/0.99  --prop_solver_per_cl                    1000
% 0.54/0.99  --min_unsat_core                        false
% 0.54/0.99  --soft_assumptions                      false
% 0.54/0.99  --soft_lemma_size                       3
% 0.54/0.99  --prop_impl_unit_size                   0
% 0.54/0.99  --prop_impl_unit                        []
% 0.54/0.99  --share_sel_clauses                     true
% 0.54/0.99  --reset_solvers                         false
% 0.54/0.99  --bc_imp_inh                            [conj_cone]
% 0.54/0.99  --conj_cone_tolerance                   3.
% 0.54/0.99  --extra_neg_conj                        none
% 0.54/0.99  --large_theory_mode                     true
% 0.54/0.99  --prolific_symb_bound                   200
% 0.54/0.99  --lt_threshold                          2000
% 0.54/0.99  --clause_weak_htbl                      true
% 0.54/0.99  --gc_record_bc_elim                     false
% 0.54/0.99  
% 0.54/0.99  ------ Preprocessing Options
% 0.54/0.99  
% 0.54/0.99  --preprocessing_flag                    true
% 0.54/0.99  --time_out_prep_mult                    0.1
% 0.54/0.99  --splitting_mode                        input
% 0.54/0.99  --splitting_grd                         true
% 0.54/0.99  --splitting_cvd                         false
% 0.54/0.99  --splitting_cvd_svl                     false
% 0.54/0.99  --splitting_nvd                         32
% 0.54/0.99  --sub_typing                            true
% 0.54/0.99  --prep_gs_sim                           true
% 0.54/0.99  --prep_unflatten                        true
% 0.54/0.99  --prep_res_sim                          true
% 0.54/0.99  --prep_upred                            true
% 0.54/0.99  --prep_sem_filter                       exhaustive
% 0.54/0.99  --prep_sem_filter_out                   false
% 0.54/0.99  --pred_elim                             true
% 0.54/0.99  --res_sim_input                         true
% 0.54/0.99  --eq_ax_congr_red                       true
% 0.54/0.99  --pure_diseq_elim                       true
% 0.54/0.99  --brand_transform                       false
% 0.54/0.99  --non_eq_to_eq                          false
% 0.54/0.99  --prep_def_merge                        true
% 0.54/0.99  --prep_def_merge_prop_impl              false
% 0.54/0.99  --prep_def_merge_mbd                    true
% 0.54/0.99  --prep_def_merge_tr_red                 false
% 0.54/0.99  --prep_def_merge_tr_cl                  false
% 0.54/0.99  --smt_preprocessing                     true
% 0.54/0.99  --smt_ac_axioms                         fast
% 0.54/0.99  --preprocessed_out                      false
% 0.54/0.99  --preprocessed_stats                    false
% 0.54/0.99  
% 0.54/0.99  ------ Abstraction refinement Options
% 0.54/0.99  
% 0.54/0.99  --abstr_ref                             []
% 0.54/0.99  --abstr_ref_prep                        false
% 0.54/0.99  --abstr_ref_until_sat                   false
% 0.54/0.99  --abstr_ref_sig_restrict                funpre
% 0.54/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.54/0.99  --abstr_ref_under                       []
% 0.54/0.99  
% 0.54/0.99  ------ SAT Options
% 0.54/0.99  
% 0.54/0.99  --sat_mode                              false
% 0.54/0.99  --sat_fm_restart_options                ""
% 0.54/0.99  --sat_gr_def                            false
% 0.54/0.99  --sat_epr_types                         true
% 0.54/0.99  --sat_non_cyclic_types                  false
% 0.54/0.99  --sat_finite_models                     false
% 0.54/0.99  --sat_fm_lemmas                         false
% 0.54/0.99  --sat_fm_prep                           false
% 0.54/0.99  --sat_fm_uc_incr                        true
% 0.54/0.99  --sat_out_model                         small
% 0.54/0.99  --sat_out_clauses                       false
% 0.54/0.99  
% 0.54/0.99  ------ QBF Options
% 0.54/0.99  
% 0.54/0.99  --qbf_mode                              false
% 0.54/0.99  --qbf_elim_univ                         false
% 0.54/0.99  --qbf_dom_inst                          none
% 0.54/0.99  --qbf_dom_pre_inst                      false
% 0.54/0.99  --qbf_sk_in                             false
% 0.54/0.99  --qbf_pred_elim                         true
% 0.54/0.99  --qbf_split                             512
% 0.54/0.99  
% 0.54/0.99  ------ BMC1 Options
% 0.54/0.99  
% 0.54/0.99  --bmc1_incremental                      false
% 0.54/0.99  --bmc1_axioms                           reachable_all
% 0.54/0.99  --bmc1_min_bound                        0
% 0.54/0.99  --bmc1_max_bound                        -1
% 0.54/0.99  --bmc1_max_bound_default                -1
% 0.54/0.99  --bmc1_symbol_reachability              true
% 0.54/0.99  --bmc1_property_lemmas                  false
% 0.54/0.99  --bmc1_k_induction                      false
% 0.54/0.99  --bmc1_non_equiv_states                 false
% 0.54/0.99  --bmc1_deadlock                         false
% 0.54/0.99  --bmc1_ucm                              false
% 0.54/0.99  --bmc1_add_unsat_core                   none
% 0.54/0.99  --bmc1_unsat_core_children              false
% 0.54/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.54/0.99  --bmc1_out_stat                         full
% 0.54/0.99  --bmc1_ground_init                      false
% 0.54/0.99  --bmc1_pre_inst_next_state              false
% 0.54/0.99  --bmc1_pre_inst_state                   false
% 0.54/0.99  --bmc1_pre_inst_reach_state             false
% 0.54/0.99  --bmc1_out_unsat_core                   false
% 0.54/0.99  --bmc1_aig_witness_out                  false
% 0.54/0.99  --bmc1_verbose                          false
% 0.54/0.99  --bmc1_dump_clauses_tptp                false
% 0.54/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.54/0.99  --bmc1_dump_file                        -
% 0.54/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.54/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.54/0.99  --bmc1_ucm_extend_mode                  1
% 0.54/0.99  --bmc1_ucm_init_mode                    2
% 0.54/0.99  --bmc1_ucm_cone_mode                    none
% 0.54/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.54/0.99  --bmc1_ucm_relax_model                  4
% 0.54/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.54/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.54/0.99  --bmc1_ucm_layered_model                none
% 0.54/0.99  --bmc1_ucm_max_lemma_size               10
% 0.54/0.99  
% 0.54/0.99  ------ AIG Options
% 0.54/0.99  
% 0.54/0.99  --aig_mode                              false
% 0.54/0.99  
% 0.54/0.99  ------ Instantiation Options
% 0.54/0.99  
% 0.54/0.99  --instantiation_flag                    true
% 0.54/0.99  --inst_sos_flag                         false
% 0.54/0.99  --inst_sos_phase                        true
% 0.54/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.54/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.54/0.99  --inst_lit_sel_side                     num_symb
% 0.54/0.99  --inst_solver_per_active                1400
% 0.54/0.99  --inst_solver_calls_frac                1.
% 0.54/0.99  --inst_passive_queue_type               priority_queues
% 0.54/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.54/0.99  --inst_passive_queues_freq              [25;2]
% 0.54/0.99  --inst_dismatching                      true
% 0.54/0.99  --inst_eager_unprocessed_to_passive     true
% 0.54/0.99  --inst_prop_sim_given                   true
% 0.54/0.99  --inst_prop_sim_new                     false
% 0.54/0.99  --inst_subs_new                         false
% 0.54/0.99  --inst_eq_res_simp                      false
% 0.54/0.99  --inst_subs_given                       false
% 0.54/0.99  --inst_orphan_elimination               true
% 0.54/0.99  --inst_learning_loop_flag               true
% 0.54/0.99  --inst_learning_start                   3000
% 0.54/0.99  --inst_learning_factor                  2
% 0.54/0.99  --inst_start_prop_sim_after_learn       3
% 0.54/0.99  --inst_sel_renew                        solver
% 0.54/0.99  --inst_lit_activity_flag                true
% 0.54/0.99  --inst_restr_to_given                   false
% 0.54/0.99  --inst_activity_threshold               500
% 0.54/0.99  --inst_out_proof                        true
% 0.54/0.99  
% 0.54/0.99  ------ Resolution Options
% 0.54/0.99  
% 0.54/0.99  --resolution_flag                       true
% 0.54/0.99  --res_lit_sel                           adaptive
% 0.54/0.99  --res_lit_sel_side                      none
% 0.54/0.99  --res_ordering                          kbo
% 0.54/0.99  --res_to_prop_solver                    active
% 0.54/0.99  --res_prop_simpl_new                    false
% 0.54/0.99  --res_prop_simpl_given                  true
% 0.54/0.99  --res_passive_queue_type                priority_queues
% 0.54/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.54/0.99  --res_passive_queues_freq               [15;5]
% 0.54/0.99  --res_forward_subs                      full
% 0.54/0.99  --res_backward_subs                     full
% 0.54/0.99  --res_forward_subs_resolution           true
% 0.54/0.99  --res_backward_subs_resolution          true
% 0.54/0.99  --res_orphan_elimination                true
% 0.54/0.99  --res_time_limit                        2.
% 0.54/0.99  --res_out_proof                         true
% 0.54/0.99  
% 0.54/0.99  ------ Superposition Options
% 0.54/0.99  
% 0.54/0.99  --superposition_flag                    true
% 0.54/0.99  --sup_passive_queue_type                priority_queues
% 0.54/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.54/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.54/0.99  --demod_completeness_check              fast
% 0.54/0.99  --demod_use_ground                      true
% 0.54/0.99  --sup_to_prop_solver                    passive
% 0.54/0.99  --sup_prop_simpl_new                    true
% 0.54/0.99  --sup_prop_simpl_given                  true
% 0.54/0.99  --sup_fun_splitting                     false
% 0.54/0.99  --sup_smt_interval                      50000
% 0.54/0.99  
% 0.54/0.99  ------ Superposition Simplification Setup
% 0.54/0.99  
% 0.54/0.99  --sup_indices_passive                   []
% 0.54/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.54/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.54/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.54/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.54/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.54/0.99  --sup_full_bw                           [BwDemod]
% 0.54/0.99  --sup_immed_triv                        [TrivRules]
% 0.54/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.54/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.54/0.99  --sup_immed_bw_main                     []
% 0.54/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.54/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.54/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.54/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.54/0.99  
% 0.54/0.99  ------ Combination Options
% 0.54/0.99  
% 0.54/0.99  --comb_res_mult                         3
% 0.54/0.99  --comb_sup_mult                         2
% 0.54/0.99  --comb_inst_mult                        10
% 0.54/0.99  
% 0.54/0.99  ------ Debug Options
% 0.54/0.99  
% 0.54/0.99  --dbg_backtrace                         false
% 0.54/0.99  --dbg_dump_prop_clauses                 false
% 0.54/0.99  --dbg_dump_prop_clauses_file            -
% 0.54/0.99  --dbg_out_stat                          false
% 0.54/0.99  ------ Parsing...
% 0.54/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.54/0.99  
% 0.54/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s 
% 0.54/0.99  
% 0.54/0.99  % SZS status Theorem for theBenchmark.p
% 0.54/0.99  
% 0.54/0.99   Resolution empty clause
% 0.54/0.99  
% 0.54/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 0.54/0.99  
% 0.54/0.99  fof(f3,conjecture,(
% 0.54/0.99    ! [X0,X1,X2,X3] : k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 0.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.54/0.99  
% 0.54/0.99  fof(f4,negated_conjecture,(
% 0.54/0.99    ~! [X0,X1,X2,X3] : k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 0.54/0.99    inference(negated_conjecture,[],[f3])).
% 0.54/0.99  
% 0.54/0.99  fof(f5,plain,(
% 0.54/0.99    ? [X0,X1,X2,X3] : k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) != k4_zfmisc_1(X0,X1,X2,X3)),
% 0.54/0.99    inference(ennf_transformation,[],[f4])).
% 0.54/0.99  
% 0.54/0.99  fof(f6,plain,(
% 0.54/0.99    ? [X0,X1,X2,X3] : k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) != k4_zfmisc_1(X0,X1,X2,X3) => k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3) != k4_zfmisc_1(sK0,sK1,sK2,sK3)),
% 0.54/0.99    introduced(choice_axiom,[])).
% 0.54/0.99  
% 0.54/0.99  fof(f7,plain,(
% 0.54/0.99    k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3) != k4_zfmisc_1(sK0,sK1,sK2,sK3)),
% 0.54/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f5,f6])).
% 0.54/0.99  
% 0.54/0.99  fof(f10,plain,(
% 0.54/0.99    k3_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2,sK3) != k4_zfmisc_1(sK0,sK1,sK2,sK3)),
% 0.54/0.99    inference(cnf_transformation,[],[f7])).
% 0.54/0.99  
% 0.54/0.99  fof(f2,axiom,(
% 0.54/0.99    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)),
% 0.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.54/0.99  
% 0.54/0.99  fof(f9,plain,(
% 0.54/0.99    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 0.54/0.99    inference(cnf_transformation,[],[f2])).
% 0.54/0.99  
% 0.54/0.99  fof(f1,axiom,(
% 0.54/0.99    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.54/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.54/0.99  
% 0.54/0.99  fof(f8,plain,(
% 0.54/0.99    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.54/0.99    inference(cnf_transformation,[],[f1])).
% 0.54/0.99  
% 0.54/0.99  fof(f11,plain,(
% 0.54/0.99    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) = k4_zfmisc_1(X0,X1,X2,X3)) )),
% 0.54/0.99    inference(definition_unfolding,[],[f9,f8])).
% 0.54/0.99  
% 0.54/0.99  fof(f12,plain,(
% 0.54/0.99    k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)),
% 0.54/0.99    inference(definition_unfolding,[],[f10,f8,f11])).
% 0.54/0.99  
% 0.54/0.99  cnf(c_0,negated_conjecture,
% 0.54/0.99      ( k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3) ),
% 0.54/0.99      inference(cnf_transformation,[],[f12]) ).
% 0.54/0.99  
% 0.54/0.99  cnf(c_1,plain,
% 0.54/0.99      ( iProver_spec_dis_eq_$i(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3),k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
% 0.54/0.99      inference(dis_equality_elim,[status(thm)],[c_0]) ).
% 0.54/0.99  
% 0.54/0.99  cnf(c_2,plain,( ~ iProver_spec_dis_eq_$i(X0,X0) ),theory(irreflexivity) ).
% 0.54/0.99  
% 0.54/0.99  cnf(c_17,plain,( $false ),inference(resolution,[status(thm)],[c_1,c_2]) ).
% 0.54/0.99  
% 0.54/0.99  
% 0.54/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 0.54/0.99  
% 0.54/0.99  ------                               Statistics
% 0.54/0.99  
% 0.54/0.99  ------ General
% 0.54/0.99  
% 0.54/0.99  abstr_ref_over_cycles:                  0
% 0.54/0.99  abstr_ref_under_cycles:                 0
% 0.54/0.99  gc_basic_clause_elim:                   0
% 0.54/0.99  forced_gc_time:                         0
% 0.54/0.99  parsing_time:                           0.008
% 0.54/0.99  unif_index_cands_time:                  0.
% 0.54/0.99  unif_index_add_time:                    0.
% 0.54/0.99  orderings_time:                         0.
% 0.54/0.99  out_proof_time:                         0.006
% 0.54/0.99  total_time:                             0.032
% 0.54/0.99  num_of_symbols:                         34
% 0.54/0.99  num_of_terms:                           36
% 0.54/0.99  
% 0.54/0.99  ------ Preprocessing
% 0.54/0.99  
% 0.54/0.99  num_of_splits:                          0
% 0.54/0.99  num_of_split_atoms:                     0
% 0.54/0.99  num_of_reused_defs:                     0
% 0.54/0.99  num_eq_ax_congr_red:                    0
% 0.54/0.99  num_of_sem_filtered_clauses:            0
% 0.54/0.99  num_of_subtypes:                        0
% 0.54/0.99  monotx_restored_types:                  0
% 0.54/0.99  sat_num_of_epr_types:                   0
% 0.54/0.99  sat_num_of_non_cyclic_types:            0
% 0.54/0.99  sat_guarded_non_collapsed_types:        0
% 0.54/0.99  num_pure_diseq_elim:                    1
% 0.54/0.99  simp_replaced_by:                       0
% 0.54/0.99  res_preprocessed:                       2
% 0.54/0.99  prep_upred:                             0
% 0.54/0.99  prep_unflattend:                        0
% 0.54/0.99  smt_new_axioms:                         0
% 0.54/0.99  pred_elim_cands:                        1
% 0.54/0.99  pred_elim:                              0
% 0.54/0.99  pred_elim_cl:                           0
% 0.54/0.99  pred_elim_cycles:                       0
% 0.54/0.99  merged_defs:                            0
% 0.54/0.99  merged_defs_ncl:                        0
% 0.54/0.99  bin_hyper_res:                          0
% 0.54/0.99  prep_cycles:                            1
% 0.54/0.99  pred_elim_time:                         0.
% 0.54/0.99  splitting_time:                         0.
% 0.54/0.99  sem_filter_time:                        0.
% 0.54/0.99  monotx_time:                            0.
% 0.54/0.99  subtype_inf_time:                       0.
% 0.54/0.99  
% 0.54/0.99  ------ Problem properties
% 0.54/0.99  
% 0.54/0.99  clauses:                                0
% 0.54/0.99  conjectures:                            0
% 0.54/0.99  epr:                                    0
% 0.54/0.99  horn:                                   0
% 0.54/0.99  ground:                                 0
% 0.54/0.99  unary:                                  0
% 0.54/0.99  binary:                                 0
% 0.54/0.99  lits:                                   0
% 0.54/0.99  lits_eq:                                0
% 0.54/0.99  fd_pure:                                0
% 0.54/0.99  fd_pseudo:                              0
% 0.54/0.99  fd_cond:                                0
% 0.54/0.99  fd_pseudo_cond:                         0
% 0.54/0.99  ac_symbols:                             undef
% 0.54/0.99  
% 0.54/0.99  ------ Propositional Solver
% 0.54/0.99  
% 0.54/0.99  prop_solver_calls:                      6
% 0.54/0.99  prop_fast_solver_calls:                 4
% 0.54/0.99  smt_solver_calls:                       0
% 0.54/0.99  smt_fast_solver_calls:                  0
% 0.54/0.99  prop_num_of_clauses:                    7
% 0.54/0.99  prop_preprocess_simplified:             31
% 0.54/0.99  prop_fo_subsumed:                       0
% 0.54/0.99  prop_solver_time:                       0.
% 0.54/0.99  smt_solver_time:                        0.
% 0.54/0.99  smt_fast_solver_time:                   0.
% 0.54/0.99  prop_fast_solver_time:                  0.
% 0.54/0.99  prop_unsat_core_time:                   0.
% 0.54/0.99  
% 0.54/0.99  ------ QBF
% 0.54/0.99  
% 0.54/0.99  qbf_q_res:                              0
% 0.54/0.99  qbf_num_tautologies:                    0
% 0.54/0.99  qbf_prep_cycles:                        0
% 0.54/0.99  
% 0.54/0.99  ------ BMC1
% 0.54/0.99  
% 0.54/0.99  bmc1_current_bound:                     -1
% 0.54/0.99  bmc1_last_solved_bound:                 -1
% 0.54/0.99  bmc1_unsat_core_size:                   -1
% 0.54/0.99  bmc1_unsat_core_parents_size:           -1
% 0.54/0.99  bmc1_merge_next_fun:                    0
% 0.54/0.99  bmc1_unsat_core_clauses_time:           0.
% 0.54/0.99  
% 0.54/0.99  ------ Instantiation
% 0.54/0.99  
% 0.54/0.99  inst_num_of_clauses:                    undef
% 0.54/0.99  inst_num_in_passive:                    undef
% 0.54/0.99  inst_num_in_active:                     0
% 0.54/0.99  inst_num_in_unprocessed:                0
% 0.54/0.99  inst_num_of_loops:                      0
% 0.54/0.99  inst_num_of_learning_restarts:          0
% 0.54/0.99  inst_num_moves_active_passive:          0
% 0.54/0.99  inst_lit_activity:                      0
% 0.54/0.99  inst_lit_activity_moves:                0
% 0.54/0.99  inst_num_tautologies:                   0
% 0.54/0.99  inst_num_prop_implied:                  0
% 0.54/0.99  inst_num_existing_simplified:           0
% 0.54/0.99  inst_num_eq_res_simplified:             0
% 0.54/0.99  inst_num_child_elim:                    0
% 0.54/0.99  inst_num_of_dismatching_blockings:      0
% 0.54/0.99  inst_num_of_non_proper_insts:           0
% 0.54/0.99  inst_num_of_duplicates:                 0
% 0.54/0.99  inst_inst_num_from_inst_to_res:         0
% 0.54/0.99  inst_dismatching_checking_time:         0.
% 0.54/0.99  
% 0.54/0.99  ------ Resolution
% 0.54/0.99  
% 0.54/0.99  res_num_of_clauses:                     2
% 0.54/0.99  res_num_in_passive:                     0
% 0.54/0.99  res_num_in_active:                      0
% 0.54/0.99  res_num_of_loops:                       3
% 0.54/0.99  res_forward_subset_subsumed:            0
% 0.54/0.99  res_backward_subset_subsumed:           0
% 0.54/0.99  res_forward_subsumed:                   0
% 0.54/0.99  res_backward_subsumed:                  0
% 0.54/0.99  res_forward_subsumption_resolution:     0
% 0.54/0.99  res_backward_subsumption_resolution:    0
% 0.54/0.99  res_clause_to_clause_subsumption:       0
% 0.54/0.99  res_orphan_elimination:                 0
% 0.54/0.99  res_tautology_del:                      0
% 0.54/0.99  res_num_eq_res_simplified:              0
% 0.54/0.99  res_num_sel_changes:                    0
% 0.54/0.99  res_moves_from_active_to_pass:          0
% 0.54/0.99  
% 0.54/0.99  ------ Superposition
% 0.54/0.99  
% 0.54/0.99  sup_time_total:                         0.
% 0.54/0.99  sup_time_generating:                    0.
% 0.54/0.99  sup_time_sim_full:                      0.
% 0.54/0.99  sup_time_sim_immed:                     0.
% 0.54/0.99  
% 0.54/0.99  sup_num_of_clauses:                     undef
% 0.54/0.99  sup_num_in_active:                      undef
% 0.54/0.99  sup_num_in_passive:                     undef
% 0.54/0.99  sup_num_of_loops:                       0
% 0.54/0.99  sup_fw_superposition:                   0
% 0.54/0.99  sup_bw_superposition:                   0
% 0.54/0.99  sup_immediate_simplified:               0
% 0.54/0.99  sup_given_eliminated:                   0
% 0.54/0.99  comparisons_done:                       0
% 0.54/0.99  comparisons_avoided:                    0
% 0.54/0.99  
% 0.54/0.99  ------ Simplifications
% 0.54/0.99  
% 0.54/0.99  
% 0.54/0.99  sim_fw_subset_subsumed:                 0
% 0.54/0.99  sim_bw_subset_subsumed:                 0
% 0.54/0.99  sim_fw_subsumed:                        0
% 0.54/0.99  sim_bw_subsumed:                        0
% 0.54/0.99  sim_fw_subsumption_res:                 0
% 0.54/0.99  sim_bw_subsumption_res:                 0
% 0.54/0.99  sim_tautology_del:                      0
% 0.54/0.99  sim_eq_tautology_del:                   0
% 0.54/0.99  sim_eq_res_simp:                        0
% 0.54/0.99  sim_fw_demodulated:                     0
% 0.54/0.99  sim_bw_demodulated:                     0
% 0.54/0.99  sim_light_normalised:                   0
% 0.54/0.99  sim_joinable_taut:                      0
% 0.54/0.99  sim_joinable_simp:                      0
% 0.54/0.99  sim_ac_normalised:                      0
% 0.54/0.99  sim_smt_subsumption:                    0
% 0.54/0.99  
%------------------------------------------------------------------------------
