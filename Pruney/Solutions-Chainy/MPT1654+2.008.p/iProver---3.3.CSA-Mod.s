%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:57 EST 2020

% Result     : CounterSatisfiable 1.70s
% Output     : Model 1.70s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----WARNING: Could not form TPTP format derivation
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:57:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.70/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/0.92  
% 1.70/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.70/0.92  
% 1.70/0.92  ------  iProver source info
% 1.70/0.92  
% 1.70/0.92  git: date: 2020-06-30 10:37:57 +0100
% 1.70/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.70/0.92  git: non_committed_changes: false
% 1.70/0.92  git: last_make_outside_of_git: false
% 1.70/0.92  
% 1.70/0.92  ------ 
% 1.70/0.92  
% 1.70/0.92  ------ Input Options
% 1.70/0.92  
% 1.70/0.92  --out_options                           all
% 1.70/0.92  --tptp_safe_out                         true
% 1.70/0.92  --problem_path                          ""
% 1.70/0.92  --include_path                          ""
% 1.70/0.92  --clausifier                            res/vclausify_rel
% 1.70/0.92  --clausifier_options                    --mode clausify
% 1.70/0.92  --stdin                                 false
% 1.70/0.92  --stats_out                             all
% 1.70/0.92  
% 1.70/0.92  ------ General Options
% 1.70/0.92  
% 1.70/0.92  --fof                                   false
% 1.70/0.92  --time_out_real                         305.
% 1.70/0.92  --time_out_virtual                      -1.
% 1.70/0.92  --symbol_type_check                     false
% 1.70/0.92  --clausify_out                          false
% 1.70/0.92  --sig_cnt_out                           false
% 1.70/0.92  --trig_cnt_out                          false
% 1.70/0.92  --trig_cnt_out_tolerance                1.
% 1.70/0.92  --trig_cnt_out_sk_spl                   false
% 1.70/0.92  --abstr_cl_out                          false
% 1.70/0.92  
% 1.70/0.92  ------ Global Options
% 1.70/0.92  
% 1.70/0.92  --schedule                              default
% 1.70/0.92  --add_important_lit                     false
% 1.70/0.92  --prop_solver_per_cl                    1000
% 1.70/0.92  --min_unsat_core                        false
% 1.70/0.92  --soft_assumptions                      false
% 1.70/0.92  --soft_lemma_size                       3
% 1.70/0.92  --prop_impl_unit_size                   0
% 1.70/0.92  --prop_impl_unit                        []
% 1.70/0.92  --share_sel_clauses                     true
% 1.70/0.92  --reset_solvers                         false
% 1.70/0.92  --bc_imp_inh                            [conj_cone]
% 1.70/0.92  --conj_cone_tolerance                   3.
% 1.70/0.92  --extra_neg_conj                        none
% 1.70/0.92  --large_theory_mode                     true
% 1.70/0.92  --prolific_symb_bound                   200
% 1.70/0.92  --lt_threshold                          2000
% 1.70/0.92  --clause_weak_htbl                      true
% 1.70/0.92  --gc_record_bc_elim                     false
% 1.70/0.92  
% 1.70/0.92  ------ Preprocessing Options
% 1.70/0.92  
% 1.70/0.92  --preprocessing_flag                    true
% 1.70/0.92  --time_out_prep_mult                    0.1
% 1.70/0.92  --splitting_mode                        input
% 1.70/0.92  --splitting_grd                         true
% 1.70/0.92  --splitting_cvd                         false
% 1.70/0.92  --splitting_cvd_svl                     false
% 1.70/0.92  --splitting_nvd                         32
% 1.70/0.92  --sub_typing                            true
% 1.70/0.92  --prep_gs_sim                           true
% 1.70/0.92  --prep_unflatten                        true
% 1.70/0.92  --prep_res_sim                          true
% 1.70/0.92  --prep_upred                            true
% 1.70/0.92  --prep_sem_filter                       exhaustive
% 1.70/0.92  --prep_sem_filter_out                   false
% 1.70/0.92  --pred_elim                             true
% 1.70/0.92  --res_sim_input                         true
% 1.70/0.92  --eq_ax_congr_red                       true
% 1.70/0.92  --pure_diseq_elim                       true
% 1.70/0.92  --brand_transform                       false
% 1.70/0.92  --non_eq_to_eq                          false
% 1.70/0.92  --prep_def_merge                        true
% 1.70/0.92  --prep_def_merge_prop_impl              false
% 1.70/0.92  --prep_def_merge_mbd                    true
% 1.70/0.92  --prep_def_merge_tr_red                 false
% 1.70/0.92  --prep_def_merge_tr_cl                  false
% 1.70/0.92  --smt_preprocessing                     true
% 1.70/0.92  --smt_ac_axioms                         fast
% 1.70/0.92  --preprocessed_out                      false
% 1.70/0.92  --preprocessed_stats                    false
% 1.70/0.92  
% 1.70/0.92  ------ Abstraction refinement Options
% 1.70/0.92  
% 1.70/0.92  --abstr_ref                             []
% 1.70/0.92  --abstr_ref_prep                        false
% 1.70/0.92  --abstr_ref_until_sat                   false
% 1.70/0.92  --abstr_ref_sig_restrict                funpre
% 1.70/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 1.70/0.92  --abstr_ref_under                       []
% 1.70/0.92  
% 1.70/0.92  ------ SAT Options
% 1.70/0.92  
% 1.70/0.92  --sat_mode                              false
% 1.70/0.92  --sat_fm_restart_options                ""
% 1.70/0.92  --sat_gr_def                            false
% 1.70/0.92  --sat_epr_types                         true
% 1.70/0.92  --sat_non_cyclic_types                  false
% 1.70/0.92  --sat_finite_models                     false
% 1.70/0.92  --sat_fm_lemmas                         false
% 1.70/0.92  --sat_fm_prep                           false
% 1.70/0.92  --sat_fm_uc_incr                        true
% 1.70/0.92  --sat_out_model                         small
% 1.70/0.92  --sat_out_clauses                       false
% 1.70/0.92  
% 1.70/0.92  ------ QBF Options
% 1.70/0.92  
% 1.70/0.92  --qbf_mode                              false
% 1.70/0.92  --qbf_elim_univ                         false
% 1.70/0.92  --qbf_dom_inst                          none
% 1.70/0.92  --qbf_dom_pre_inst                      false
% 1.70/0.92  --qbf_sk_in                             false
% 1.70/0.92  --qbf_pred_elim                         true
% 1.70/0.92  --qbf_split                             512
% 1.70/0.92  
% 1.70/0.92  ------ BMC1 Options
% 1.70/0.92  
% 1.70/0.92  --bmc1_incremental                      false
% 1.70/0.92  --bmc1_axioms                           reachable_all
% 1.70/0.92  --bmc1_min_bound                        0
% 1.70/0.92  --bmc1_max_bound                        -1
% 1.70/0.92  --bmc1_max_bound_default                -1
% 1.70/0.92  --bmc1_symbol_reachability              true
% 1.70/0.92  --bmc1_property_lemmas                  false
% 1.70/0.92  --bmc1_k_induction                      false
% 1.70/0.92  --bmc1_non_equiv_states                 false
% 1.70/0.92  --bmc1_deadlock                         false
% 1.70/0.92  --bmc1_ucm                              false
% 1.70/0.92  --bmc1_add_unsat_core                   none
% 1.70/0.92  --bmc1_unsat_core_children              false
% 1.70/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 1.70/0.92  --bmc1_out_stat                         full
% 1.70/0.92  --bmc1_ground_init                      false
% 1.70/0.92  --bmc1_pre_inst_next_state              false
% 1.70/0.92  --bmc1_pre_inst_state                   false
% 1.70/0.92  --bmc1_pre_inst_reach_state             false
% 1.70/0.92  --bmc1_out_unsat_core                   false
% 1.70/0.92  --bmc1_aig_witness_out                  false
% 1.70/0.92  --bmc1_verbose                          false
% 1.70/0.92  --bmc1_dump_clauses_tptp                false
% 1.70/0.92  --bmc1_dump_unsat_core_tptp             false
% 1.70/0.92  --bmc1_dump_file                        -
% 1.70/0.92  --bmc1_ucm_expand_uc_limit              128
% 1.70/0.92  --bmc1_ucm_n_expand_iterations          6
% 1.70/0.92  --bmc1_ucm_extend_mode                  1
% 1.70/0.92  --bmc1_ucm_init_mode                    2
% 1.70/0.92  --bmc1_ucm_cone_mode                    none
% 1.70/0.92  --bmc1_ucm_reduced_relation_type        0
% 1.70/0.92  --bmc1_ucm_relax_model                  4
% 1.70/0.92  --bmc1_ucm_full_tr_after_sat            true
% 1.70/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 1.70/0.92  --bmc1_ucm_layered_model                none
% 1.70/0.92  --bmc1_ucm_max_lemma_size               10
% 1.70/0.92  
% 1.70/0.92  ------ AIG Options
% 1.70/0.92  
% 1.70/0.92  --aig_mode                              false
% 1.70/0.92  
% 1.70/0.92  ------ Instantiation Options
% 1.70/0.92  
% 1.70/0.92  --instantiation_flag                    true
% 1.70/0.92  --inst_sos_flag                         false
% 1.70/0.92  --inst_sos_phase                        true
% 1.70/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.70/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.70/0.92  --inst_lit_sel_side                     num_symb
% 1.70/0.92  --inst_solver_per_active                1400
% 1.70/0.92  --inst_solver_calls_frac                1.
% 1.70/0.92  --inst_passive_queue_type               priority_queues
% 1.70/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.70/0.92  --inst_passive_queues_freq              [25;2]
% 1.70/0.92  --inst_dismatching                      true
% 1.70/0.92  --inst_eager_unprocessed_to_passive     true
% 1.70/0.92  --inst_prop_sim_given                   true
% 1.70/0.92  --inst_prop_sim_new                     false
% 1.70/0.92  --inst_subs_new                         false
% 1.70/0.92  --inst_eq_res_simp                      false
% 1.70/0.92  --inst_subs_given                       false
% 1.70/0.92  --inst_orphan_elimination               true
% 1.70/0.92  --inst_learning_loop_flag               true
% 1.70/0.92  --inst_learning_start                   3000
% 1.70/0.92  --inst_learning_factor                  2
% 1.70/0.92  --inst_start_prop_sim_after_learn       3
% 1.70/0.92  --inst_sel_renew                        solver
% 1.70/0.92  --inst_lit_activity_flag                true
% 1.70/0.92  --inst_restr_to_given                   false
% 1.70/0.92  --inst_activity_threshold               500
% 1.70/0.92  --inst_out_proof                        true
% 1.70/0.92  
% 1.70/0.92  ------ Resolution Options
% 1.70/0.92  
% 1.70/0.92  --resolution_flag                       true
% 1.70/0.92  --res_lit_sel                           adaptive
% 1.70/0.92  --res_lit_sel_side                      none
% 1.70/0.92  --res_ordering                          kbo
% 1.70/0.92  --res_to_prop_solver                    active
% 1.70/0.92  --res_prop_simpl_new                    false
% 1.70/0.92  --res_prop_simpl_given                  true
% 1.70/0.92  --res_passive_queue_type                priority_queues
% 1.70/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.70/0.92  --res_passive_queues_freq               [15;5]
% 1.70/0.92  --res_forward_subs                      full
% 1.70/0.92  --res_backward_subs                     full
% 1.70/0.92  --res_forward_subs_resolution           true
% 1.70/0.92  --res_backward_subs_resolution          true
% 1.70/0.92  --res_orphan_elimination                true
% 1.70/0.92  --res_time_limit                        2.
% 1.70/0.92  --res_out_proof                         true
% 1.70/0.92  
% 1.70/0.92  ------ Superposition Options
% 1.70/0.92  
% 1.70/0.92  --superposition_flag                    true
% 1.70/0.92  --sup_passive_queue_type                priority_queues
% 1.70/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.70/0.92  --sup_passive_queues_freq               [8;1;4]
% 1.70/0.92  --demod_completeness_check              fast
% 1.70/0.92  --demod_use_ground                      true
% 1.70/0.92  --sup_to_prop_solver                    passive
% 1.70/0.92  --sup_prop_simpl_new                    true
% 1.70/0.92  --sup_prop_simpl_given                  true
% 1.70/0.92  --sup_fun_splitting                     false
% 1.70/0.92  --sup_smt_interval                      50000
% 1.70/0.92  
% 1.70/0.92  ------ Superposition Simplification Setup
% 1.70/0.92  
% 1.70/0.92  --sup_indices_passive                   []
% 1.70/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 1.70/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.92  --sup_full_bw                           [BwDemod]
% 1.70/0.92  --sup_immed_triv                        [TrivRules]
% 1.70/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.70/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.92  --sup_immed_bw_main                     []
% 1.70/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 1.70/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.92  
% 1.70/0.92  ------ Combination Options
% 1.70/0.92  
% 1.70/0.92  --comb_res_mult                         3
% 1.70/0.92  --comb_sup_mult                         2
% 1.70/0.92  --comb_inst_mult                        10
% 1.70/0.92  
% 1.70/0.92  ------ Debug Options
% 1.70/0.92  
% 1.70/0.92  --dbg_backtrace                         false
% 1.70/0.92  --dbg_dump_prop_clauses                 false
% 1.70/0.92  --dbg_dump_prop_clauses_file            -
% 1.70/0.92  --dbg_out_stat                          false
% 1.70/0.92  ------ Parsing...
% 1.70/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.70/0.92  
% 1.70/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.70/0.92  
% 1.70/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.70/0.92  
% 1.70/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.70/0.92  ------ Proving...
% 1.70/0.92  ------ Problem Properties 
% 1.70/0.92  
% 1.70/0.92  
% 1.70/0.92  clauses                                 17
% 1.70/0.92  conjectures                             2
% 1.70/0.92  EPR                                     0
% 1.70/0.92  Horn                                    11
% 1.70/0.92  unary                                   1
% 1.70/0.92  binary                                  4
% 1.70/0.92  lits                                    59
% 1.70/0.92  lits eq                                 4
% 1.70/0.92  fd_pure                                 0
% 1.70/0.92  fd_pseudo                               0
% 1.70/0.92  fd_cond                                 0
% 1.70/0.92  fd_pseudo_cond                          3
% 1.70/0.92  AC symbols                              0
% 1.70/0.92  
% 1.70/0.92  ------ Schedule dynamic 5 is on 
% 1.70/0.92  
% 1.70/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.70/0.92  
% 1.70/0.92  
% 1.70/0.92  ------ 
% 1.70/0.92  Current options:
% 1.70/0.92  ------ 
% 1.70/0.92  
% 1.70/0.92  ------ Input Options
% 1.70/0.92  
% 1.70/0.92  --out_options                           all
% 1.70/0.92  --tptp_safe_out                         true
% 1.70/0.92  --problem_path                          ""
% 1.70/0.92  --include_path                          ""
% 1.70/0.92  --clausifier                            res/vclausify_rel
% 1.70/0.92  --clausifier_options                    --mode clausify
% 1.70/0.92  --stdin                                 false
% 1.70/0.92  --stats_out                             all
% 1.70/0.92  
% 1.70/0.92  ------ General Options
% 1.70/0.92  
% 1.70/0.92  --fof                                   false
% 1.70/0.92  --time_out_real                         305.
% 1.70/0.92  --time_out_virtual                      -1.
% 1.70/0.92  --symbol_type_check                     false
% 1.70/0.92  --clausify_out                          false
% 1.70/0.92  --sig_cnt_out                           false
% 1.70/0.92  --trig_cnt_out                          false
% 1.70/0.92  --trig_cnt_out_tolerance                1.
% 1.70/0.92  --trig_cnt_out_sk_spl                   false
% 1.70/0.92  --abstr_cl_out                          false
% 1.70/0.92  
% 1.70/0.92  ------ Global Options
% 1.70/0.92  
% 1.70/0.92  --schedule                              default
% 1.70/0.92  --add_important_lit                     false
% 1.70/0.92  --prop_solver_per_cl                    1000
% 1.70/0.92  --min_unsat_core                        false
% 1.70/0.92  --soft_assumptions                      false
% 1.70/0.92  --soft_lemma_size                       3
% 1.70/0.92  --prop_impl_unit_size                   0
% 1.70/0.92  --prop_impl_unit                        []
% 1.70/0.92  --share_sel_clauses                     true
% 1.70/0.92  --reset_solvers                         false
% 1.70/0.92  --bc_imp_inh                            [conj_cone]
% 1.70/0.92  --conj_cone_tolerance                   3.
% 1.70/0.92  --extra_neg_conj                        none
% 1.70/0.92  --large_theory_mode                     true
% 1.70/0.92  --prolific_symb_bound                   200
% 1.70/0.92  --lt_threshold                          2000
% 1.70/0.92  --clause_weak_htbl                      true
% 1.70/0.92  --gc_record_bc_elim                     false
% 1.70/0.92  
% 1.70/0.92  ------ Preprocessing Options
% 1.70/0.92  
% 1.70/0.92  --preprocessing_flag                    true
% 1.70/0.92  --time_out_prep_mult                    0.1
% 1.70/0.92  --splitting_mode                        input
% 1.70/0.92  --splitting_grd                         true
% 1.70/0.92  --splitting_cvd                         false
% 1.70/0.92  --splitting_cvd_svl                     false
% 1.70/0.92  --splitting_nvd                         32
% 1.70/0.92  --sub_typing                            true
% 1.70/0.92  --prep_gs_sim                           true
% 1.70/0.92  --prep_unflatten                        true
% 1.70/0.92  --prep_res_sim                          true
% 1.70/0.92  --prep_upred                            true
% 1.70/0.92  --prep_sem_filter                       exhaustive
% 1.70/0.92  --prep_sem_filter_out                   false
% 1.70/0.92  --pred_elim                             true
% 1.70/0.92  --res_sim_input                         true
% 1.70/0.92  --eq_ax_congr_red                       true
% 1.70/0.92  --pure_diseq_elim                       true
% 1.70/0.92  --brand_transform                       false
% 1.70/0.92  --non_eq_to_eq                          false
% 1.70/0.92  --prep_def_merge                        true
% 1.70/0.92  --prep_def_merge_prop_impl              false
% 1.70/0.92  --prep_def_merge_mbd                    true
% 1.70/0.92  --prep_def_merge_tr_red                 false
% 1.70/0.92  --prep_def_merge_tr_cl                  false
% 1.70/0.92  --smt_preprocessing                     true
% 1.70/0.92  --smt_ac_axioms                         fast
% 1.70/0.92  --preprocessed_out                      false
% 1.70/0.92  --preprocessed_stats                    false
% 1.70/0.92  
% 1.70/0.92  ------ Abstraction refinement Options
% 1.70/0.92  
% 1.70/0.92  --abstr_ref                             []
% 1.70/0.92  --abstr_ref_prep                        false
% 1.70/0.92  --abstr_ref_until_sat                   false
% 1.70/0.92  --abstr_ref_sig_restrict                funpre
% 1.70/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 1.70/0.92  --abstr_ref_under                       []
% 1.70/0.92  
% 1.70/0.92  ------ SAT Options
% 1.70/0.92  
% 1.70/0.92  --sat_mode                              false
% 1.70/0.92  --sat_fm_restart_options                ""
% 1.70/0.92  --sat_gr_def                            false
% 1.70/0.92  --sat_epr_types                         true
% 1.70/0.92  --sat_non_cyclic_types                  false
% 1.70/0.92  --sat_finite_models                     false
% 1.70/0.92  --sat_fm_lemmas                         false
% 1.70/0.92  --sat_fm_prep                           false
% 1.70/0.92  --sat_fm_uc_incr                        true
% 1.70/0.92  --sat_out_model                         small
% 1.70/0.92  --sat_out_clauses                       false
% 1.70/0.92  
% 1.70/0.92  ------ QBF Options
% 1.70/0.92  
% 1.70/0.92  --qbf_mode                              false
% 1.70/0.92  --qbf_elim_univ                         false
% 1.70/0.92  --qbf_dom_inst                          none
% 1.70/0.92  --qbf_dom_pre_inst                      false
% 1.70/0.92  --qbf_sk_in                             false
% 1.70/0.92  --qbf_pred_elim                         true
% 1.70/0.92  --qbf_split                             512
% 1.70/0.92  
% 1.70/0.92  ------ BMC1 Options
% 1.70/0.92  
% 1.70/0.92  --bmc1_incremental                      false
% 1.70/0.92  --bmc1_axioms                           reachable_all
% 1.70/0.92  --bmc1_min_bound                        0
% 1.70/0.92  --bmc1_max_bound                        -1
% 1.70/0.92  --bmc1_max_bound_default                -1
% 1.70/0.92  --bmc1_symbol_reachability              true
% 1.70/0.92  --bmc1_property_lemmas                  false
% 1.70/0.92  --bmc1_k_induction                      false
% 1.70/0.92  --bmc1_non_equiv_states                 false
% 1.70/0.92  --bmc1_deadlock                         false
% 1.70/0.92  --bmc1_ucm                              false
% 1.70/0.92  --bmc1_add_unsat_core                   none
% 1.70/0.92  --bmc1_unsat_core_children              false
% 1.70/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 1.70/0.92  --bmc1_out_stat                         full
% 1.70/0.92  --bmc1_ground_init                      false
% 1.70/0.92  --bmc1_pre_inst_next_state              false
% 1.70/0.92  --bmc1_pre_inst_state                   false
% 1.70/0.92  --bmc1_pre_inst_reach_state             false
% 1.70/0.92  --bmc1_out_unsat_core                   false
% 1.70/0.92  --bmc1_aig_witness_out                  false
% 1.70/0.92  --bmc1_verbose                          false
% 1.70/0.92  --bmc1_dump_clauses_tptp                false
% 1.70/0.92  --bmc1_dump_unsat_core_tptp             false
% 1.70/0.92  --bmc1_dump_file                        -
% 1.70/0.92  --bmc1_ucm_expand_uc_limit              128
% 1.70/0.92  --bmc1_ucm_n_expand_iterations          6
% 1.70/0.92  --bmc1_ucm_extend_mode                  1
% 1.70/0.92  --bmc1_ucm_init_mode                    2
% 1.70/0.92  --bmc1_ucm_cone_mode                    none
% 1.70/0.92  --bmc1_ucm_reduced_relation_type        0
% 1.70/0.92  --bmc1_ucm_relax_model                  4
% 1.70/0.92  --bmc1_ucm_full_tr_after_sat            true
% 1.70/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 1.70/0.92  --bmc1_ucm_layered_model                none
% 1.70/0.92  --bmc1_ucm_max_lemma_size               10
% 1.70/0.92  
% 1.70/0.92  ------ AIG Options
% 1.70/0.92  
% 1.70/0.92  --aig_mode                              false
% 1.70/0.92  
% 1.70/0.92  ------ Instantiation Options
% 1.70/0.92  
% 1.70/0.92  --instantiation_flag                    true
% 1.70/0.92  --inst_sos_flag                         false
% 1.70/0.92  --inst_sos_phase                        true
% 1.70/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.70/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.70/0.92  --inst_lit_sel_side                     none
% 1.70/0.92  --inst_solver_per_active                1400
% 1.70/0.92  --inst_solver_calls_frac                1.
% 1.70/0.92  --inst_passive_queue_type               priority_queues
% 1.70/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.70/0.92  --inst_passive_queues_freq              [25;2]
% 1.70/0.92  --inst_dismatching                      true
% 1.70/0.92  --inst_eager_unprocessed_to_passive     true
% 1.70/0.92  --inst_prop_sim_given                   true
% 1.70/0.92  --inst_prop_sim_new                     false
% 1.70/0.92  --inst_subs_new                         false
% 1.70/0.92  --inst_eq_res_simp                      false
% 1.70/0.92  --inst_subs_given                       false
% 1.70/0.92  --inst_orphan_elimination               true
% 1.70/0.92  --inst_learning_loop_flag               true
% 1.70/0.92  --inst_learning_start                   3000
% 1.70/0.92  --inst_learning_factor                  2
% 1.70/0.92  --inst_start_prop_sim_after_learn       3
% 1.70/0.92  --inst_sel_renew                        solver
% 1.70/0.92  --inst_lit_activity_flag                true
% 1.70/0.92  --inst_restr_to_given                   false
% 1.70/0.92  --inst_activity_threshold               500
% 1.70/0.92  --inst_out_proof                        true
% 1.70/0.92  
% 1.70/0.92  ------ Resolution Options
% 1.70/0.92  
% 1.70/0.92  --resolution_flag                       false
% 1.70/0.92  --res_lit_sel                           adaptive
% 1.70/0.92  --res_lit_sel_side                      none
% 1.70/0.92  --res_ordering                          kbo
% 1.70/0.92  --res_to_prop_solver                    active
% 1.70/0.92  --res_prop_simpl_new                    false
% 1.70/0.92  --res_prop_simpl_given                  true
% 1.70/0.92  --res_passive_queue_type                priority_queues
% 1.70/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.70/0.92  --res_passive_queues_freq               [15;5]
% 1.70/0.92  --res_forward_subs                      full
% 1.70/0.92  --res_backward_subs                     full
% 1.70/0.92  --res_forward_subs_resolution           true
% 1.70/0.92  --res_backward_subs_resolution          true
% 1.70/0.92  --res_orphan_elimination                true
% 1.70/0.92  --res_time_limit                        2.
% 1.70/0.92  --res_out_proof                         true
% 1.70/0.92  
% 1.70/0.92  ------ Superposition Options
% 1.70/0.92  
% 1.70/0.92  --superposition_flag                    true
% 1.70/0.92  --sup_passive_queue_type                priority_queues
% 1.70/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.70/0.92  --sup_passive_queues_freq               [8;1;4]
% 1.70/0.92  --demod_completeness_check              fast
% 1.70/0.92  --demod_use_ground                      true
% 1.70/0.92  --sup_to_prop_solver                    passive
% 1.70/0.92  --sup_prop_simpl_new                    true
% 1.70/0.92  --sup_prop_simpl_given                  true
% 1.70/0.92  --sup_fun_splitting                     false
% 1.70/0.92  --sup_smt_interval                      50000
% 1.70/0.92  
% 1.70/0.92  ------ Superposition Simplification Setup
% 1.70/0.92  
% 1.70/0.92  --sup_indices_passive                   []
% 1.70/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 1.70/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.92  --sup_full_bw                           [BwDemod]
% 1.70/0.92  --sup_immed_triv                        [TrivRules]
% 1.70/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.70/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.92  --sup_immed_bw_main                     []
% 1.70/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 1.70/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.92  
% 1.70/0.92  ------ Combination Options
% 1.70/0.92  
% 1.70/0.92  --comb_res_mult                         3
% 1.70/0.92  --comb_sup_mult                         2
% 1.70/0.92  --comb_inst_mult                        10
% 1.70/0.92  
% 1.70/0.92  ------ Debug Options
% 1.70/0.92  
% 1.70/0.92  --dbg_backtrace                         false
% 1.70/0.92  --dbg_dump_prop_clauses                 false
% 1.70/0.92  --dbg_dump_prop_clauses_file            -
% 1.70/0.92  --dbg_out_stat                          false
% 1.70/0.92  
% 1.70/0.92  
% 1.70/0.92  
% 1.70/0.92  
% 1.70/0.92  ------ Proving...
% 1.70/0.92  
% 1.70/0.92  
% 1.70/0.92  % SZS status CounterSatisfiable for theBenchmark.p
% 1.70/0.92  
% 1.70/0.92  ------ Building Model...Done
% 1.70/0.92  
% 1.70/0.92  %------ The model is defined over ground terms (initial term algebra).
% 1.70/0.92  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 1.70/0.92  %------ where \phi is a formula over the term algebra.
% 1.70/0.92  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 1.70/0.92  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 1.70/0.92  %------ See help for --sat_out_model for different model outputs.
% 1.70/0.92  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 1.70/0.92  %------ where the first argument stands for the sort ($i in the unsorted case)
% 1.70/0.92  % SZS output start Model for theBenchmark.p
% 1.70/0.92  
% 1.70/0.92  %------ Negative definition of equality_sorted 
% 1.70/0.92  fof(lit_def,axiom,
% 1.70/0.92      (! [X0_0,X0_2,X1_2] : 
% 1.70/0.92        ( ~(equality_sorted(X0_0,X0_2,X1_2)) <=>
% 1.70/0.92             (
% 1.70/0.92              ? [X0_47,X2_48] : 
% 1.70/0.92                (
% 1.70/0.92                  ( X0_0=iProver_r1_orders_2_3_$i & X0_48=sK2(sK4,X0_47,X2_48) )
% 1.70/0.92                 &
% 1.70/0.92                  ( X0_47!=X0_47 | X1_48!=sK2(sK4,X0_47,X1_48) | X2_48!=X1_48 )
% 1.70/0.92                 &
% 1.70/0.92                  ( X0_47!=X0_47 | X1_48!=sK2(sK4,X0_47,X2_48) | X2_48!=X2_48 )
% 1.70/0.92                )
% 1.70/0.92  
% 1.70/0.92               | 
% 1.70/0.92              ? [X0_47] : 
% 1.70/0.92                (
% 1.70/0.92                  ( X0_0=iProver_r1_orders_2_3_$i & X1_48=sK2(sK4,X0_47,X0_48) )
% 1.70/0.92                )
% 1.70/0.92  
% 1.70/0.92               | 
% 1.70/0.92              ? [X0_47,X2_48] : 
% 1.70/0.92                (
% 1.70/0.92                  ( X0_0=iProver_r1_orders_2_3_$i & X1_48=sK2(sK4,X0_47,X2_48) )
% 1.70/0.92                 &
% 1.70/0.92                  ( X0_47!=X0_47 | X0_48!=sK2(sK4,X0_47,X0_48) | X2_48!=X0_48 )
% 1.70/0.92                )
% 1.70/0.92  
% 1.70/0.92             )
% 1.70/0.92        )
% 1.70/0.92      )
% 1.70/0.92     ).
% 1.70/0.92  
% 1.70/0.92  %------ Negative definition of r1_orders_2 
% 1.70/0.92  fof(lit_def,axiom,
% 1.70/0.92      (! [X0_46,X0_48,X1_48] : 
% 1.70/0.92        ( ~(r1_orders_2(X0_46,X0_48,X1_48)) <=>
% 1.70/0.92             (
% 1.70/0.92              ? [X0_47] : 
% 1.70/0.92                (
% 1.70/0.92                  ( X0_46=sK4 & X1_48=sK2(sK4,X0_47,X0_48) )
% 1.70/0.92                )
% 1.70/0.92  
% 1.70/0.92               | 
% 1.70/0.92              ? [X0_47,X2_48] : 
% 1.70/0.92                (
% 1.70/0.92                  ( X0_46=sK4 & X1_48=sK2(sK4,X0_47,X2_48) )
% 1.70/0.92                 &
% 1.70/0.92                  ( X0_47!=X0_47 | X0_48!=sK2(sK4,X0_47,X0_48) | X2_48!=X0_48 )
% 1.70/0.92                )
% 1.70/0.93  
% 1.70/0.93             )
% 1.70/0.93        )
% 1.70/0.93      )
% 1.70/0.93     ).
% 1.70/0.93  
% 1.70/0.93  %------ Positive definition of m1_subset_1 
% 1.70/0.93  fof(lit_def,axiom,
% 1.70/0.93      (! [X0_48,X0_49] : 
% 1.70/0.93        ( m1_subset_1(X0_48,X0_49) <=>
% 1.70/0.93             (
% 1.70/0.93                (
% 1.70/0.93                  ( X0_48=sK5 & X0_49=u1_struct_0(sK4) )
% 1.70/0.93                )
% 1.70/0.93  
% 1.70/0.93               | 
% 1.70/0.93              ? [X0_47,X1_48] : 
% 1.70/0.93                (
% 1.70/0.93                  ( X0_48=sK2(sK4,X0_47,X1_48) & X0_49=u1_struct_0(sK4) )
% 1.70/0.93                )
% 1.70/0.93  
% 1.70/0.93               | 
% 1.70/0.93                (
% 1.70/0.93                  ( X0_49=u1_struct_0(sK4) )
% 1.70/0.93                )
% 1.70/0.93  
% 1.70/0.93             )
% 1.70/0.93        )
% 1.70/0.93      )
% 1.70/0.93     ).
% 1.70/0.93  
% 1.70/0.93  %------ Positive definition of l1_orders_2 
% 1.70/0.93  fof(lit_def,axiom,
% 1.70/0.93      (! [X0] : 
% 1.70/0.93        ( l1_orders_2(X0) <=>
% 1.70/0.93            $false
% 1.70/0.93        )
% 1.70/0.93      )
% 1.70/0.93     ).
% 1.70/0.93  
% 1.70/0.93  %------ Positive definition of v3_orders_2 
% 1.70/0.93  fof(lit_def,axiom,
% 1.70/0.93      (! [X0] : 
% 1.70/0.93        ( v3_orders_2(X0) <=>
% 1.70/0.93            $false
% 1.70/0.93        )
% 1.70/0.93      )
% 1.70/0.93     ).
% 1.70/0.93  
% 1.70/0.93  %------ Positive definition of v2_struct_0 
% 1.70/0.93  fof(lit_def,axiom,
% 1.70/0.93      (! [X0] : 
% 1.70/0.93        ( v2_struct_0(X0) <=>
% 1.70/0.93            $false
% 1.70/0.93        )
% 1.70/0.93      )
% 1.70/0.93     ).
% 1.70/0.93  
% 1.70/0.93  %------ Positive definition of r2_lattice3 
% 1.70/0.93  fof(lit_def,axiom,
% 1.70/0.93      (! [X0_46,X0_47,X0_48] : 
% 1.70/0.93        ( r2_lattice3(X0_46,X0_47,X0_48) <=>
% 1.70/0.93            $true
% 1.70/0.93        )
% 1.70/0.93      )
% 1.70/0.93     ).
% 1.70/0.93  
% 1.70/0.93  %------ Positive definition of r2_hidden 
% 1.70/0.93  fof(lit_def,axiom,
% 1.70/0.93      (! [X0,X1] : 
% 1.70/0.93        ( r2_hidden(X0,X1) <=>
% 1.70/0.93            $false
% 1.70/0.93        )
% 1.70/0.93      )
% 1.70/0.93     ).
% 1.70/0.93  
% 1.70/0.93  %------ Positive definition of r1_yellow_0 
% 1.70/0.93  fof(lit_def,axiom,
% 1.70/0.93      (! [X0_46,X0_47] : 
% 1.70/0.93        ( r1_yellow_0(X0_46,X0_47) <=>
% 1.70/0.93            $false
% 1.70/0.93        )
% 1.70/0.93      )
% 1.70/0.93     ).
% 1.70/0.93  
% 1.70/0.93  %------ Positive definition of v5_orders_2 
% 1.70/0.93  fof(lit_def,axiom,
% 1.70/0.93      (! [X0] : 
% 1.70/0.93        ( v5_orders_2(X0) <=>
% 1.70/0.93            $false
% 1.70/0.93        )
% 1.70/0.93      )
% 1.70/0.93     ).
% 1.70/0.93  % SZS output end Model for theBenchmark.p
% 1.70/0.93  ------                               Statistics
% 1.70/0.93  
% 1.70/0.93  ------ General
% 1.70/0.93  
% 1.70/0.93  abstr_ref_over_cycles:                  0
% 1.70/0.93  abstr_ref_under_cycles:                 0
% 1.70/0.93  gc_basic_clause_elim:                   0
% 1.70/0.93  forced_gc_time:                         0
% 1.70/0.93  parsing_time:                           0.011
% 1.70/0.93  unif_index_cands_time:                  0.
% 1.70/0.93  unif_index_add_time:                    0.
% 1.70/0.93  orderings_time:                         0.
% 1.70/0.93  out_proof_time:                         0.
% 1.70/0.93  total_time:                             0.107
% 1.70/0.93  num_of_symbols:                         50
% 1.70/0.93  num_of_terms:                           1822
% 1.70/0.93  
% 1.70/0.93  ------ Preprocessing
% 1.70/0.93  
% 1.70/0.93  num_of_splits:                          0
% 1.70/0.93  num_of_split_atoms:                     0
% 1.70/0.93  num_of_reused_defs:                     0
% 1.70/0.93  num_eq_ax_congr_red:                    42
% 1.70/0.93  num_of_sem_filtered_clauses:            1
% 1.70/0.93  num_of_subtypes:                        4
% 1.70/0.93  monotx_restored_types:                  0
% 1.70/0.93  sat_num_of_epr_types:                   0
% 1.70/0.93  sat_num_of_non_cyclic_types:            0
% 1.70/0.93  sat_guarded_non_collapsed_types:        1
% 1.70/0.93  num_pure_diseq_elim:                    0
% 1.70/0.93  simp_replaced_by:                       0
% 1.70/0.93  res_preprocessed:                       92
% 1.70/0.93  prep_upred:                             0
% 1.70/0.93  prep_unflattend:                        62
% 1.70/0.93  smt_new_axioms:                         0
% 1.70/0.93  pred_elim_cands:                        4
% 1.70/0.93  pred_elim:                              5
% 1.70/0.93  pred_elim_cl:                           5
% 1.70/0.93  pred_elim_cycles:                       10
% 1.70/0.93  merged_defs:                            0
% 1.70/0.93  merged_defs_ncl:                        0
% 1.70/0.93  bin_hyper_res:                          0
% 1.70/0.93  prep_cycles:                            4
% 1.70/0.93  pred_elim_time:                         0.047
% 1.70/0.93  splitting_time:                         0.
% 1.70/0.93  sem_filter_time:                        0.
% 1.70/0.93  monotx_time:                            0.
% 1.70/0.93  subtype_inf_time:                       0.
% 1.70/0.93  
% 1.70/0.93  ------ Problem properties
% 1.70/0.93  
% 1.70/0.93  clauses:                                17
% 1.70/0.93  conjectures:                            2
% 1.70/0.93  epr:                                    0
% 1.70/0.93  horn:                                   11
% 1.70/0.93  ground:                                 2
% 1.70/0.93  unary:                                  1
% 1.70/0.93  binary:                                 4
% 1.70/0.93  lits:                                   59
% 1.70/0.93  lits_eq:                                4
% 1.70/0.93  fd_pure:                                0
% 1.70/0.93  fd_pseudo:                              0
% 1.70/0.93  fd_cond:                                0
% 1.70/0.93  fd_pseudo_cond:                         3
% 1.70/0.93  ac_symbols:                             0
% 1.70/0.93  
% 1.70/0.93  ------ Propositional Solver
% 1.70/0.93  
% 1.70/0.93  prop_solver_calls:                      24
% 1.70/0.93  prop_fast_solver_calls:                 1248
% 1.70/0.93  smt_solver_calls:                       0
% 1.70/0.93  smt_fast_solver_calls:                  0
% 1.70/0.93  prop_num_of_clauses:                    457
% 1.70/0.93  prop_preprocess_simplified:             3117
% 1.70/0.93  prop_fo_subsumed:                       18
% 1.70/0.93  prop_solver_time:                       0.
% 1.70/0.93  smt_solver_time:                        0.
% 1.70/0.93  smt_fast_solver_time:                   0.
% 1.70/0.93  prop_fast_solver_time:                  0.
% 1.70/0.93  prop_unsat_core_time:                   0.
% 1.70/0.93  
% 1.70/0.93  ------ QBF
% 1.70/0.93  
% 1.70/0.93  qbf_q_res:                              0
% 1.70/0.93  qbf_num_tautologies:                    0
% 1.70/0.93  qbf_prep_cycles:                        0
% 1.70/0.93  
% 1.70/0.93  ------ BMC1
% 1.70/0.93  
% 1.70/0.93  bmc1_current_bound:                     -1
% 1.70/0.93  bmc1_last_solved_bound:                 -1
% 1.70/0.93  bmc1_unsat_core_size:                   -1
% 1.70/0.93  bmc1_unsat_core_parents_size:           -1
% 1.70/0.93  bmc1_merge_next_fun:                    0
% 1.70/0.93  bmc1_unsat_core_clauses_time:           0.
% 1.70/0.93  
% 1.70/0.93  ------ Instantiation
% 1.70/0.93  
% 1.70/0.93  inst_num_of_clauses:                    41
% 1.70/0.93  inst_num_in_passive:                    0
% 1.70/0.93  inst_num_in_active:                     41
% 1.70/0.93  inst_num_in_unprocessed:                0
% 1.70/0.93  inst_num_of_loops:                      47
% 1.70/0.93  inst_num_of_learning_restarts:          0
% 1.70/0.93  inst_num_moves_active_passive:          0
% 1.70/0.93  inst_lit_activity:                      0
% 1.70/0.93  inst_lit_activity_moves:                0
% 1.70/0.93  inst_num_tautologies:                   0
% 1.70/0.93  inst_num_prop_implied:                  0
% 1.70/0.93  inst_num_existing_simplified:           0
% 1.70/0.93  inst_num_eq_res_simplified:             0
% 1.70/0.93  inst_num_child_elim:                    0
% 1.70/0.93  inst_num_of_dismatching_blockings:      0
% 1.70/0.93  inst_num_of_non_proper_insts:           21
% 1.70/0.93  inst_num_of_duplicates:                 0
% 1.70/0.93  inst_inst_num_from_inst_to_res:         0
% 1.70/0.93  inst_dismatching_checking_time:         0.
% 1.70/0.93  
% 1.70/0.93  ------ Resolution
% 1.70/0.93  
% 1.70/0.93  res_num_of_clauses:                     0
% 1.70/0.93  res_num_in_passive:                     0
% 1.70/0.93  res_num_in_active:                      0
% 1.70/0.93  res_num_of_loops:                       96
% 1.70/0.93  res_forward_subset_subsumed:            2
% 1.70/0.93  res_backward_subset_subsumed:           0
% 1.70/0.93  res_forward_subsumed:                   0
% 1.70/0.93  res_backward_subsumed:                  0
% 1.70/0.93  res_forward_subsumption_resolution:     3
% 1.70/0.93  res_backward_subsumption_resolution:    0
% 1.70/0.93  res_clause_to_clause_subsumption:       260
% 1.70/0.93  res_orphan_elimination:                 0
% 1.70/0.93  res_tautology_del:                      6
% 1.70/0.93  res_num_eq_res_simplified:              0
% 1.70/0.93  res_num_sel_changes:                    0
% 1.70/0.93  res_moves_from_active_to_pass:          0
% 1.70/0.93  
% 1.70/0.93  ------ Superposition
% 1.70/0.93  
% 1.70/0.93  sup_time_total:                         0.
% 1.70/0.93  sup_time_generating:                    0.
% 1.70/0.93  sup_time_sim_full:                      0.
% 1.70/0.93  sup_time_sim_immed:                     0.
% 1.70/0.93  
% 1.70/0.93  sup_num_of_clauses:                     19
% 1.70/0.93  sup_num_in_active:                      8
% 1.70/0.93  sup_num_in_passive:                     11
% 1.70/0.93  sup_num_of_loops:                       8
% 1.70/0.93  sup_fw_superposition:                   1
% 1.70/0.93  sup_bw_superposition:                   1
% 1.70/0.93  sup_immediate_simplified:               0
% 1.70/0.93  sup_given_eliminated:                   0
% 1.70/0.93  comparisons_done:                       0
% 1.70/0.93  comparisons_avoided:                    0
% 1.70/0.93  
% 1.70/0.93  ------ Simplifications
% 1.70/0.93  
% 1.70/0.93  
% 1.70/0.93  sim_fw_subset_subsumed:                 0
% 1.70/0.93  sim_bw_subset_subsumed:                 0
% 1.70/0.93  sim_fw_subsumed:                        0
% 1.70/0.93  sim_bw_subsumed:                        0
% 1.70/0.93  sim_fw_subsumption_res:                 0
% 1.70/0.93  sim_bw_subsumption_res:                 0
% 1.70/0.93  sim_tautology_del:                      0
% 1.70/0.93  sim_eq_tautology_del:                   0
% 1.70/0.93  sim_eq_res_simp:                        0
% 1.70/0.93  sim_fw_demodulated:                     0
% 1.70/0.93  sim_bw_demodulated:                     0
% 1.70/0.93  sim_light_normalised:                   0
% 1.70/0.93  sim_joinable_taut:                      0
% 1.70/0.93  sim_joinable_simp:                      0
% 1.70/0.93  sim_ac_normalised:                      0
% 1.70/0.93  sim_smt_subsumption:                    0
% 1.70/0.93  
%------------------------------------------------------------------------------
