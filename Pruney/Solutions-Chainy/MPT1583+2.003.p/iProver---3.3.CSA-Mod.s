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
% DateTime   : Thu Dec  3 12:19:59 EST 2020

% Result     : CounterSatisfiable 2.16s
% Output     : Model 2.16s
% Verified   : 
% Statistics : -

% Comments   : 
%------------------------------------------------------------------------------
%----WARNING: Could not form TPTP format derivation
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.16/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.16/1.00  
% 2.16/1.00  ------  iProver source info
% 2.16/1.00  
% 2.16/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.16/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.16/1.00  git: non_committed_changes: false
% 2.16/1.00  git: last_make_outside_of_git: false
% 2.16/1.00  
% 2.16/1.00  ------ 
% 2.16/1.00  
% 2.16/1.00  ------ Input Options
% 2.16/1.00  
% 2.16/1.00  --out_options                           all
% 2.16/1.00  --tptp_safe_out                         true
% 2.16/1.00  --problem_path                          ""
% 2.16/1.00  --include_path                          ""
% 2.16/1.00  --clausifier                            res/vclausify_rel
% 2.16/1.00  --clausifier_options                    --mode clausify
% 2.16/1.00  --stdin                                 false
% 2.16/1.00  --stats_out                             all
% 2.16/1.00  
% 2.16/1.00  ------ General Options
% 2.16/1.00  
% 2.16/1.00  --fof                                   false
% 2.16/1.00  --time_out_real                         305.
% 2.16/1.00  --time_out_virtual                      -1.
% 2.16/1.00  --symbol_type_check                     false
% 2.16/1.00  --clausify_out                          false
% 2.16/1.00  --sig_cnt_out                           false
% 2.16/1.00  --trig_cnt_out                          false
% 2.16/1.00  --trig_cnt_out_tolerance                1.
% 2.16/1.00  --trig_cnt_out_sk_spl                   false
% 2.16/1.00  --abstr_cl_out                          false
% 2.16/1.00  
% 2.16/1.00  ------ Global Options
% 2.16/1.00  
% 2.16/1.00  --schedule                              default
% 2.16/1.00  --add_important_lit                     false
% 2.16/1.00  --prop_solver_per_cl                    1000
% 2.16/1.00  --min_unsat_core                        false
% 2.16/1.00  --soft_assumptions                      false
% 2.16/1.00  --soft_lemma_size                       3
% 2.16/1.00  --prop_impl_unit_size                   0
% 2.16/1.00  --prop_impl_unit                        []
% 2.16/1.00  --share_sel_clauses                     true
% 2.16/1.00  --reset_solvers                         false
% 2.16/1.00  --bc_imp_inh                            [conj_cone]
% 2.16/1.00  --conj_cone_tolerance                   3.
% 2.16/1.00  --extra_neg_conj                        none
% 2.16/1.00  --large_theory_mode                     true
% 2.16/1.00  --prolific_symb_bound                   200
% 2.16/1.00  --lt_threshold                          2000
% 2.16/1.00  --clause_weak_htbl                      true
% 2.16/1.00  --gc_record_bc_elim                     false
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing Options
% 2.16/1.00  
% 2.16/1.00  --preprocessing_flag                    true
% 2.16/1.00  --time_out_prep_mult                    0.1
% 2.16/1.00  --splitting_mode                        input
% 2.16/1.00  --splitting_grd                         true
% 2.16/1.00  --splitting_cvd                         false
% 2.16/1.00  --splitting_cvd_svl                     false
% 2.16/1.00  --splitting_nvd                         32
% 2.16/1.00  --sub_typing                            true
% 2.16/1.00  --prep_gs_sim                           true
% 2.16/1.00  --prep_unflatten                        true
% 2.16/1.00  --prep_res_sim                          true
% 2.16/1.00  --prep_upred                            true
% 2.16/1.00  --prep_sem_filter                       exhaustive
% 2.16/1.00  --prep_sem_filter_out                   false
% 2.16/1.00  --pred_elim                             true
% 2.16/1.00  --res_sim_input                         true
% 2.16/1.00  --eq_ax_congr_red                       true
% 2.16/1.00  --pure_diseq_elim                       true
% 2.16/1.00  --brand_transform                       false
% 2.16/1.00  --non_eq_to_eq                          false
% 2.16/1.00  --prep_def_merge                        true
% 2.16/1.00  --prep_def_merge_prop_impl              false
% 2.16/1.00  --prep_def_merge_mbd                    true
% 2.16/1.00  --prep_def_merge_tr_red                 false
% 2.16/1.00  --prep_def_merge_tr_cl                  false
% 2.16/1.00  --smt_preprocessing                     true
% 2.16/1.00  --smt_ac_axioms                         fast
% 2.16/1.00  --preprocessed_out                      false
% 2.16/1.00  --preprocessed_stats                    false
% 2.16/1.00  
% 2.16/1.00  ------ Abstraction refinement Options
% 2.16/1.00  
% 2.16/1.00  --abstr_ref                             []
% 2.16/1.00  --abstr_ref_prep                        false
% 2.16/1.00  --abstr_ref_until_sat                   false
% 2.16/1.00  --abstr_ref_sig_restrict                funpre
% 2.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.00  --abstr_ref_under                       []
% 2.16/1.00  
% 2.16/1.00  ------ SAT Options
% 2.16/1.00  
% 2.16/1.00  --sat_mode                              false
% 2.16/1.00  --sat_fm_restart_options                ""
% 2.16/1.00  --sat_gr_def                            false
% 2.16/1.00  --sat_epr_types                         true
% 2.16/1.00  --sat_non_cyclic_types                  false
% 2.16/1.00  --sat_finite_models                     false
% 2.16/1.00  --sat_fm_lemmas                         false
% 2.16/1.00  --sat_fm_prep                           false
% 2.16/1.00  --sat_fm_uc_incr                        true
% 2.16/1.00  --sat_out_model                         small
% 2.16/1.00  --sat_out_clauses                       false
% 2.16/1.00  
% 2.16/1.00  ------ QBF Options
% 2.16/1.00  
% 2.16/1.00  --qbf_mode                              false
% 2.16/1.00  --qbf_elim_univ                         false
% 2.16/1.00  --qbf_dom_inst                          none
% 2.16/1.00  --qbf_dom_pre_inst                      false
% 2.16/1.00  --qbf_sk_in                             false
% 2.16/1.00  --qbf_pred_elim                         true
% 2.16/1.00  --qbf_split                             512
% 2.16/1.00  
% 2.16/1.00  ------ BMC1 Options
% 2.16/1.00  
% 2.16/1.00  --bmc1_incremental                      false
% 2.16/1.00  --bmc1_axioms                           reachable_all
% 2.16/1.00  --bmc1_min_bound                        0
% 2.16/1.00  --bmc1_max_bound                        -1
% 2.16/1.00  --bmc1_max_bound_default                -1
% 2.16/1.00  --bmc1_symbol_reachability              true
% 2.16/1.00  --bmc1_property_lemmas                  false
% 2.16/1.00  --bmc1_k_induction                      false
% 2.16/1.00  --bmc1_non_equiv_states                 false
% 2.16/1.00  --bmc1_deadlock                         false
% 2.16/1.00  --bmc1_ucm                              false
% 2.16/1.00  --bmc1_add_unsat_core                   none
% 2.16/1.00  --bmc1_unsat_core_children              false
% 2.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.00  --bmc1_out_stat                         full
% 2.16/1.00  --bmc1_ground_init                      false
% 2.16/1.00  --bmc1_pre_inst_next_state              false
% 2.16/1.00  --bmc1_pre_inst_state                   false
% 2.16/1.00  --bmc1_pre_inst_reach_state             false
% 2.16/1.00  --bmc1_out_unsat_core                   false
% 2.16/1.00  --bmc1_aig_witness_out                  false
% 2.16/1.00  --bmc1_verbose                          false
% 2.16/1.00  --bmc1_dump_clauses_tptp                false
% 2.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.00  --bmc1_dump_file                        -
% 2.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.00  --bmc1_ucm_extend_mode                  1
% 2.16/1.00  --bmc1_ucm_init_mode                    2
% 2.16/1.00  --bmc1_ucm_cone_mode                    none
% 2.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.00  --bmc1_ucm_relax_model                  4
% 2.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.00  --bmc1_ucm_layered_model                none
% 2.16/1.00  --bmc1_ucm_max_lemma_size               10
% 2.16/1.00  
% 2.16/1.00  ------ AIG Options
% 2.16/1.00  
% 2.16/1.00  --aig_mode                              false
% 2.16/1.00  
% 2.16/1.00  ------ Instantiation Options
% 2.16/1.00  
% 2.16/1.00  --instantiation_flag                    true
% 2.16/1.00  --inst_sos_flag                         false
% 2.16/1.00  --inst_sos_phase                        true
% 2.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel_side                     num_symb
% 2.16/1.00  --inst_solver_per_active                1400
% 2.16/1.00  --inst_solver_calls_frac                1.
% 2.16/1.00  --inst_passive_queue_type               priority_queues
% 2.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.00  --inst_passive_queues_freq              [25;2]
% 2.16/1.00  --inst_dismatching                      true
% 2.16/1.00  --inst_eager_unprocessed_to_passive     true
% 2.16/1.00  --inst_prop_sim_given                   true
% 2.16/1.00  --inst_prop_sim_new                     false
% 2.16/1.00  --inst_subs_new                         false
% 2.16/1.00  --inst_eq_res_simp                      false
% 2.16/1.00  --inst_subs_given                       false
% 2.16/1.00  --inst_orphan_elimination               true
% 2.16/1.00  --inst_learning_loop_flag               true
% 2.16/1.00  --inst_learning_start                   3000
% 2.16/1.00  --inst_learning_factor                  2
% 2.16/1.00  --inst_start_prop_sim_after_learn       3
% 2.16/1.00  --inst_sel_renew                        solver
% 2.16/1.00  --inst_lit_activity_flag                true
% 2.16/1.00  --inst_restr_to_given                   false
% 2.16/1.00  --inst_activity_threshold               500
% 2.16/1.00  --inst_out_proof                        true
% 2.16/1.00  
% 2.16/1.00  ------ Resolution Options
% 2.16/1.00  
% 2.16/1.00  --resolution_flag                       true
% 2.16/1.00  --res_lit_sel                           adaptive
% 2.16/1.00  --res_lit_sel_side                      none
% 2.16/1.00  --res_ordering                          kbo
% 2.16/1.00  --res_to_prop_solver                    active
% 2.16/1.00  --res_prop_simpl_new                    false
% 2.16/1.00  --res_prop_simpl_given                  true
% 2.16/1.00  --res_passive_queue_type                priority_queues
% 2.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.00  --res_passive_queues_freq               [15;5]
% 2.16/1.00  --res_forward_subs                      full
% 2.16/1.00  --res_backward_subs                     full
% 2.16/1.00  --res_forward_subs_resolution           true
% 2.16/1.00  --res_backward_subs_resolution          true
% 2.16/1.00  --res_orphan_elimination                true
% 2.16/1.00  --res_time_limit                        2.
% 2.16/1.00  --res_out_proof                         true
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Options
% 2.16/1.00  
% 2.16/1.00  --superposition_flag                    true
% 2.16/1.00  --sup_passive_queue_type                priority_queues
% 2.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.00  --demod_completeness_check              fast
% 2.16/1.00  --demod_use_ground                      true
% 2.16/1.00  --sup_to_prop_solver                    passive
% 2.16/1.00  --sup_prop_simpl_new                    true
% 2.16/1.00  --sup_prop_simpl_given                  true
% 2.16/1.00  --sup_fun_splitting                     false
% 2.16/1.00  --sup_smt_interval                      50000
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Simplification Setup
% 2.16/1.00  
% 2.16/1.00  --sup_indices_passive                   []
% 2.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_full_bw                           [BwDemod]
% 2.16/1.00  --sup_immed_triv                        [TrivRules]
% 2.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_immed_bw_main                     []
% 2.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  
% 2.16/1.00  ------ Combination Options
% 2.16/1.00  
% 2.16/1.00  --comb_res_mult                         3
% 2.16/1.00  --comb_sup_mult                         2
% 2.16/1.00  --comb_inst_mult                        10
% 2.16/1.00  
% 2.16/1.00  ------ Debug Options
% 2.16/1.00  
% 2.16/1.00  --dbg_backtrace                         false
% 2.16/1.00  --dbg_dump_prop_clauses                 false
% 2.16/1.00  --dbg_dump_prop_clauses_file            -
% 2.16/1.00  --dbg_out_stat                          false
% 2.16/1.00  ------ Parsing...
% 2.16/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.16/1.00  ------ Proving...
% 2.16/1.00  ------ Problem Properties 
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  clauses                                 19
% 2.16/1.00  conjectures                             7
% 2.16/1.00  EPR                                     6
% 2.16/1.00  Horn                                    14
% 2.16/1.00  unary                                   3
% 2.16/1.00  binary                                  6
% 2.16/1.00  lits                                    49
% 2.16/1.00  lits eq                                 2
% 2.16/1.00  fd_pure                                 0
% 2.16/1.00  fd_pseudo                               0
% 2.16/1.00  fd_cond                                 0
% 2.16/1.00  fd_pseudo_cond                          0
% 2.16/1.00  AC symbols                              0
% 2.16/1.00  
% 2.16/1.00  ------ Schedule dynamic 5 is on 
% 2.16/1.00  
% 2.16/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  ------ 
% 2.16/1.00  Current options:
% 2.16/1.00  ------ 
% 2.16/1.00  
% 2.16/1.00  ------ Input Options
% 2.16/1.00  
% 2.16/1.00  --out_options                           all
% 2.16/1.00  --tptp_safe_out                         true
% 2.16/1.00  --problem_path                          ""
% 2.16/1.00  --include_path                          ""
% 2.16/1.00  --clausifier                            res/vclausify_rel
% 2.16/1.00  --clausifier_options                    --mode clausify
% 2.16/1.00  --stdin                                 false
% 2.16/1.00  --stats_out                             all
% 2.16/1.00  
% 2.16/1.00  ------ General Options
% 2.16/1.00  
% 2.16/1.00  --fof                                   false
% 2.16/1.00  --time_out_real                         305.
% 2.16/1.00  --time_out_virtual                      -1.
% 2.16/1.00  --symbol_type_check                     false
% 2.16/1.00  --clausify_out                          false
% 2.16/1.00  --sig_cnt_out                           false
% 2.16/1.00  --trig_cnt_out                          false
% 2.16/1.00  --trig_cnt_out_tolerance                1.
% 2.16/1.00  --trig_cnt_out_sk_spl                   false
% 2.16/1.00  --abstr_cl_out                          false
% 2.16/1.00  
% 2.16/1.00  ------ Global Options
% 2.16/1.00  
% 2.16/1.00  --schedule                              default
% 2.16/1.00  --add_important_lit                     false
% 2.16/1.00  --prop_solver_per_cl                    1000
% 2.16/1.00  --min_unsat_core                        false
% 2.16/1.00  --soft_assumptions                      false
% 2.16/1.00  --soft_lemma_size                       3
% 2.16/1.00  --prop_impl_unit_size                   0
% 2.16/1.00  --prop_impl_unit                        []
% 2.16/1.00  --share_sel_clauses                     true
% 2.16/1.00  --reset_solvers                         false
% 2.16/1.00  --bc_imp_inh                            [conj_cone]
% 2.16/1.00  --conj_cone_tolerance                   3.
% 2.16/1.00  --extra_neg_conj                        none
% 2.16/1.00  --large_theory_mode                     true
% 2.16/1.00  --prolific_symb_bound                   200
% 2.16/1.00  --lt_threshold                          2000
% 2.16/1.00  --clause_weak_htbl                      true
% 2.16/1.00  --gc_record_bc_elim                     false
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing Options
% 2.16/1.00  
% 2.16/1.00  --preprocessing_flag                    true
% 2.16/1.00  --time_out_prep_mult                    0.1
% 2.16/1.00  --splitting_mode                        input
% 2.16/1.00  --splitting_grd                         true
% 2.16/1.00  --splitting_cvd                         false
% 2.16/1.00  --splitting_cvd_svl                     false
% 2.16/1.00  --splitting_nvd                         32
% 2.16/1.00  --sub_typing                            true
% 2.16/1.00  --prep_gs_sim                           true
% 2.16/1.00  --prep_unflatten                        true
% 2.16/1.00  --prep_res_sim                          true
% 2.16/1.00  --prep_upred                            true
% 2.16/1.00  --prep_sem_filter                       exhaustive
% 2.16/1.00  --prep_sem_filter_out                   false
% 2.16/1.00  --pred_elim                             true
% 2.16/1.00  --res_sim_input                         true
% 2.16/1.00  --eq_ax_congr_red                       true
% 2.16/1.00  --pure_diseq_elim                       true
% 2.16/1.00  --brand_transform                       false
% 2.16/1.00  --non_eq_to_eq                          false
% 2.16/1.00  --prep_def_merge                        true
% 2.16/1.00  --prep_def_merge_prop_impl              false
% 2.16/1.00  --prep_def_merge_mbd                    true
% 2.16/1.00  --prep_def_merge_tr_red                 false
% 2.16/1.00  --prep_def_merge_tr_cl                  false
% 2.16/1.00  --smt_preprocessing                     true
% 2.16/1.00  --smt_ac_axioms                         fast
% 2.16/1.00  --preprocessed_out                      false
% 2.16/1.00  --preprocessed_stats                    false
% 2.16/1.00  
% 2.16/1.00  ------ Abstraction refinement Options
% 2.16/1.00  
% 2.16/1.00  --abstr_ref                             []
% 2.16/1.00  --abstr_ref_prep                        false
% 2.16/1.00  --abstr_ref_until_sat                   false
% 2.16/1.00  --abstr_ref_sig_restrict                funpre
% 2.16/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/1.00  --abstr_ref_under                       []
% 2.16/1.00  
% 2.16/1.00  ------ SAT Options
% 2.16/1.00  
% 2.16/1.00  --sat_mode                              false
% 2.16/1.00  --sat_fm_restart_options                ""
% 2.16/1.00  --sat_gr_def                            false
% 2.16/1.00  --sat_epr_types                         true
% 2.16/1.00  --sat_non_cyclic_types                  false
% 2.16/1.00  --sat_finite_models                     false
% 2.16/1.00  --sat_fm_lemmas                         false
% 2.16/1.00  --sat_fm_prep                           false
% 2.16/1.00  --sat_fm_uc_incr                        true
% 2.16/1.00  --sat_out_model                         small
% 2.16/1.00  --sat_out_clauses                       false
% 2.16/1.00  
% 2.16/1.00  ------ QBF Options
% 2.16/1.00  
% 2.16/1.00  --qbf_mode                              false
% 2.16/1.00  --qbf_elim_univ                         false
% 2.16/1.00  --qbf_dom_inst                          none
% 2.16/1.00  --qbf_dom_pre_inst                      false
% 2.16/1.00  --qbf_sk_in                             false
% 2.16/1.00  --qbf_pred_elim                         true
% 2.16/1.00  --qbf_split                             512
% 2.16/1.00  
% 2.16/1.00  ------ BMC1 Options
% 2.16/1.00  
% 2.16/1.00  --bmc1_incremental                      false
% 2.16/1.00  --bmc1_axioms                           reachable_all
% 2.16/1.00  --bmc1_min_bound                        0
% 2.16/1.00  --bmc1_max_bound                        -1
% 2.16/1.00  --bmc1_max_bound_default                -1
% 2.16/1.00  --bmc1_symbol_reachability              true
% 2.16/1.00  --bmc1_property_lemmas                  false
% 2.16/1.00  --bmc1_k_induction                      false
% 2.16/1.00  --bmc1_non_equiv_states                 false
% 2.16/1.00  --bmc1_deadlock                         false
% 2.16/1.00  --bmc1_ucm                              false
% 2.16/1.00  --bmc1_add_unsat_core                   none
% 2.16/1.00  --bmc1_unsat_core_children              false
% 2.16/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/1.00  --bmc1_out_stat                         full
% 2.16/1.00  --bmc1_ground_init                      false
% 2.16/1.00  --bmc1_pre_inst_next_state              false
% 2.16/1.00  --bmc1_pre_inst_state                   false
% 2.16/1.00  --bmc1_pre_inst_reach_state             false
% 2.16/1.00  --bmc1_out_unsat_core                   false
% 2.16/1.00  --bmc1_aig_witness_out                  false
% 2.16/1.00  --bmc1_verbose                          false
% 2.16/1.00  --bmc1_dump_clauses_tptp                false
% 2.16/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.16/1.00  --bmc1_dump_file                        -
% 2.16/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.16/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.16/1.00  --bmc1_ucm_extend_mode                  1
% 2.16/1.00  --bmc1_ucm_init_mode                    2
% 2.16/1.00  --bmc1_ucm_cone_mode                    none
% 2.16/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.16/1.00  --bmc1_ucm_relax_model                  4
% 2.16/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.16/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/1.00  --bmc1_ucm_layered_model                none
% 2.16/1.00  --bmc1_ucm_max_lemma_size               10
% 2.16/1.00  
% 2.16/1.00  ------ AIG Options
% 2.16/1.00  
% 2.16/1.00  --aig_mode                              false
% 2.16/1.00  
% 2.16/1.00  ------ Instantiation Options
% 2.16/1.00  
% 2.16/1.00  --instantiation_flag                    true
% 2.16/1.00  --inst_sos_flag                         false
% 2.16/1.00  --inst_sos_phase                        true
% 2.16/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/1.00  --inst_lit_sel_side                     none
% 2.16/1.00  --inst_solver_per_active                1400
% 2.16/1.00  --inst_solver_calls_frac                1.
% 2.16/1.00  --inst_passive_queue_type               priority_queues
% 2.16/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/1.00  --inst_passive_queues_freq              [25;2]
% 2.16/1.00  --inst_dismatching                      true
% 2.16/1.00  --inst_eager_unprocessed_to_passive     true
% 2.16/1.00  --inst_prop_sim_given                   true
% 2.16/1.00  --inst_prop_sim_new                     false
% 2.16/1.00  --inst_subs_new                         false
% 2.16/1.00  --inst_eq_res_simp                      false
% 2.16/1.00  --inst_subs_given                       false
% 2.16/1.00  --inst_orphan_elimination               true
% 2.16/1.00  --inst_learning_loop_flag               true
% 2.16/1.00  --inst_learning_start                   3000
% 2.16/1.00  --inst_learning_factor                  2
% 2.16/1.00  --inst_start_prop_sim_after_learn       3
% 2.16/1.00  --inst_sel_renew                        solver
% 2.16/1.00  --inst_lit_activity_flag                true
% 2.16/1.00  --inst_restr_to_given                   false
% 2.16/1.00  --inst_activity_threshold               500
% 2.16/1.00  --inst_out_proof                        true
% 2.16/1.00  
% 2.16/1.00  ------ Resolution Options
% 2.16/1.00  
% 2.16/1.00  --resolution_flag                       false
% 2.16/1.00  --res_lit_sel                           adaptive
% 2.16/1.00  --res_lit_sel_side                      none
% 2.16/1.00  --res_ordering                          kbo
% 2.16/1.00  --res_to_prop_solver                    active
% 2.16/1.00  --res_prop_simpl_new                    false
% 2.16/1.00  --res_prop_simpl_given                  true
% 2.16/1.00  --res_passive_queue_type                priority_queues
% 2.16/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/1.00  --res_passive_queues_freq               [15;5]
% 2.16/1.00  --res_forward_subs                      full
% 2.16/1.00  --res_backward_subs                     full
% 2.16/1.00  --res_forward_subs_resolution           true
% 2.16/1.00  --res_backward_subs_resolution          true
% 2.16/1.00  --res_orphan_elimination                true
% 2.16/1.00  --res_time_limit                        2.
% 2.16/1.00  --res_out_proof                         true
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Options
% 2.16/1.00  
% 2.16/1.00  --superposition_flag                    true
% 2.16/1.00  --sup_passive_queue_type                priority_queues
% 2.16/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.16/1.00  --demod_completeness_check              fast
% 2.16/1.00  --demod_use_ground                      true
% 2.16/1.00  --sup_to_prop_solver                    passive
% 2.16/1.00  --sup_prop_simpl_new                    true
% 2.16/1.00  --sup_prop_simpl_given                  true
% 2.16/1.00  --sup_fun_splitting                     false
% 2.16/1.00  --sup_smt_interval                      50000
% 2.16/1.00  
% 2.16/1.00  ------ Superposition Simplification Setup
% 2.16/1.00  
% 2.16/1.00  --sup_indices_passive                   []
% 2.16/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_full_bw                           [BwDemod]
% 2.16/1.00  --sup_immed_triv                        [TrivRules]
% 2.16/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_immed_bw_main                     []
% 2.16/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/1.00  
% 2.16/1.00  ------ Combination Options
% 2.16/1.00  
% 2.16/1.00  --comb_res_mult                         3
% 2.16/1.00  --comb_sup_mult                         2
% 2.16/1.00  --comb_inst_mult                        10
% 2.16/1.00  
% 2.16/1.00  ------ Debug Options
% 2.16/1.00  
% 2.16/1.00  --dbg_backtrace                         false
% 2.16/1.00  --dbg_dump_prop_clauses                 false
% 2.16/1.00  --dbg_dump_prop_clauses_file            -
% 2.16/1.00  --dbg_out_stat                          false
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  ------ Proving...
% 2.16/1.00  
% 2.16/1.00  
% 2.16/1.00  % SZS status CounterSatisfiable for theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  ------ Building Model...Done
% 2.16/1.00  
% 2.16/1.00  %------ The model is defined over ground terms (initial term algebra).
% 2.16/1.00  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 2.16/1.00  %------ where \phi is a formula over the term algebra.
% 2.16/1.00  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 2.16/1.00  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 2.16/1.00  %------ See help for --sat_out_model for different model outputs.
% 2.16/1.00  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 2.16/1.00  %------ where the first argument stands for the sort ($i in the unsorted case)
% 2.16/1.00  % SZS output start Model for theBenchmark.p
% 2.16/1.00  
% 2.16/1.00  %------ Positive definition of equality_sorted 
% 2.16/1.00  fof(lit_def,axiom,
% 2.16/1.00      (! [X0_0,X0_2,X1_2] : 
% 2.16/1.00        ( equality_sorted(X0_0,X0_2,X1_2) <=>
% 2.16/1.00             (
% 2.16/1.00                (
% 2.16/1.00                  ( X0_0=$o & X1_2=X0_2 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_0=iProver_u1_struct_0_1_$i )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_47!=sK3 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_47!=sK2 | X1_47!=sK3 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X1_47!=sK3 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_0=iProver_u1_struct_0_1_$i & X0_47=sK3 & X1_47=sK3 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_0=iProver_u1_struct_0_1_$i & X1_47=X0_47 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_47!=sK3 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_0=iProver_m1_subset_1_1_$i )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_46!=sK6 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_46!=sK5 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_46!=u1_struct_0(sK3) )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_46!=u1_struct_0(sK2) )
% 2.16/1.00                 &
% 2.16/1.00                  ! [X0_47] : ( X0_46!=u1_struct_0(X0_47) )
% 2.16/1.00                 &
% 2.16/1.00                  ( X1_46!=sK6 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X1_46!=sK5 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X1_46!=u1_struct_0(sK3) )
% 2.16/1.00                 &
% 2.16/1.00                  ( X1_46!=u1_struct_0(sK2) )
% 2.16/1.00                 &
% 2.16/1.00                  ( X1_46!=u1_struct_0(X0_47) )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_0=iProver_m1_subset_1_1_$i & X0_46=sK6 & X1_46=sK6 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_0=iProver_m1_subset_1_1_$i & X0_46=sK6 & X1_46=sK5 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_0=iProver_m1_subset_1_1_$i & X0_46=sK5 & X1_46=sK6 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_0=iProver_m1_subset_1_1_$i & X0_46=sK5 & X1_46=sK5 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_0=iProver_m1_subset_1_1_$i & X0_46=u1_struct_0(sK3) & X1_46=u1_struct_0(sK3) )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_0=iProver_m1_subset_1_1_$i & X0_46=u1_struct_0(sK2) & X1_46=u1_struct_0(sK2) )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00              ? [X0_47] : 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_0=iProver_m1_subset_1_1_$i & X0_46=u1_struct_0(sK2) & X1_46=u1_struct_0(X0_47) )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_47!=sK3 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_47!=sK2 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00              ? [X0_47] : 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_0=iProver_m1_subset_1_1_$i & X0_46=u1_struct_0(X0_47) & X1_46=u1_struct_0(sK2) )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_47!=sK3 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_47!=sK2 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00              ? [X0_47] : 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_0=iProver_m1_subset_1_1_$i & X0_46=u1_struct_0(X0_47) & X1_46=u1_struct_0(X0_47) )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_47!=sK3 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_47!=sK2 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00              ? [X0_47,X1_47] : 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_0=iProver_m1_subset_1_1_$i & X0_46=u1_struct_0(X0_47) & X1_46=u1_struct_0(X1_47) )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_47!=sK3 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_47!=sK3 | X1_47!=sK2 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_47!=sK2 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_47!=sK2 | X1_47!=sK3 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X1_47!=sK3 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X1_47!=sK2 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00              ? [X0_47,X2_46,X3_46,X1_47] : 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_0=iProver_m1_subset_1_1_$i & X0_46=sK0(X0_47,X2_46,X3_46) & X1_46=sK0(X1_47,X2_46,X3_46) )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00              ? [X0_47,X2_46,X3_46,X1_47] : 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_0=iProver_m1_subset_1_1_$i & X0_46=sK1(X0_47,X2_46,X3_46) & X1_46=sK1(X1_47,X2_46,X3_46) )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_0=iProver_m1_subset_1_1_$i & X1_46=X0_46 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_46!=sK6 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_46!=sK5 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_46!=u1_struct_0(sK3) )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_46!=u1_struct_0(sK2) )
% 2.16/1.00                 &
% 2.16/1.00                  ! [X0_47] : ( X0_46!=u1_struct_0(X0_47) )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00             )
% 2.16/1.00        )
% 2.16/1.00      )
% 2.16/1.00     ).
% 2.16/1.00  
% 2.16/1.00  %------ Positive definition of m1_subset_1 
% 2.16/1.00  fof(lit_def,axiom,
% 2.16/1.00      (! [X0_46,X1_46] : 
% 2.16/1.00        ( m1_subset_1(X0_46,X1_46) <=>
% 2.16/1.00             (
% 2.16/1.00                (
% 2.16/1.00                  ( X0_46=sK6 & X1_46=u1_struct_0(sK3) )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_46=sK6 & X1_46=u1_struct_0(sK2) )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00              ? [X0_47] : 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_46=sK6 & X1_46=u1_struct_0(X0_47) )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_46=sK5 & X1_46=u1_struct_0(sK3) )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_46=sK5 & X1_46=u1_struct_0(sK2) )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00              ? [X0_47] : 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_46=sK5 & X1_46=u1_struct_0(X0_47) )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_47!=sK2 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00             )
% 2.16/1.00        )
% 2.16/1.00      )
% 2.16/1.00     ).
% 2.16/1.00  
% 2.16/1.00  %------ Positive definition of r2_hidden 
% 2.16/1.00  fof(lit_def,axiom,
% 2.16/1.00      (! [X0_46,X1_46] : 
% 2.16/1.00        ( r2_hidden(X0_46,X1_46) <=>
% 2.16/1.00             (
% 2.16/1.00                (
% 2.16/1.00                  ( X0_46=sK6 & X1_46=u1_struct_0(sK2) )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00              ? [X0_47] : 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_46=sK6 & X1_46=u1_struct_0(X0_47) )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_46=sK5 & X1_46=u1_struct_0(sK2) )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00              ? [X0_47] : 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_46=sK5 & X1_46=u1_struct_0(X0_47) )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00             )
% 2.16/1.00        )
% 2.16/1.00      )
% 2.16/1.00     ).
% 2.16/1.00  
% 2.16/1.00  %------ Positive definition of v1_xboole_0 
% 2.16/1.00  fof(lit_def,axiom,
% 2.16/1.00      (! [X0] : 
% 2.16/1.00        ( v1_xboole_0(X0) <=>
% 2.16/1.00            $false
% 2.16/1.00        )
% 2.16/1.00      )
% 2.16/1.00     ).
% 2.16/1.00  
% 2.16/1.00  %------ Positive definition of v2_struct_0 
% 2.16/1.00  fof(lit_def,axiom,
% 2.16/1.00      (! [X0] : 
% 2.16/1.00        ( v2_struct_0(X0) <=>
% 2.16/1.00            $false
% 2.16/1.00        )
% 2.16/1.00      )
% 2.16/1.00     ).
% 2.16/1.00  
% 2.16/1.00  %------ Positive definition of l1_orders_2 
% 2.16/1.00  fof(lit_def,axiom,
% 2.16/1.00      (! [X0] : 
% 2.16/1.00        ( l1_orders_2(X0) <=>
% 2.16/1.00            $false
% 2.16/1.00        )
% 2.16/1.00      )
% 2.16/1.00     ).
% 2.16/1.00  
% 2.16/1.00  %------ Negative definition of r1_lattice3 
% 2.16/1.00  fof(lit_def,axiom,
% 2.16/1.00      (! [X0_47,X0_46,X1_46] : 
% 2.16/1.00        ( ~(r1_lattice3(X0_47,X0_46,X1_46)) <=>
% 2.16/1.00             (
% 2.16/1.00                (
% 2.16/1.00                  ( X0_47!=sK2 | X1_46!=sK6 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_47!=sK2 | X1_46!=sK5 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X1_46!=sK6 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X1_46!=sK5 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00             )
% 2.16/1.00        )
% 2.16/1.00      )
% 2.16/1.00     ).
% 2.16/1.00  
% 2.16/1.00  %------ Positive definition of r1_orders_2 
% 2.16/1.00  fof(lit_def,axiom,
% 2.16/1.00      (! [X0_47,X0_46,X1_46] : 
% 2.16/1.00        ( r1_orders_2(X0_47,X0_46,X1_46) <=>
% 2.16/1.00             (
% 2.16/1.00                (
% 2.16/1.00                  ( X0_46=sK6 & X1_46=sK6 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_46=sK6 & X1_46=sK5 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_46=sK5 & X1_46=sK6 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_46=sK5 & X1_46=sK5 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_47=sK2 & X0_46=sK6 & X1_46=sK6 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_47=sK2 & X0_46=sK6 & X1_46=sK5 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_47=sK2 & X0_46=sK5 & X1_46=sK6 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_47=sK2 & X0_46=sK5 & X1_46=sK5 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00             )
% 2.16/1.00        )
% 2.16/1.00      )
% 2.16/1.00     ).
% 2.16/1.00  
% 2.16/1.00  %------ Negative definition of r2_lattice3 
% 2.16/1.00  fof(lit_def,axiom,
% 2.16/1.00      (! [X0_47,X0_46,X1_46] : 
% 2.16/1.00        ( ~(r2_lattice3(X0_47,X0_46,X1_46)) <=>
% 2.16/1.00             (
% 2.16/1.00                (
% 2.16/1.00                  ( X0_46!=sK4 | X0_47!=sK2 | X1_46!=sK5 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X0_47!=sK2 | X1_46!=sK5 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X1_46!=sK6 )
% 2.16/1.00                 &
% 2.16/1.00                  ( X1_46!=sK5 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_47=sK3 & X0_46=sK4 & X1_46=sK6 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_47=sK3 & X1_46=sK6 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00               | 
% 2.16/1.00                (
% 2.16/1.00                  ( X0_47=sK3 & X1_46=sK5 )
% 2.16/1.00                )
% 2.16/1.00  
% 2.16/1.00             )
% 2.16/1.00        )
% 2.16/1.00      )
% 2.16/1.00     ).
% 2.16/1.00  % SZS output end Model for theBenchmark.p
% 2.16/1.00  ------                               Statistics
% 2.16/1.00  
% 2.16/1.00  ------ General
% 2.16/1.00  
% 2.16/1.00  abstr_ref_over_cycles:                  0
% 2.16/1.00  abstr_ref_under_cycles:                 0
% 2.16/1.00  gc_basic_clause_elim:                   0
% 2.16/1.00  forced_gc_time:                         0
% 2.16/1.00  parsing_time:                           0.01
% 2.16/1.00  unif_index_cands_time:                  0.
% 2.16/1.00  unif_index_add_time:                    0.
% 2.16/1.00  orderings_time:                         0.
% 2.16/1.00  out_proof_time:                         0.
% 2.16/1.00  total_time:                             0.205
% 2.16/1.00  num_of_symbols:                         48
% 2.16/1.00  num_of_terms:                           4872
% 2.16/1.00  
% 2.16/1.00  ------ Preprocessing
% 2.16/1.00  
% 2.16/1.00  num_of_splits:                          0
% 2.16/1.00  num_of_split_atoms:                     0
% 2.16/1.00  num_of_reused_defs:                     0
% 2.16/1.00  num_eq_ax_congr_red:                    20
% 2.16/1.00  num_of_sem_filtered_clauses:            1
% 2.16/1.00  num_of_subtypes:                        2
% 2.16/1.00  monotx_restored_types:                  0
% 2.16/1.00  sat_num_of_epr_types:                   0
% 2.16/1.00  sat_num_of_non_cyclic_types:            0
% 2.16/1.00  sat_guarded_non_collapsed_types:        0
% 2.16/1.00  num_pure_diseq_elim:                    0
% 2.16/1.00  simp_replaced_by:                       0
% 2.16/1.00  res_preprocessed:                       105
% 2.16/1.00  prep_upred:                             0
% 2.16/1.00  prep_unflattend:                        169
% 2.16/1.00  smt_new_axioms:                         0
% 2.16/1.00  pred_elim_cands:                        5
% 2.16/1.00  pred_elim:                              4
% 2.16/1.00  pred_elim_cl:                           4
% 2.16/1.00  pred_elim_cycles:                       13
% 2.16/1.00  merged_defs:                            0
% 2.16/1.00  merged_defs_ncl:                        0
% 2.16/1.00  bin_hyper_res:                          0
% 2.16/1.00  prep_cycles:                            4
% 2.16/1.00  pred_elim_time:                         0.022
% 2.16/1.00  splitting_time:                         0.
% 2.16/1.00  sem_filter_time:                        0.
% 2.16/1.00  monotx_time:                            0.
% 2.16/1.00  subtype_inf_time:                       0.
% 2.16/1.00  
% 2.16/1.00  ------ Problem properties
% 2.16/1.00  
% 2.16/1.00  clauses:                                19
% 2.16/1.00  conjectures:                            7
% 2.16/1.00  epr:                                    6
% 2.16/1.00  horn:                                   14
% 2.16/1.00  ground:                                 7
% 2.16/1.00  unary:                                  3
% 2.16/1.00  binary:                                 6
% 2.16/1.00  lits:                                   49
% 2.16/1.00  lits_eq:                                2
% 2.16/1.00  fd_pure:                                0
% 2.16/1.00  fd_pseudo:                              0
% 2.16/1.00  fd_cond:                                0
% 2.16/1.00  fd_pseudo_cond:                         0
% 2.16/1.00  ac_symbols:                             0
% 2.16/1.00  
% 2.16/1.00  ------ Propositional Solver
% 2.16/1.00  
% 2.16/1.00  prop_solver_calls:                      31
% 2.16/1.00  prop_fast_solver_calls:                 1642
% 2.16/1.00  smt_solver_calls:                       0
% 2.16/1.00  smt_fast_solver_calls:                  0
% 2.16/1.00  prop_num_of_clauses:                    1580
% 2.16/1.00  prop_preprocess_simplified:             5098
% 2.16/1.00  prop_fo_subsumed:                       47
% 2.16/1.00  prop_solver_time:                       0.
% 2.16/1.00  smt_solver_time:                        0.
% 2.16/1.00  smt_fast_solver_time:                   0.
% 2.16/1.00  prop_fast_solver_time:                  0.
% 2.16/1.00  prop_unsat_core_time:                   0.
% 2.16/1.00  
% 2.16/1.00  ------ QBF
% 2.16/1.00  
% 2.16/1.00  qbf_q_res:                              0
% 2.16/1.00  qbf_num_tautologies:                    0
% 2.16/1.00  qbf_prep_cycles:                        0
% 2.16/1.00  
% 2.16/1.00  ------ BMC1
% 2.16/1.00  
% 2.16/1.00  bmc1_current_bound:                     -1
% 2.16/1.00  bmc1_last_solved_bound:                 -1
% 2.16/1.00  bmc1_unsat_core_size:                   -1
% 2.16/1.00  bmc1_unsat_core_parents_size:           -1
% 2.16/1.00  bmc1_merge_next_fun:                    0
% 2.16/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.16/1.00  
% 2.16/1.00  ------ Instantiation
% 2.16/1.00  
% 2.16/1.00  inst_num_of_clauses:                    363
% 2.16/1.00  inst_num_in_passive:                    0
% 2.16/1.00  inst_num_in_active:                     363
% 2.16/1.00  inst_num_in_unprocessed:                0
% 2.16/1.00  inst_num_of_loops:                      396
% 2.16/1.00  inst_num_of_learning_restarts:          0
% 2.16/1.00  inst_num_moves_active_passive:          23
% 2.16/1.00  inst_lit_activity:                      0
% 2.16/1.00  inst_lit_activity_moves:                0
% 2.16/1.00  inst_num_tautologies:                   0
% 2.16/1.00  inst_num_prop_implied:                  0
% 2.16/1.00  inst_num_existing_simplified:           0
% 2.16/1.00  inst_num_eq_res_simplified:             0
% 2.16/1.00  inst_num_child_elim:                    0
% 2.16/1.00  inst_num_of_dismatching_blockings:      110
% 2.16/1.00  inst_num_of_non_proper_insts:           520
% 2.16/1.00  inst_num_of_duplicates:                 0
% 2.16/1.00  inst_inst_num_from_inst_to_res:         0
% 2.16/1.00  inst_dismatching_checking_time:         0.
% 2.16/1.01  
% 2.16/1.01  ------ Resolution
% 2.16/1.01  
% 2.16/1.01  res_num_of_clauses:                     0
% 2.16/1.01  res_num_in_passive:                     0
% 2.16/1.01  res_num_in_active:                      0
% 2.16/1.01  res_num_of_loops:                       109
% 2.16/1.01  res_forward_subset_subsumed:            87
% 2.16/1.01  res_backward_subset_subsumed:           0
% 2.16/1.01  res_forward_subsumed:                   8
% 2.16/1.01  res_backward_subsumed:                  0
% 2.16/1.01  res_forward_subsumption_resolution:     6
% 2.16/1.01  res_backward_subsumption_resolution:    0
% 2.16/1.01  res_clause_to_clause_subsumption:       2445
% 2.16/1.01  res_orphan_elimination:                 0
% 2.16/1.01  res_tautology_del:                      64
% 2.16/1.01  res_num_eq_res_simplified:              0
% 2.16/1.01  res_num_sel_changes:                    0
% 2.16/1.01  res_moves_from_active_to_pass:          0
% 2.16/1.01  
% 2.16/1.01  ------ Superposition
% 2.16/1.01  
% 2.16/1.01  sup_time_total:                         0.
% 2.16/1.01  sup_time_generating:                    0.
% 2.16/1.01  sup_time_sim_full:                      0.
% 2.16/1.01  sup_time_sim_immed:                     0.
% 2.16/1.01  
% 2.16/1.01  sup_num_of_clauses:                     101
% 2.16/1.01  sup_num_in_active:                      78
% 2.16/1.01  sup_num_in_passive:                     23
% 2.16/1.01  sup_num_of_loops:                       78
% 2.16/1.01  sup_fw_superposition:                   42
% 2.16/1.01  sup_bw_superposition:                   142
% 2.16/1.01  sup_immediate_simplified:               99
% 2.16/1.01  sup_given_eliminated:                   0
% 2.16/1.01  comparisons_done:                       0
% 2.16/1.01  comparisons_avoided:                    0
% 2.16/1.01  
% 2.16/1.01  ------ Simplifications
% 2.16/1.01  
% 2.16/1.01  
% 2.16/1.01  sim_fw_subset_subsumed:                 1
% 2.16/1.01  sim_bw_subset_subsumed:                 0
% 2.16/1.01  sim_fw_subsumed:                        102
% 2.16/1.01  sim_bw_subsumed:                        2
% 2.16/1.01  sim_fw_subsumption_res:                 0
% 2.16/1.01  sim_bw_subsumption_res:                 0
% 2.16/1.01  sim_tautology_del:                      1
% 2.16/1.01  sim_eq_tautology_del:                   0
% 2.16/1.01  sim_eq_res_simp:                        0
% 2.16/1.01  sim_fw_demodulated:                     0
% 2.16/1.01  sim_bw_demodulated:                     0
% 2.16/1.01  sim_light_normalised:                   4
% 2.16/1.01  sim_joinable_taut:                      0
% 2.16/1.01  sim_joinable_simp:                      0
% 2.16/1.01  sim_ac_normalised:                      0
% 2.16/1.01  sim_smt_subsumption:                    0
% 2.16/1.01  
%------------------------------------------------------------------------------
