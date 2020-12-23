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
% DateTime   : Thu Dec  3 11:30:13 EST 2020

% Result     : CounterSatisfiable 0.49s
% Output     : Model 0.49s
% Verified   : 
% Statistics : Number of formulae       :    2 (   2 expanded)
%              Number of leaves         :    2 (   2 expanded)
%              Depth                    :    0
%              Number of atoms          :    4 (   4 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   5 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%------ Negative definition of equality_sorted 
fof(lit_def,axiom,(
    ! [X0_0,X0,X1] :
      ( ~ equality_sorted(X0_0,X0,X1)
    <=> $false ) )).

%------ Positive definition of r1_xboole_0 
fof(lit_def_001,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> $false ) )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:44:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.49/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.49/0.98  
% 0.49/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.49/0.98  
% 0.49/0.98  ------  iProver source info
% 0.49/0.98  
% 0.49/0.98  git: date: 2020-06-30 10:37:57 +0100
% 0.49/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.49/0.98  git: non_committed_changes: false
% 0.49/0.98  git: last_make_outside_of_git: false
% 0.49/0.98  
% 0.49/0.98  ------ 
% 0.49/0.98  
% 0.49/0.98  ------ Input Options
% 0.49/0.98  
% 0.49/0.98  --out_options                           all
% 0.49/0.98  --tptp_safe_out                         true
% 0.49/0.98  --problem_path                          ""
% 0.49/0.98  --include_path                          ""
% 0.49/0.98  --clausifier                            res/vclausify_rel
% 0.49/0.98  --clausifier_options                    --mode clausify
% 0.49/0.98  --stdin                                 false
% 0.49/0.98  --stats_out                             all
% 0.49/0.98  
% 0.49/0.98  ------ General Options
% 0.49/0.98  
% 0.49/0.98  --fof                                   false
% 0.49/0.98  --time_out_real                         305.
% 0.49/0.98  --time_out_virtual                      -1.
% 0.49/0.98  --symbol_type_check                     false
% 0.49/0.98  --clausify_out                          false
% 0.49/0.98  --sig_cnt_out                           false
% 0.49/0.98  --trig_cnt_out                          false
% 0.49/0.98  --trig_cnt_out_tolerance                1.
% 0.49/0.98  --trig_cnt_out_sk_spl                   false
% 0.49/0.98  --abstr_cl_out                          false
% 0.49/0.98  
% 0.49/0.98  ------ Global Options
% 0.49/0.98  
% 0.49/0.98  --schedule                              default
% 0.49/0.98  --add_important_lit                     false
% 0.49/0.98  --prop_solver_per_cl                    1000
% 0.49/0.98  --min_unsat_core                        false
% 0.49/0.98  --soft_assumptions                      false
% 0.49/0.98  --soft_lemma_size                       3
% 0.49/0.98  --prop_impl_unit_size                   0
% 0.49/0.98  --prop_impl_unit                        []
% 0.49/0.98  --share_sel_clauses                     true
% 0.49/0.98  --reset_solvers                         false
% 0.49/0.98  --bc_imp_inh                            [conj_cone]
% 0.49/0.98  --conj_cone_tolerance                   3.
% 0.49/0.98  --extra_neg_conj                        none
% 0.49/0.98  --large_theory_mode                     true
% 0.49/0.98  --prolific_symb_bound                   200
% 0.49/0.98  --lt_threshold                          2000
% 0.49/0.98  --clause_weak_htbl                      true
% 0.49/0.98  --gc_record_bc_elim                     false
% 0.49/0.98  
% 0.49/0.98  ------ Preprocessing Options
% 0.49/0.98  
% 0.49/0.98  --preprocessing_flag                    true
% 0.49/0.98  --time_out_prep_mult                    0.1
% 0.49/0.98  --splitting_mode                        input
% 0.49/0.98  --splitting_grd                         true
% 0.49/0.98  --splitting_cvd                         false
% 0.49/0.98  --splitting_cvd_svl                     false
% 0.49/0.98  --splitting_nvd                         32
% 0.49/0.98  --sub_typing                            true
% 0.49/0.98  --prep_gs_sim                           true
% 0.49/0.98  --prep_unflatten                        true
% 0.49/0.98  --prep_res_sim                          true
% 0.49/0.98  --prep_upred                            true
% 0.49/0.98  --prep_sem_filter                       exhaustive
% 0.49/0.98  --prep_sem_filter_out                   false
% 0.49/0.98  --pred_elim                             true
% 0.49/0.98  --res_sim_input                         true
% 0.49/0.98  --eq_ax_congr_red                       true
% 0.49/0.98  --pure_diseq_elim                       true
% 0.49/0.98  --brand_transform                       false
% 0.49/0.98  --non_eq_to_eq                          false
% 0.49/0.98  --prep_def_merge                        true
% 0.49/0.98  --prep_def_merge_prop_impl              false
% 0.49/0.98  --prep_def_merge_mbd                    true
% 0.49/0.98  --prep_def_merge_tr_red                 false
% 0.49/0.98  --prep_def_merge_tr_cl                  false
% 0.49/0.98  --smt_preprocessing                     true
% 0.49/0.98  --smt_ac_axioms                         fast
% 0.49/0.98  --preprocessed_out                      false
% 0.49/0.98  --preprocessed_stats                    false
% 0.49/0.98  
% 0.49/0.98  ------ Abstraction refinement Options
% 0.49/0.98  
% 0.49/0.98  --abstr_ref                             []
% 0.49/0.98  --abstr_ref_prep                        false
% 0.49/0.98  --abstr_ref_until_sat                   false
% 0.49/0.98  --abstr_ref_sig_restrict                funpre
% 0.49/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.49/0.98  --abstr_ref_under                       []
% 0.49/0.98  
% 0.49/0.98  ------ SAT Options
% 0.49/0.98  
% 0.49/0.98  --sat_mode                              false
% 0.49/0.98  --sat_fm_restart_options                ""
% 0.49/0.98  --sat_gr_def                            false
% 0.49/0.98  --sat_epr_types                         true
% 0.49/0.98  --sat_non_cyclic_types                  false
% 0.49/0.98  --sat_finite_models                     false
% 0.49/0.98  --sat_fm_lemmas                         false
% 0.49/0.98  --sat_fm_prep                           false
% 0.49/0.98  --sat_fm_uc_incr                        true
% 0.49/0.98  --sat_out_model                         small
% 0.49/0.98  --sat_out_clauses                       false
% 0.49/0.98  
% 0.49/0.98  ------ QBF Options
% 0.49/0.98  
% 0.49/0.98  --qbf_mode                              false
% 0.49/0.98  --qbf_elim_univ                         false
% 0.49/0.98  --qbf_dom_inst                          none
% 0.49/0.98  --qbf_dom_pre_inst                      false
% 0.49/0.98  --qbf_sk_in                             false
% 0.49/0.98  --qbf_pred_elim                         true
% 0.49/0.98  --qbf_split                             512
% 0.49/0.98  
% 0.49/0.98  ------ BMC1 Options
% 0.49/0.98  
% 0.49/0.98  --bmc1_incremental                      false
% 0.49/0.98  --bmc1_axioms                           reachable_all
% 0.49/0.98  --bmc1_min_bound                        0
% 0.49/0.98  --bmc1_max_bound                        -1
% 0.49/0.98  --bmc1_max_bound_default                -1
% 0.49/0.98  --bmc1_symbol_reachability              true
% 0.49/0.98  --bmc1_property_lemmas                  false
% 0.49/0.98  --bmc1_k_induction                      false
% 0.49/0.98  --bmc1_non_equiv_states                 false
% 0.49/0.98  --bmc1_deadlock                         false
% 0.49/0.98  --bmc1_ucm                              false
% 0.49/0.98  --bmc1_add_unsat_core                   none
% 0.49/0.98  --bmc1_unsat_core_children              false
% 0.49/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.49/0.98  --bmc1_out_stat                         full
% 0.49/0.98  --bmc1_ground_init                      false
% 0.49/0.98  --bmc1_pre_inst_next_state              false
% 0.49/0.98  --bmc1_pre_inst_state                   false
% 0.49/0.98  --bmc1_pre_inst_reach_state             false
% 0.49/0.98  --bmc1_out_unsat_core                   false
% 0.49/0.98  --bmc1_aig_witness_out                  false
% 0.49/0.98  --bmc1_verbose                          false
% 0.49/0.98  --bmc1_dump_clauses_tptp                false
% 0.49/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.49/0.98  --bmc1_dump_file                        -
% 0.49/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.49/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.49/0.98  --bmc1_ucm_extend_mode                  1
% 0.49/0.98  --bmc1_ucm_init_mode                    2
% 0.49/0.98  --bmc1_ucm_cone_mode                    none
% 0.49/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.49/0.98  --bmc1_ucm_relax_model                  4
% 0.49/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.49/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.49/0.98  --bmc1_ucm_layered_model                none
% 0.49/0.98  --bmc1_ucm_max_lemma_size               10
% 0.49/0.98  
% 0.49/0.98  ------ AIG Options
% 0.49/0.98  
% 0.49/0.98  --aig_mode                              false
% 0.49/0.98  
% 0.49/0.98  ------ Instantiation Options
% 0.49/0.98  
% 0.49/0.98  --instantiation_flag                    true
% 0.49/0.98  --inst_sos_flag                         false
% 0.49/0.98  --inst_sos_phase                        true
% 0.49/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.49/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.49/0.98  --inst_lit_sel_side                     num_symb
% 0.49/0.98  --inst_solver_per_active                1400
% 0.49/0.98  --inst_solver_calls_frac                1.
% 0.49/0.98  --inst_passive_queue_type               priority_queues
% 0.49/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.49/0.98  --inst_passive_queues_freq              [25;2]
% 0.49/0.98  --inst_dismatching                      true
% 0.49/0.98  --inst_eager_unprocessed_to_passive     true
% 0.49/0.98  --inst_prop_sim_given                   true
% 0.49/0.98  --inst_prop_sim_new                     false
% 0.49/0.98  --inst_subs_new                         false
% 0.49/0.98  --inst_eq_res_simp                      false
% 0.49/0.98  --inst_subs_given                       false
% 0.49/0.98  --inst_orphan_elimination               true
% 0.49/0.98  --inst_learning_loop_flag               true
% 0.49/0.98  --inst_learning_start                   3000
% 0.49/0.98  --inst_learning_factor                  2
% 0.49/0.98  --inst_start_prop_sim_after_learn       3
% 0.49/0.98  --inst_sel_renew                        solver
% 0.49/0.98  --inst_lit_activity_flag                true
% 0.49/0.98  --inst_restr_to_given                   false
% 0.49/0.98  --inst_activity_threshold               500
% 0.49/0.98  --inst_out_proof                        true
% 0.49/0.98  
% 0.49/0.98  ------ Resolution Options
% 0.49/0.98  
% 0.49/0.98  --resolution_flag                       true
% 0.49/0.98  --res_lit_sel                           adaptive
% 0.49/0.98  --res_lit_sel_side                      none
% 0.49/0.98  --res_ordering                          kbo
% 0.49/0.98  --res_to_prop_solver                    active
% 0.49/0.98  --res_prop_simpl_new                    false
% 0.49/0.98  --res_prop_simpl_given                  true
% 0.49/0.98  --res_passive_queue_type                priority_queues
% 0.49/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.49/0.98  --res_passive_queues_freq               [15;5]
% 0.49/0.98  --res_forward_subs                      full
% 0.49/0.98  --res_backward_subs                     full
% 0.49/0.98  --res_forward_subs_resolution           true
% 0.49/0.98  --res_backward_subs_resolution          true
% 0.49/0.98  --res_orphan_elimination                true
% 0.49/0.98  --res_time_limit                        2.
% 0.49/0.98  --res_out_proof                         true
% 0.49/0.98  
% 0.49/0.98  ------ Superposition Options
% 0.49/0.98  
% 0.49/0.98  --superposition_flag                    true
% 0.49/0.98  --sup_passive_queue_type                priority_queues
% 0.49/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.49/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.49/0.98  --demod_completeness_check              fast
% 0.49/0.98  --demod_use_ground                      true
% 0.49/0.98  --sup_to_prop_solver                    passive
% 0.49/0.98  --sup_prop_simpl_new                    true
% 0.49/0.98  --sup_prop_simpl_given                  true
% 0.49/0.98  --sup_fun_splitting                     false
% 0.49/0.98  --sup_smt_interval                      50000
% 0.49/0.98  
% 0.49/0.98  ------ Superposition Simplification Setup
% 0.49/0.98  
% 0.49/0.98  --sup_indices_passive                   []
% 0.49/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.49/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.49/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.49/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.49/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.49/0.98  --sup_full_bw                           [BwDemod]
% 0.49/0.98  --sup_immed_triv                        [TrivRules]
% 0.49/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.49/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.49/0.98  --sup_immed_bw_main                     []
% 0.49/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.49/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.49/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.49/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.49/0.98  
% 0.49/0.98  ------ Combination Options
% 0.49/0.98  
% 0.49/0.98  --comb_res_mult                         3
% 0.49/0.98  --comb_sup_mult                         2
% 0.49/0.98  --comb_inst_mult                        10
% 0.49/0.98  
% 0.49/0.98  ------ Debug Options
% 0.49/0.98  
% 0.49/0.98  --dbg_backtrace                         false
% 0.49/0.98  --dbg_dump_prop_clauses                 false
% 0.49/0.98  --dbg_dump_prop_clauses_file            -
% 0.49/0.98  --dbg_out_stat                          false
% 0.49/0.98  ------ Parsing...
% 0.49/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.49/0.98  
% 0.49/0.98  ------ Preprocessing... sf_s  rm: 12 0s  sf_e  pe_s  pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 0.49/0.98  
% 0.49/0.98  ------ Preprocessing...------  preprocesses with Option_epr_horn
% 0.49/0.98   gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.49/0.98  ------ Proving...
% 0.49/0.98  ------ Problem Properties 
% 0.49/0.98  
% 0.49/0.98  
% 0.49/0.98  clauses                                 0
% 0.49/0.98  conjectures                             0
% 0.49/0.98  EPR                                     0
% 0.49/0.98  Horn                                    0
% 0.49/0.98  unary                                   0
% 0.49/0.98  binary                                  0
% 0.49/0.98  lits                                    0
% 0.49/0.98  lits eq                                 0
% 0.49/0.98  fd_pure                                 0
% 0.49/0.98  fd_pseudo                               0
% 0.49/0.98  fd_cond                                 0
% 0.49/0.98  fd_pseudo_cond                          0
% 0.49/0.98  AC symbols                              0
% 0.49/0.98  
% 0.49/0.98  ------ Schedule EPR Horn non eq is on
% 0.49/0.98  
% 0.49/0.98  ------ no conjectures: strip conj schedule 
% 0.49/0.98  
% 0.49/0.98  ------ no equalities: superposition off 
% 0.49/0.98  
% 0.49/0.98  ------ pure equality problem: resolution off 
% 0.49/0.98  
% 0.49/0.98  ------ Option_epr_horn stripped conjectures Time Limit: Unbounded
% 0.49/0.98  
% 0.49/0.98  
% 0.49/0.98  ------ 
% 0.49/0.98  Current options:
% 0.49/0.98  ------ 
% 0.49/0.98  
% 0.49/0.98  ------ Input Options
% 0.49/0.98  
% 0.49/0.98  --out_options                           all
% 0.49/0.98  --tptp_safe_out                         true
% 0.49/0.98  --problem_path                          ""
% 0.49/0.98  --include_path                          ""
% 0.49/0.98  --clausifier                            res/vclausify_rel
% 0.49/0.98  --clausifier_options                    --mode clausify
% 0.49/0.98  --stdin                                 false
% 0.49/0.98  --stats_out                             all
% 0.49/0.98  
% 0.49/0.98  ------ General Options
% 0.49/0.98  
% 0.49/0.98  --fof                                   false
% 0.49/0.98  --time_out_real                         305.
% 0.49/0.98  --time_out_virtual                      -1.
% 0.49/0.98  --symbol_type_check                     false
% 0.49/0.98  --clausify_out                          false
% 0.49/0.98  --sig_cnt_out                           false
% 0.49/0.98  --trig_cnt_out                          false
% 0.49/0.98  --trig_cnt_out_tolerance                1.
% 0.49/0.98  --trig_cnt_out_sk_spl                   false
% 0.49/0.98  --abstr_cl_out                          false
% 0.49/0.98  
% 0.49/0.98  ------ Global Options
% 0.49/0.98  
% 0.49/0.98  --schedule                              default
% 0.49/0.98  --add_important_lit                     false
% 0.49/0.98  --prop_solver_per_cl                    1000
% 0.49/0.98  --min_unsat_core                        false
% 0.49/0.98  --soft_assumptions                      false
% 0.49/0.98  --soft_lemma_size                       3
% 0.49/0.98  --prop_impl_unit_size                   0
% 0.49/0.98  --prop_impl_unit                        []
% 0.49/0.98  --share_sel_clauses                     true
% 0.49/0.98  --reset_solvers                         false
% 0.49/0.98  --bc_imp_inh                            []
% 0.49/0.98  --conj_cone_tolerance                   1.5
% 0.49/0.98  --extra_neg_conj                        none
% 0.49/0.98  --large_theory_mode                     true
% 0.49/0.98  --prolific_symb_bound                   500
% 0.49/0.98  --lt_threshold                          2000
% 0.49/0.98  --clause_weak_htbl                      true
% 0.49/0.98  --gc_record_bc_elim                     false
% 0.49/0.98  
% 0.49/0.98  ------ Preprocessing Options
% 0.49/0.98  
% 0.49/0.98  --preprocessing_flag                    true
% 0.49/0.98  --time_out_prep_mult                    0.8
% 0.49/0.98  --splitting_mode                        none
% 0.49/0.98  --splitting_grd                         false
% 0.49/0.98  --splitting_cvd                         false
% 0.49/0.98  --splitting_cvd_svl                     false
% 0.49/0.98  --splitting_nvd                         128
% 0.49/0.98  --sub_typing                            true
% 0.49/0.98  --prep_gs_sim                           true
% 0.49/0.98  --prep_unflatten                        true
% 0.49/0.98  --prep_res_sim                          false
% 0.49/0.98  --prep_upred                            true
% 0.49/0.98  --prep_sem_filter                       exhaustive
% 0.49/0.98  --prep_sem_filter_out                   false
% 0.49/0.98  --pred_elim                             false
% 0.49/0.98  --res_sim_input                         false
% 0.49/0.98  --eq_ax_congr_red                       true
% 0.49/0.98  --pure_diseq_elim                       true
% 0.49/0.98  --brand_transform                       false
% 0.49/0.98  --non_eq_to_eq                          false
% 0.49/0.98  --prep_def_merge                        true
% 0.49/0.98  --prep_def_merge_prop_impl              false
% 0.49/0.98  --prep_def_merge_mbd                    true
% 0.49/0.98  --prep_def_merge_tr_red                 false
% 0.49/0.98  --prep_def_merge_tr_cl                  false
% 0.49/0.98  --smt_preprocessing                     true
% 0.49/0.98  --smt_ac_axioms                         fast
% 0.49/0.98  --preprocessed_out                      false
% 0.49/0.98  --preprocessed_stats                    false
% 0.49/0.98  
% 0.49/0.98  ------ Abstraction refinement Options
% 0.49/0.98  
% 0.49/0.98  --abstr_ref                             []
% 0.49/0.98  --abstr_ref_prep                        false
% 0.49/0.98  --abstr_ref_until_sat                   false
% 0.49/0.98  --abstr_ref_sig_restrict                funpre
% 0.49/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 0.49/0.98  --abstr_ref_under                       []
% 0.49/0.98  
% 0.49/0.98  ------ SAT Options
% 0.49/0.98  
% 0.49/0.98  --sat_mode                              false
% 0.49/0.98  --sat_fm_restart_options                ""
% 0.49/0.98  --sat_gr_def                            false
% 0.49/0.98  --sat_epr_types                         true
% 0.49/0.98  --sat_non_cyclic_types                  false
% 0.49/0.98  --sat_finite_models                     false
% 0.49/0.98  --sat_fm_lemmas                         false
% 0.49/0.98  --sat_fm_prep                           false
% 0.49/0.98  --sat_fm_uc_incr                        true
% 0.49/0.98  --sat_out_model                         small
% 0.49/0.98  --sat_out_clauses                       false
% 0.49/0.98  
% 0.49/0.98  ------ QBF Options
% 0.49/0.98  
% 0.49/0.98  --qbf_mode                              false
% 0.49/0.98  --qbf_elim_univ                         false
% 0.49/0.98  --qbf_dom_inst                          none
% 0.49/0.98  --qbf_dom_pre_inst                      false
% 0.49/0.98  --qbf_sk_in                             false
% 0.49/0.98  --qbf_pred_elim                         true
% 0.49/0.98  --qbf_split                             512
% 0.49/0.98  
% 0.49/0.98  ------ BMC1 Options
% 0.49/0.98  
% 0.49/0.98  --bmc1_incremental                      false
% 0.49/0.98  --bmc1_axioms                           reachable_all
% 0.49/0.98  --bmc1_min_bound                        0
% 0.49/0.98  --bmc1_max_bound                        -1
% 0.49/0.98  --bmc1_max_bound_default                -1
% 0.49/0.98  --bmc1_symbol_reachability              true
% 0.49/0.98  --bmc1_property_lemmas                  false
% 0.49/0.98  --bmc1_k_induction                      false
% 0.49/0.98  --bmc1_non_equiv_states                 false
% 0.49/0.98  --bmc1_deadlock                         false
% 0.49/0.98  --bmc1_ucm                              false
% 0.49/0.98  --bmc1_add_unsat_core                   none
% 0.49/0.98  --bmc1_unsat_core_children              false
% 0.49/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 0.49/0.98  --bmc1_out_stat                         full
% 0.49/0.98  --bmc1_ground_init                      false
% 0.49/0.98  --bmc1_pre_inst_next_state              false
% 0.49/0.98  --bmc1_pre_inst_state                   false
% 0.49/0.98  --bmc1_pre_inst_reach_state             false
% 0.49/0.98  --bmc1_out_unsat_core                   false
% 0.49/0.98  --bmc1_aig_witness_out                  false
% 0.49/0.98  --bmc1_verbose                          false
% 0.49/0.98  --bmc1_dump_clauses_tptp                false
% 0.49/0.98  --bmc1_dump_unsat_core_tptp             false
% 0.49/0.98  --bmc1_dump_file                        -
% 0.49/0.98  --bmc1_ucm_expand_uc_limit              128
% 0.49/0.98  --bmc1_ucm_n_expand_iterations          6
% 0.49/0.98  --bmc1_ucm_extend_mode                  1
% 0.49/0.98  --bmc1_ucm_init_mode                    2
% 0.49/0.98  --bmc1_ucm_cone_mode                    none
% 0.49/0.98  --bmc1_ucm_reduced_relation_type        0
% 0.49/0.98  --bmc1_ucm_relax_model                  4
% 0.49/0.98  --bmc1_ucm_full_tr_after_sat            true
% 0.49/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 0.49/0.98  --bmc1_ucm_layered_model                none
% 0.49/0.98  --bmc1_ucm_max_lemma_size               10
% 0.49/0.98  
% 0.49/0.98  ------ AIG Options
% 0.49/0.98  
% 0.49/0.98  --aig_mode                              false
% 0.49/0.98  
% 0.49/0.98  ------ Instantiation Options
% 0.49/0.98  
% 0.49/0.98  --instantiation_flag                    true
% 0.49/0.98  --inst_sos_flag                         false
% 0.49/0.98  --inst_sos_phase                        true
% 0.49/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.49/0.98  --inst_lit_sel                          [+prop;-num_symb]
% 0.49/0.98  --inst_lit_sel_side                     num_symb
% 0.49/0.98  --inst_solver_per_active                100
% 0.49/0.98  --inst_solver_calls_frac                1.
% 0.49/0.98  --inst_passive_queue_type               priority_queues
% 0.49/0.98  --inst_passive_queues                   [[+ground;+num_symb;+min_def_symb];[-num_lits;+age;+conj_non_prolific_symb]]
% 0.49/0.98  --inst_passive_queues_freq              [1000;5]
% 0.49/0.98  --inst_dismatching                      false
% 0.49/0.98  --inst_eager_unprocessed_to_passive     false
% 0.49/0.98  --inst_prop_sim_given                   false
% 0.49/0.98  --inst_prop_sim_new                     true
% 0.49/0.98  --inst_subs_new                         false
% 0.49/0.98  --inst_eq_res_simp                      false
% 0.49/0.98  --inst_subs_given                       false
% 0.49/0.98  --inst_orphan_elimination               false
% 0.49/0.98  --inst_learning_loop_flag               true
% 0.49/0.98  --inst_learning_start                   3000
% 0.49/0.98  --inst_learning_factor                  4
% 0.49/0.98  --inst_start_prop_sim_after_learn       0
% 0.49/0.98  --inst_sel_renew                        solver
% 0.49/0.98  --inst_lit_activity_flag                true
% 0.49/0.98  --inst_restr_to_given                   true
% 0.49/0.98  --inst_activity_threshold               10000
% 0.49/0.98  --inst_out_proof                        true
% 0.49/0.98  
% 0.49/0.98  ------ Resolution Options
% 0.49/0.98  
% 0.49/0.98  --resolution_flag                       false
% 0.49/0.98  --res_lit_sel                           neg_min
% 0.49/0.98  --res_lit_sel_side                      none
% 0.49/0.98  --res_ordering                          kbo
% 0.49/0.98  --res_to_prop_solver                    active
% 0.49/0.98  --res_prop_simpl_new                    false
% 0.49/0.98  --res_prop_simpl_given                  true
% 0.49/0.98  --res_passive_queue_type                priority_queues
% 0.49/0.98  --res_passive_queues                    [[+conj_non_prolific_symb;-num_symb;-num_symb];[+age;-num_symb]]
% 0.49/0.98  --res_passive_queues_freq               [10;5]
% 0.49/0.98  --res_forward_subs                      subset_subsumption
% 0.49/0.98  --res_backward_subs                     subset_subsumption
% 0.49/0.98  --res_forward_subs_resolution           false
% 0.49/0.98  --res_backward_subs_resolution          false
% 0.49/0.98  --res_orphan_elimination                true
% 0.49/0.98  --res_time_limit                        2.
% 0.49/0.98  --res_out_proof                         true
% 0.49/0.98  
% 0.49/0.98  ------ Superposition Options
% 0.49/0.98  
% 0.49/0.98  --superposition_flag                    false
% 0.49/0.98  --sup_passive_queue_type                priority_queues
% 0.49/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.49/0.98  --sup_passive_queues_freq               [8;1;4]
% 0.49/0.98  --demod_completeness_check              fast
% 0.49/0.98  --demod_use_ground                      true
% 0.49/0.98  --sup_to_prop_solver                    passive
% 0.49/0.98  --sup_prop_simpl_new                    true
% 0.49/0.98  --sup_prop_simpl_given                  true
% 0.49/0.98  --sup_fun_splitting                     false
% 0.49/0.98  --sup_smt_interval                      50000
% 0.49/0.98  
% 0.49/0.98  ------ Superposition Simplification Setup
% 0.49/0.98  
% 0.49/0.98  --sup_indices_passive                   []
% 0.49/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.49/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.49/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.49/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 0.49/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.49/0.98  --sup_full_bw                           [BwDemod]
% 0.49/0.98  --sup_immed_triv                        [TrivRules]
% 0.49/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.49/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.49/0.98  --sup_immed_bw_main                     []
% 0.49/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.49/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.49/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.49/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.49/0.98  
% 0.49/0.98  ------ Combination Options
% 0.49/0.98  
% 0.49/0.98  --comb_res_mult                         10
% 0.49/0.98  --comb_sup_mult                         2
% 0.49/0.98  --comb_inst_mult                        3
% 0.49/0.98  
% 0.49/0.98  ------ Debug Options
% 0.49/0.98  
% 0.49/0.98  --dbg_backtrace                         false
% 0.49/0.98  --dbg_dump_prop_clauses                 false
% 0.49/0.98  --dbg_dump_prop_clauses_file            -
% 0.49/0.98  --dbg_out_stat                          false
% 0.49/0.98  
% 0.49/0.98  
% 0.49/0.98  
% 0.49/0.98  
% 0.49/0.98  ------ Proving...
% 0.49/0.98  
% 0.49/0.98  
% 0.49/0.98  % SZS status CounterSatisfiable for theBenchmark.p
% 0.49/0.98  
% 0.49/0.98  ------ Building Model...Done
% 0.49/0.98  
% 0.49/0.98  %------ The model is defined over ground terms (initial term algebra).
% 0.49/0.98  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 0.49/0.98  %------ where \phi is a formula over the term algebra.
% 0.49/0.98  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 0.49/0.98  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 0.49/0.98  %------ See help for --sat_out_model for different model outputs.
% 0.49/0.98  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 0.49/0.98  %------ where the first argument stands for the sort ($i in the unsorted case)
% 0.49/0.98  % SZS output start Model for theBenchmark.p
% 0.49/0.98  
% 0.49/0.98  %------ Negative definition of equality_sorted 
% 0.49/0.98  fof(lit_def,axiom,
% 0.49/0.98      (! [X0_0,X0,X1] : 
% 0.49/0.98        ( ~(equality_sorted(X0_0,X0,X1)) <=>
% 0.49/0.98            $false
% 0.49/0.98        )
% 0.49/0.98      )
% 0.49/0.98     ).
% 0.49/0.98  
% 0.49/0.98  %------ Positive definition of r1_xboole_0 
% 0.49/0.98  fof(lit_def,axiom,
% 0.49/0.98      (! [X0,X1] : 
% 0.49/0.98        ( r1_xboole_0(X0,X1) <=>
% 0.49/0.98            $false
% 0.49/0.98        )
% 0.49/0.98      )
% 0.49/0.98     ).
% 0.49/0.98  % SZS output end Model for theBenchmark.p
% 0.49/0.98  ------                               Statistics
% 0.49/0.98  
% 0.49/0.98  ------ General
% 0.49/0.98  
% 0.49/0.98  abstr_ref_over_cycles:                  0
% 0.49/0.98  abstr_ref_under_cycles:                 0
% 0.49/0.98  gc_basic_clause_elim:                   0
% 0.49/0.98  forced_gc_time:                         0
% 0.49/0.98  parsing_time:                           0.008
% 0.49/0.98  unif_index_cands_time:                  0.
% 0.49/0.98  unif_index_add_time:                    0.
% 0.49/0.98  orderings_time:                         0.
% 0.49/0.98  out_proof_time:                         0.
% 0.49/0.98  total_time:                             0.025
% 0.49/0.98  num_of_symbols:                         37
% 0.49/0.98  num_of_terms:                           184
% 0.49/0.98  
% 0.49/0.98  ------ Preprocessing
% 0.49/0.98  
% 0.49/0.98  num_of_splits:                          0
% 0.49/0.98  num_of_split_atoms:                     0
% 0.49/0.98  num_of_reused_defs:                     0
% 0.49/0.98  num_eq_ax_congr_red:                    0
% 0.49/0.98  num_of_sem_filtered_clauses:            5
% 0.49/0.98  num_of_subtypes:                        0
% 0.49/0.98  monotx_restored_types:                  0
% 0.49/0.98  sat_num_of_epr_types:                   0
% 0.49/0.98  sat_num_of_non_cyclic_types:            0
% 0.49/0.98  sat_guarded_non_collapsed_types:        0
% 0.49/0.98  num_pure_diseq_elim:                    0
% 0.49/0.98  simp_replaced_by:                       0
% 0.49/0.98  res_preprocessed:                       5
% 0.49/0.98  prep_upred:                             0
% 0.49/0.98  prep_unflattend:                        0
% 0.49/0.98  smt_new_axioms:                         0
% 0.49/0.98  pred_elim_cands:                        0
% 0.49/0.98  pred_elim:                              0
% 0.49/0.98  pred_elim_cl:                           0
% 0.49/0.98  pred_elim_cycles:                       0
% 0.49/0.98  merged_defs:                            2
% 0.49/0.98  merged_defs_ncl:                        0
% 0.49/0.98  bin_hyper_res:                          2
% 0.49/0.98  prep_cycles:                            2
% 0.49/0.98  pred_elim_time:                         0.
% 0.49/0.98  splitting_time:                         0.
% 0.49/0.98  sem_filter_time:                        0.
% 0.49/0.98  monotx_time:                            0.
% 0.49/0.98  subtype_inf_time:                       0.
% 0.49/0.98  
% 0.49/0.98  ------ Problem properties
% 0.49/0.98  
% 0.49/0.98  clauses:                                0
% 0.49/0.98  conjectures:                            0
% 0.49/0.98  epr:                                    0
% 0.49/0.98  horn:                                   0
% 0.49/0.98  ground:                                 0
% 0.49/0.98  unary:                                  0
% 0.49/0.98  binary:                                 0
% 0.49/0.98  lits:                                   0
% 0.49/0.98  lits_eq:                                0
% 0.49/0.98  fd_pure:                                0
% 0.49/0.98  fd_pseudo:                              0
% 0.49/0.98  fd_cond:                                0
% 0.49/0.98  fd_pseudo_cond:                         0
% 0.49/0.98  ac_symbols:                             0
% 0.49/0.98  
% 0.49/0.98  ------ Propositional Solver
% 0.49/0.98  
% 0.49/0.98  prop_solver_calls:                      12
% 0.49/0.98  prop_fast_solver_calls:                 18
% 0.49/0.98  smt_solver_calls:                       0
% 0.49/0.98  smt_fast_solver_calls:                  0
% 0.49/0.98  prop_num_of_clauses:                    12
% 0.49/0.98  prop_preprocess_simplified:             82
% 0.49/0.98  prop_fo_subsumed:                       0
% 0.49/0.98  prop_solver_time:                       0.
% 0.49/0.98  smt_solver_time:                        0.
% 0.49/0.98  smt_fast_solver_time:                   0.
% 0.49/0.98  prop_fast_solver_time:                  0.
% 0.49/0.98  prop_unsat_core_time:                   0.
% 0.49/0.98  
% 0.49/0.98  ------ QBF
% 0.49/0.98  
% 0.49/0.98  qbf_q_res:                              0
% 0.49/0.98  qbf_num_tautologies:                    0
% 0.49/0.98  qbf_prep_cycles:                        0
% 0.49/0.98  
% 0.49/0.98  ------ BMC1
% 0.49/0.98  
% 0.49/0.98  bmc1_current_bound:                     -1
% 0.49/0.98  bmc1_last_solved_bound:                 -1
% 0.49/0.98  bmc1_unsat_core_size:                   -1
% 0.49/0.98  bmc1_unsat_core_parents_size:           -1
% 0.49/0.98  bmc1_merge_next_fun:                    0
% 0.49/0.98  bmc1_unsat_core_clauses_time:           0.
% 0.49/0.98  
% 0.49/0.98  ------ Instantiation
% 0.49/0.98  
% 0.49/0.98  inst_num_of_clauses:                    0
% 0.49/0.98  inst_num_in_passive:                    0
% 0.49/0.98  inst_num_in_active:                     0
% 0.49/0.98  inst_num_in_unprocessed:                0
% 0.49/0.98  inst_num_of_loops:                      1
% 0.49/0.98  inst_num_of_learning_restarts:          0
% 0.49/0.98  inst_num_moves_active_passive:          0
% 0.49/0.98  inst_lit_activity:                      0
% 0.49/0.98  inst_lit_activity_moves:                0
% 0.49/0.98  inst_num_tautologies:                   0
% 0.49/0.98  inst_num_prop_implied:                  0
% 0.49/0.98  inst_num_existing_simplified:           0
% 0.49/0.98  inst_num_eq_res_simplified:             0
% 0.49/0.98  inst_num_child_elim:                    0
% 0.49/0.98  inst_num_of_dismatching_blockings:      0
% 0.49/0.98  inst_num_of_non_proper_insts:           0
% 0.49/0.98  inst_num_of_duplicates:                 0
% 0.49/0.98  inst_inst_num_from_inst_to_res:         0
% 0.49/0.98  inst_dismatching_checking_time:         0.
% 0.49/0.98  
% 0.49/0.98  ------ Resolution
% 0.49/0.98  
% 0.49/0.98  res_num_of_clauses:                     0
% 0.49/0.98  res_num_in_passive:                     0
% 0.49/0.98  res_num_in_active:                      0
% 0.49/0.98  res_num_of_loops:                       7
% 0.49/0.98  res_forward_subset_subsumed:            0
% 0.49/0.98  res_backward_subset_subsumed:           0
% 0.49/0.98  res_forward_subsumed:                   0
% 0.49/0.98  res_backward_subsumed:                  0
% 0.49/0.98  res_forward_subsumption_resolution:     0
% 0.49/0.98  res_backward_subsumption_resolution:    0
% 0.49/0.98  res_clause_to_clause_subsumption:       0
% 0.49/0.98  res_orphan_elimination:                 0
% 0.49/0.98  res_tautology_del:                      4
% 0.49/0.98  res_num_eq_res_simplified:              0
% 0.49/0.98  res_num_sel_changes:                    0
% 0.49/0.98  res_moves_from_active_to_pass:          0
% 0.49/0.98  
% 0.49/0.98  ------ Superposition
% 0.49/0.98  
% 0.49/0.98  sup_time_total:                         0.
% 0.49/0.98  sup_time_generating:                    0.
% 0.49/0.98  sup_time_sim_full:                      0.
% 0.49/0.98  sup_time_sim_immed:                     0.
% 0.49/0.98  
% 0.49/0.98  sup_num_of_clauses:                     0
% 0.49/0.98  sup_num_in_active:                      0
% 0.49/0.98  sup_num_in_passive:                     0
% 0.49/0.98  sup_num_of_loops:                       0
% 0.49/0.98  sup_fw_superposition:                   0
% 0.49/0.98  sup_bw_superposition:                   0
% 0.49/0.98  sup_immediate_simplified:               0
% 0.49/0.98  sup_given_eliminated:                   0
% 0.49/0.98  comparisons_done:                       0
% 0.49/0.98  comparisons_avoided:                    0
% 0.49/0.98  
% 0.49/0.98  ------ Simplifications
% 0.49/0.98  
% 0.49/0.98  
% 0.49/0.98  sim_fw_subset_subsumed:                 0
% 0.49/0.98  sim_bw_subset_subsumed:                 0
% 0.49/0.98  sim_fw_subsumed:                        0
% 0.49/0.98  sim_bw_subsumed:                        0
% 0.49/0.98  sim_fw_subsumption_res:                 0
% 0.49/0.98  sim_bw_subsumption_res:                 0
% 0.49/0.98  sim_tautology_del:                      0
% 0.49/0.98  sim_eq_tautology_del:                   0
% 0.49/0.98  sim_eq_res_simp:                        0
% 0.49/0.98  sim_fw_demodulated:                     0
% 0.49/0.98  sim_bw_demodulated:                     0
% 0.49/0.98  sim_light_normalised:                   0
% 0.49/0.98  sim_joinable_taut:                      0
% 0.49/0.98  sim_joinable_simp:                      0
% 0.49/0.98  sim_ac_normalised:                      0
% 0.49/0.98  sim_smt_subsumption:                    0
% 0.49/0.98  
%------------------------------------------------------------------------------
