%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:33:58 EST 2020

% Result     : CounterSatisfiable 0.58s
% Output     : Model 0.58s
% Verified   : 
% Statistics : Number of formulae       :    2 (   2 expanded)
%              Number of leaves         :    2 (   2 expanded)
%              Depth                    :    0
%              Number of atoms          :    4 (   4 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%------ Negative definition of equality_sorted 
fof(lit_def,axiom,(
    ! [X0_0,X0,X1] :
      ( ~ equality_sorted(X0_0,X0,X1)
    <=> $false ) )).

%------ Positive definition of v1_xboole_0 
fof(lit_def_001,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> $true ) )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.58/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.58/1.02  
% 0.58/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.58/1.02  
% 0.58/1.02  ------  iProver source info
% 0.58/1.02  
% 0.58/1.02  git: date: 2020-06-30 10:37:57 +0100
% 0.58/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.58/1.02  git: non_committed_changes: false
% 0.58/1.02  git: last_make_outside_of_git: false
% 0.58/1.02  
% 0.58/1.02  ------ 
% 0.58/1.02  
% 0.58/1.02  ------ Input Options
% 0.58/1.02  
% 0.58/1.02  --out_options                           all
% 0.58/1.02  --tptp_safe_out                         true
% 0.58/1.02  --problem_path                          ""
% 0.58/1.02  --include_path                          ""
% 0.58/1.02  --clausifier                            res/vclausify_rel
% 0.58/1.02  --clausifier_options                    --mode clausify
% 0.58/1.02  --stdin                                 false
% 0.58/1.02  --stats_out                             all
% 0.58/1.02  
% 0.58/1.02  ------ General Options
% 0.58/1.02  
% 0.58/1.02  --fof                                   false
% 0.58/1.02  --time_out_real                         305.
% 0.58/1.02  --time_out_virtual                      -1.
% 0.58/1.02  --symbol_type_check                     false
% 0.58/1.02  --clausify_out                          false
% 0.58/1.02  --sig_cnt_out                           false
% 0.58/1.02  --trig_cnt_out                          false
% 0.58/1.02  --trig_cnt_out_tolerance                1.
% 0.58/1.02  --trig_cnt_out_sk_spl                   false
% 0.58/1.02  --abstr_cl_out                          false
% 0.58/1.02  
% 0.58/1.02  ------ Global Options
% 0.58/1.02  
% 0.58/1.02  --schedule                              default
% 0.58/1.02  --add_important_lit                     false
% 0.58/1.02  --prop_solver_per_cl                    1000
% 0.58/1.02  --min_unsat_core                        false
% 0.58/1.02  --soft_assumptions                      false
% 0.58/1.02  --soft_lemma_size                       3
% 0.58/1.02  --prop_impl_unit_size                   0
% 0.58/1.02  --prop_impl_unit                        []
% 0.58/1.02  --share_sel_clauses                     true
% 0.58/1.02  --reset_solvers                         false
% 0.58/1.02  --bc_imp_inh                            [conj_cone]
% 0.58/1.02  --conj_cone_tolerance                   3.
% 0.58/1.02  --extra_neg_conj                        none
% 0.58/1.02  --large_theory_mode                     true
% 0.58/1.02  --prolific_symb_bound                   200
% 0.58/1.02  --lt_threshold                          2000
% 0.58/1.02  --clause_weak_htbl                      true
% 0.58/1.02  --gc_record_bc_elim                     false
% 0.58/1.02  
% 0.58/1.02  ------ Preprocessing Options
% 0.58/1.02  
% 0.58/1.02  --preprocessing_flag                    true
% 0.58/1.02  --time_out_prep_mult                    0.1
% 0.58/1.02  --splitting_mode                        input
% 0.58/1.02  --splitting_grd                         true
% 0.58/1.02  --splitting_cvd                         false
% 0.58/1.02  --splitting_cvd_svl                     false
% 0.58/1.02  --splitting_nvd                         32
% 0.58/1.02  --sub_typing                            true
% 0.58/1.02  --prep_gs_sim                           true
% 0.58/1.02  --prep_unflatten                        true
% 0.58/1.02  --prep_res_sim                          true
% 0.58/1.02  --prep_upred                            true
% 0.58/1.02  --prep_sem_filter                       exhaustive
% 0.58/1.02  --prep_sem_filter_out                   false
% 0.58/1.02  --pred_elim                             true
% 0.58/1.02  --res_sim_input                         true
% 0.58/1.02  --eq_ax_congr_red                       true
% 0.58/1.02  --pure_diseq_elim                       true
% 0.58/1.02  --brand_transform                       false
% 0.58/1.02  --non_eq_to_eq                          false
% 0.58/1.02  --prep_def_merge                        true
% 0.58/1.02  --prep_def_merge_prop_impl              false
% 0.58/1.02  --prep_def_merge_mbd                    true
% 0.58/1.02  --prep_def_merge_tr_red                 false
% 0.58/1.02  --prep_def_merge_tr_cl                  false
% 0.58/1.02  --smt_preprocessing                     true
% 0.58/1.02  --smt_ac_axioms                         fast
% 0.58/1.02  --preprocessed_out                      false
% 0.58/1.02  --preprocessed_stats                    false
% 0.58/1.02  
% 0.58/1.02  ------ Abstraction refinement Options
% 0.58/1.02  
% 0.58/1.02  --abstr_ref                             []
% 0.58/1.02  --abstr_ref_prep                        false
% 0.58/1.02  --abstr_ref_until_sat                   false
% 0.58/1.02  --abstr_ref_sig_restrict                funpre
% 0.58/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.58/1.02  --abstr_ref_under                       []
% 0.58/1.02  
% 0.58/1.02  ------ SAT Options
% 0.58/1.02  
% 0.58/1.02  --sat_mode                              false
% 0.58/1.02  --sat_fm_restart_options                ""
% 0.58/1.02  --sat_gr_def                            false
% 0.58/1.02  --sat_epr_types                         true
% 0.58/1.02  --sat_non_cyclic_types                  false
% 0.58/1.02  --sat_finite_models                     false
% 0.58/1.02  --sat_fm_lemmas                         false
% 0.58/1.02  --sat_fm_prep                           false
% 0.58/1.02  --sat_fm_uc_incr                        true
% 0.58/1.02  --sat_out_model                         small
% 0.58/1.02  --sat_out_clauses                       false
% 0.58/1.02  
% 0.58/1.02  ------ QBF Options
% 0.58/1.02  
% 0.58/1.02  --qbf_mode                              false
% 0.58/1.02  --qbf_elim_univ                         false
% 0.58/1.02  --qbf_dom_inst                          none
% 0.58/1.02  --qbf_dom_pre_inst                      false
% 0.58/1.02  --qbf_sk_in                             false
% 0.58/1.02  --qbf_pred_elim                         true
% 0.58/1.02  --qbf_split                             512
% 0.58/1.02  
% 0.58/1.02  ------ BMC1 Options
% 0.58/1.02  
% 0.58/1.02  --bmc1_incremental                      false
% 0.58/1.02  --bmc1_axioms                           reachable_all
% 0.58/1.02  --bmc1_min_bound                        0
% 0.58/1.02  --bmc1_max_bound                        -1
% 0.58/1.02  --bmc1_max_bound_default                -1
% 0.58/1.02  --bmc1_symbol_reachability              true
% 0.58/1.02  --bmc1_property_lemmas                  false
% 0.58/1.02  --bmc1_k_induction                      false
% 0.58/1.02  --bmc1_non_equiv_states                 false
% 0.58/1.02  --bmc1_deadlock                         false
% 0.58/1.02  --bmc1_ucm                              false
% 0.58/1.02  --bmc1_add_unsat_core                   none
% 0.58/1.02  --bmc1_unsat_core_children              false
% 0.58/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.58/1.02  --bmc1_out_stat                         full
% 0.58/1.02  --bmc1_ground_init                      false
% 0.58/1.02  --bmc1_pre_inst_next_state              false
% 0.58/1.02  --bmc1_pre_inst_state                   false
% 0.58/1.02  --bmc1_pre_inst_reach_state             false
% 0.58/1.02  --bmc1_out_unsat_core                   false
% 0.58/1.02  --bmc1_aig_witness_out                  false
% 0.58/1.02  --bmc1_verbose                          false
% 0.58/1.02  --bmc1_dump_clauses_tptp                false
% 0.58/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.58/1.02  --bmc1_dump_file                        -
% 0.58/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.58/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.58/1.02  --bmc1_ucm_extend_mode                  1
% 0.58/1.02  --bmc1_ucm_init_mode                    2
% 0.58/1.02  --bmc1_ucm_cone_mode                    none
% 0.58/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.58/1.02  --bmc1_ucm_relax_model                  4
% 0.58/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.58/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.58/1.02  --bmc1_ucm_layered_model                none
% 0.58/1.02  --bmc1_ucm_max_lemma_size               10
% 0.58/1.02  
% 0.58/1.02  ------ AIG Options
% 0.58/1.02  
% 0.58/1.02  --aig_mode                              false
% 0.58/1.02  
% 0.58/1.02  ------ Instantiation Options
% 0.58/1.02  
% 0.58/1.02  --instantiation_flag                    true
% 0.58/1.02  --inst_sos_flag                         false
% 0.58/1.02  --inst_sos_phase                        true
% 0.58/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.58/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.58/1.02  --inst_lit_sel_side                     num_symb
% 0.58/1.02  --inst_solver_per_active                1400
% 0.58/1.02  --inst_solver_calls_frac                1.
% 0.58/1.02  --inst_passive_queue_type               priority_queues
% 0.58/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.58/1.02  --inst_passive_queues_freq              [25;2]
% 0.58/1.02  --inst_dismatching                      true
% 0.58/1.02  --inst_eager_unprocessed_to_passive     true
% 0.58/1.02  --inst_prop_sim_given                   true
% 0.58/1.02  --inst_prop_sim_new                     false
% 0.58/1.02  --inst_subs_new                         false
% 0.58/1.02  --inst_eq_res_simp                      false
% 0.58/1.02  --inst_subs_given                       false
% 0.58/1.02  --inst_orphan_elimination               true
% 0.58/1.02  --inst_learning_loop_flag               true
% 0.58/1.02  --inst_learning_start                   3000
% 0.58/1.02  --inst_learning_factor                  2
% 0.58/1.02  --inst_start_prop_sim_after_learn       3
% 0.58/1.02  --inst_sel_renew                        solver
% 0.58/1.02  --inst_lit_activity_flag                true
% 0.58/1.02  --inst_restr_to_given                   false
% 0.58/1.02  --inst_activity_threshold               500
% 0.58/1.02  --inst_out_proof                        true
% 0.58/1.02  
% 0.58/1.02  ------ Resolution Options
% 0.58/1.02  
% 0.58/1.02  --resolution_flag                       true
% 0.58/1.02  --res_lit_sel                           adaptive
% 0.58/1.02  --res_lit_sel_side                      none
% 0.58/1.02  --res_ordering                          kbo
% 0.58/1.02  --res_to_prop_solver                    active
% 0.58/1.02  --res_prop_simpl_new                    false
% 0.58/1.02  --res_prop_simpl_given                  true
% 0.58/1.02  --res_passive_queue_type                priority_queues
% 0.58/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.58/1.02  --res_passive_queues_freq               [15;5]
% 0.58/1.02  --res_forward_subs                      full
% 0.58/1.02  --res_backward_subs                     full
% 0.58/1.02  --res_forward_subs_resolution           true
% 0.58/1.02  --res_backward_subs_resolution          true
% 0.58/1.02  --res_orphan_elimination                true
% 0.58/1.02  --res_time_limit                        2.
% 0.58/1.02  --res_out_proof                         true
% 0.58/1.02  
% 0.58/1.02  ------ Superposition Options
% 0.58/1.02  
% 0.58/1.02  --superposition_flag                    true
% 0.58/1.02  --sup_passive_queue_type                priority_queues
% 0.58/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.58/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.58/1.02  --demod_completeness_check              fast
% 0.58/1.02  --demod_use_ground                      true
% 0.58/1.02  --sup_to_prop_solver                    passive
% 0.58/1.02  --sup_prop_simpl_new                    true
% 0.58/1.02  --sup_prop_simpl_given                  true
% 0.58/1.02  --sup_fun_splitting                     false
% 0.58/1.02  --sup_smt_interval                      50000
% 0.58/1.02  
% 0.58/1.02  ------ Superposition Simplification Setup
% 0.58/1.02  
% 0.58/1.02  --sup_indices_passive                   []
% 0.58/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.58/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.58/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.58/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.58/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.58/1.02  --sup_full_bw                           [BwDemod]
% 0.58/1.02  --sup_immed_triv                        [TrivRules]
% 0.58/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.58/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.58/1.02  --sup_immed_bw_main                     []
% 0.58/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.58/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.58/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.58/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.58/1.02  
% 0.58/1.02  ------ Combination Options
% 0.58/1.02  
% 0.58/1.02  --comb_res_mult                         3
% 0.58/1.02  --comb_sup_mult                         2
% 0.58/1.02  --comb_inst_mult                        10
% 0.58/1.02  
% 0.58/1.02  ------ Debug Options
% 0.58/1.02  
% 0.58/1.02  --dbg_backtrace                         false
% 0.58/1.02  --dbg_dump_prop_clauses                 false
% 0.58/1.02  --dbg_dump_prop_clauses_file            -
% 0.58/1.02  --dbg_out_stat                          false
% 0.58/1.02  ------ Parsing...
% 0.58/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.58/1.02  
% 0.58/1.02  ------ Preprocessing... sf_s  rm: 11 0s  sf_e  pe_s  pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 0.58/1.02  
% 0.58/1.02  ------ Preprocessing...------  preprocesses with Option_epr_horn
% 0.58/1.02   gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.58/1.02  ------ Proving...
% 0.58/1.02  ------ Problem Properties 
% 0.58/1.02  
% 0.58/1.02  
% 0.58/1.02  clauses                                 0
% 0.58/1.02  conjectures                             0
% 0.58/1.02  EPR                                     0
% 0.58/1.02  Horn                                    0
% 0.58/1.02  unary                                   0
% 0.58/1.02  binary                                  0
% 0.58/1.02  lits                                    0
% 0.58/1.02  lits eq                                 0
% 0.58/1.02  fd_pure                                 0
% 0.58/1.02  fd_pseudo                               0
% 0.58/1.02  fd_cond                                 0
% 0.58/1.02  fd_pseudo_cond                          0
% 0.58/1.02  AC symbols                              0
% 0.58/1.02  
% 0.58/1.02  ------ Schedule EPR Horn non eq is on
% 0.58/1.02  
% 0.58/1.02  ------ no conjectures: strip conj schedule 
% 0.58/1.02  
% 0.58/1.02  ------ no equalities: superposition off 
% 0.58/1.02  
% 0.58/1.02  ------ pure equality problem: resolution off 
% 0.58/1.02  
% 0.58/1.02  ------ Option_epr_horn stripped conjectures Time Limit: Unbounded
% 0.58/1.02  
% 0.58/1.02  
% 0.58/1.02  ------ 
% 0.58/1.02  Current options:
% 0.58/1.02  ------ 
% 0.58/1.02  
% 0.58/1.02  ------ Input Options
% 0.58/1.02  
% 0.58/1.02  --out_options                           all
% 0.58/1.02  --tptp_safe_out                         true
% 0.58/1.02  --problem_path                          ""
% 0.58/1.02  --include_path                          ""
% 0.58/1.02  --clausifier                            res/vclausify_rel
% 0.58/1.02  --clausifier_options                    --mode clausify
% 0.58/1.02  --stdin                                 false
% 0.58/1.02  --stats_out                             all
% 0.58/1.02  
% 0.58/1.02  ------ General Options
% 0.58/1.02  
% 0.58/1.02  --fof                                   false
% 0.58/1.02  --time_out_real                         305.
% 0.58/1.02  --time_out_virtual                      -1.
% 0.58/1.02  --symbol_type_check                     false
% 0.58/1.02  --clausify_out                          false
% 0.58/1.02  --sig_cnt_out                           false
% 0.58/1.02  --trig_cnt_out                          false
% 0.58/1.02  --trig_cnt_out_tolerance                1.
% 0.58/1.02  --trig_cnt_out_sk_spl                   false
% 0.58/1.02  --abstr_cl_out                          false
% 0.58/1.02  
% 0.58/1.02  ------ Global Options
% 0.58/1.02  
% 0.58/1.02  --schedule                              default
% 0.58/1.02  --add_important_lit                     false
% 0.58/1.02  --prop_solver_per_cl                    1000
% 0.58/1.02  --min_unsat_core                        false
% 0.58/1.02  --soft_assumptions                      false
% 0.58/1.02  --soft_lemma_size                       3
% 0.58/1.02  --prop_impl_unit_size                   0
% 0.58/1.02  --prop_impl_unit                        []
% 0.58/1.02  --share_sel_clauses                     true
% 0.58/1.02  --reset_solvers                         false
% 0.58/1.02  --bc_imp_inh                            []
% 0.58/1.02  --conj_cone_tolerance                   1.5
% 0.58/1.02  --extra_neg_conj                        none
% 0.58/1.02  --large_theory_mode                     true
% 0.58/1.02  --prolific_symb_bound                   500
% 0.58/1.02  --lt_threshold                          2000
% 0.58/1.02  --clause_weak_htbl                      true
% 0.58/1.02  --gc_record_bc_elim                     false
% 0.58/1.02  
% 0.58/1.02  ------ Preprocessing Options
% 0.58/1.02  
% 0.58/1.02  --preprocessing_flag                    true
% 0.58/1.02  --time_out_prep_mult                    0.8
% 0.58/1.02  --splitting_mode                        none
% 0.58/1.02  --splitting_grd                         false
% 0.58/1.02  --splitting_cvd                         false
% 0.58/1.02  --splitting_cvd_svl                     false
% 0.58/1.02  --splitting_nvd                         128
% 0.58/1.02  --sub_typing                            true
% 0.58/1.02  --prep_gs_sim                           true
% 0.58/1.02  --prep_unflatten                        true
% 0.58/1.02  --prep_res_sim                          false
% 0.58/1.02  --prep_upred                            true
% 0.58/1.02  --prep_sem_filter                       exhaustive
% 0.58/1.02  --prep_sem_filter_out                   false
% 0.58/1.02  --pred_elim                             false
% 0.58/1.02  --res_sim_input                         false
% 0.58/1.02  --eq_ax_congr_red                       true
% 0.58/1.02  --pure_diseq_elim                       true
% 0.58/1.02  --brand_transform                       false
% 0.58/1.02  --non_eq_to_eq                          false
% 0.58/1.02  --prep_def_merge                        true
% 0.58/1.02  --prep_def_merge_prop_impl              false
% 0.58/1.02  --prep_def_merge_mbd                    true
% 0.58/1.02  --prep_def_merge_tr_red                 false
% 0.58/1.02  --prep_def_merge_tr_cl                  false
% 0.58/1.02  --smt_preprocessing                     true
% 0.58/1.02  --smt_ac_axioms                         fast
% 0.58/1.02  --preprocessed_out                      false
% 0.58/1.02  --preprocessed_stats                    false
% 0.58/1.02  
% 0.58/1.02  ------ Abstraction refinement Options
% 0.58/1.02  
% 0.58/1.02  --abstr_ref                             []
% 0.58/1.02  --abstr_ref_prep                        false
% 0.58/1.02  --abstr_ref_until_sat                   false
% 0.58/1.02  --abstr_ref_sig_restrict                funpre
% 0.58/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.58/1.02  --abstr_ref_under                       []
% 0.58/1.02  
% 0.58/1.02  ------ SAT Options
% 0.58/1.02  
% 0.58/1.02  --sat_mode                              false
% 0.58/1.02  --sat_fm_restart_options                ""
% 0.58/1.02  --sat_gr_def                            false
% 0.58/1.02  --sat_epr_types                         true
% 0.58/1.02  --sat_non_cyclic_types                  false
% 0.58/1.02  --sat_finite_models                     false
% 0.58/1.02  --sat_fm_lemmas                         false
% 0.58/1.02  --sat_fm_prep                           false
% 0.58/1.02  --sat_fm_uc_incr                        true
% 0.58/1.02  --sat_out_model                         small
% 0.58/1.02  --sat_out_clauses                       false
% 0.58/1.02  
% 0.58/1.02  ------ QBF Options
% 0.58/1.02  
% 0.58/1.02  --qbf_mode                              false
% 0.58/1.02  --qbf_elim_univ                         false
% 0.58/1.02  --qbf_dom_inst                          none
% 0.58/1.02  --qbf_dom_pre_inst                      false
% 0.58/1.02  --qbf_sk_in                             false
% 0.58/1.02  --qbf_pred_elim                         true
% 0.58/1.02  --qbf_split                             512
% 0.58/1.02  
% 0.58/1.02  ------ BMC1 Options
% 0.58/1.02  
% 0.58/1.02  --bmc1_incremental                      false
% 0.58/1.02  --bmc1_axioms                           reachable_all
% 0.58/1.02  --bmc1_min_bound                        0
% 0.58/1.02  --bmc1_max_bound                        -1
% 0.58/1.02  --bmc1_max_bound_default                -1
% 0.58/1.02  --bmc1_symbol_reachability              true
% 0.58/1.02  --bmc1_property_lemmas                  false
% 0.58/1.02  --bmc1_k_induction                      false
% 0.58/1.02  --bmc1_non_equiv_states                 false
% 0.58/1.02  --bmc1_deadlock                         false
% 0.58/1.02  --bmc1_ucm                              false
% 0.58/1.02  --bmc1_add_unsat_core                   none
% 0.58/1.02  --bmc1_unsat_core_children              false
% 0.58/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.58/1.02  --bmc1_out_stat                         full
% 0.58/1.02  --bmc1_ground_init                      false
% 0.58/1.02  --bmc1_pre_inst_next_state              false
% 0.58/1.02  --bmc1_pre_inst_state                   false
% 0.58/1.02  --bmc1_pre_inst_reach_state             false
% 0.58/1.02  --bmc1_out_unsat_core                   false
% 0.58/1.02  --bmc1_aig_witness_out                  false
% 0.58/1.02  --bmc1_verbose                          false
% 0.58/1.02  --bmc1_dump_clauses_tptp                false
% 0.58/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.58/1.02  --bmc1_dump_file                        -
% 0.58/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.58/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.58/1.02  --bmc1_ucm_extend_mode                  1
% 0.58/1.02  --bmc1_ucm_init_mode                    2
% 0.58/1.02  --bmc1_ucm_cone_mode                    none
% 0.58/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.58/1.02  --bmc1_ucm_relax_model                  4
% 0.58/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.58/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.58/1.02  --bmc1_ucm_layered_model                none
% 0.58/1.02  --bmc1_ucm_max_lemma_size               10
% 0.58/1.02  
% 0.58/1.02  ------ AIG Options
% 0.58/1.02  
% 0.58/1.02  --aig_mode                              false
% 0.58/1.02  
% 0.58/1.02  ------ Instantiation Options
% 0.58/1.02  
% 0.58/1.02  --instantiation_flag                    true
% 0.58/1.02  --inst_sos_flag                         false
% 0.58/1.02  --inst_sos_phase                        true
% 0.58/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.58/1.02  --inst_lit_sel                          [+prop;-num_symb]
% 0.58/1.02  --inst_lit_sel_side                     num_symb
% 0.58/1.02  --inst_solver_per_active                100
% 0.58/1.02  --inst_solver_calls_frac                1.
% 0.58/1.02  --inst_passive_queue_type               priority_queues
% 0.58/1.02  --inst_passive_queues                   [[+ground;+num_symb;+min_def_symb];[-num_lits;+age;+conj_non_prolific_symb]]
% 0.58/1.02  --inst_passive_queues_freq              [1000;5]
% 0.58/1.02  --inst_dismatching                      false
% 0.58/1.02  --inst_eager_unprocessed_to_passive     false
% 0.58/1.02  --inst_prop_sim_given                   false
% 0.58/1.02  --inst_prop_sim_new                     true
% 0.58/1.02  --inst_subs_new                         false
% 0.58/1.02  --inst_eq_res_simp                      false
% 0.58/1.02  --inst_subs_given                       false
% 0.58/1.02  --inst_orphan_elimination               false
% 0.58/1.02  --inst_learning_loop_flag               true
% 0.58/1.02  --inst_learning_start                   3000
% 0.58/1.02  --inst_learning_factor                  4
% 0.58/1.02  --inst_start_prop_sim_after_learn       0
% 0.58/1.02  --inst_sel_renew                        solver
% 0.58/1.02  --inst_lit_activity_flag                true
% 0.58/1.02  --inst_restr_to_given                   true
% 0.58/1.02  --inst_activity_threshold               10000
% 0.58/1.02  --inst_out_proof                        true
% 0.58/1.02  
% 0.58/1.02  ------ Resolution Options
% 0.58/1.02  
% 0.58/1.02  --resolution_flag                       false
% 0.58/1.02  --res_lit_sel                           neg_min
% 0.58/1.02  --res_lit_sel_side                      none
% 0.58/1.02  --res_ordering                          kbo
% 0.58/1.02  --res_to_prop_solver                    active
% 0.58/1.02  --res_prop_simpl_new                    false
% 0.58/1.02  --res_prop_simpl_given                  true
% 0.58/1.02  --res_passive_queue_type                priority_queues
% 0.58/1.02  --res_passive_queues                    [[+conj_non_prolific_symb;-num_symb;-num_symb];[+age;-num_symb]]
% 0.58/1.02  --res_passive_queues_freq               [10;5]
% 0.58/1.02  --res_forward_subs                      subset_subsumption
% 0.58/1.02  --res_backward_subs                     subset_subsumption
% 0.58/1.02  --res_forward_subs_resolution           false
% 0.58/1.02  --res_backward_subs_resolution          false
% 0.58/1.02  --res_orphan_elimination                true
% 0.58/1.02  --res_time_limit                        2.
% 0.58/1.02  --res_out_proof                         true
% 0.58/1.02  
% 0.58/1.02  ------ Superposition Options
% 0.58/1.02  
% 0.58/1.02  --superposition_flag                    false
% 0.58/1.02  --sup_passive_queue_type                priority_queues
% 0.58/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.58/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.58/1.02  --demod_completeness_check              fast
% 0.58/1.02  --demod_use_ground                      true
% 0.58/1.02  --sup_to_prop_solver                    passive
% 0.58/1.02  --sup_prop_simpl_new                    true
% 0.58/1.02  --sup_prop_simpl_given                  true
% 0.58/1.02  --sup_fun_splitting                     false
% 0.58/1.02  --sup_smt_interval                      50000
% 0.58/1.02  
% 0.58/1.02  ------ Superposition Simplification Setup
% 0.58/1.02  
% 0.58/1.02  --sup_indices_passive                   []
% 0.58/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.58/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.58/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.58/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.58/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.58/1.02  --sup_full_bw                           [BwDemod]
% 0.58/1.02  --sup_immed_triv                        [TrivRules]
% 0.58/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.58/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.58/1.02  --sup_immed_bw_main                     []
% 0.58/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.58/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.58/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.58/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.58/1.02  
% 0.58/1.02  ------ Combination Options
% 0.58/1.02  
% 0.58/1.02  --comb_res_mult                         10
% 0.58/1.02  --comb_sup_mult                         2
% 0.58/1.02  --comb_inst_mult                        3
% 0.58/1.02  
% 0.58/1.02  ------ Debug Options
% 0.58/1.02  
% 0.58/1.02  --dbg_backtrace                         false
% 0.58/1.02  --dbg_dump_prop_clauses                 false
% 0.58/1.02  --dbg_dump_prop_clauses_file            -
% 0.58/1.02  --dbg_out_stat                          false
% 0.58/1.02  
% 0.58/1.02  
% 0.58/1.02  
% 0.58/1.02  
% 0.58/1.02  ------ Proving...
% 0.58/1.02  
% 0.58/1.02  
% 0.58/1.02  % SZS status CounterSatisfiable for theBenchmark.p
% 0.58/1.02  
% 0.58/1.02  ------ Building Model...Done
% 0.58/1.02  
% 0.58/1.02  %------ The model is defined over ground terms (initial term algebra).
% 0.58/1.02  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 0.58/1.02  %------ where \phi is a formula over the term algebra.
% 0.58/1.02  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 0.58/1.02  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 0.58/1.02  %------ See help for --sat_out_model for different model outputs.
% 0.58/1.02  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 0.58/1.02  %------ where the first argument stands for the sort ($i in the unsorted case)
% 0.58/1.02  % SZS output start Model for theBenchmark.p
% 0.58/1.02  
% 0.58/1.02  %------ Negative definition of equality_sorted 
% 0.58/1.02  fof(lit_def,axiom,
% 0.58/1.02      (! [X0_0,X0,X1] : 
% 0.58/1.02        ( ~(equality_sorted(X0_0,X0,X1)) <=>
% 0.58/1.02            $false
% 0.58/1.02        )
% 0.58/1.02      )
% 0.58/1.02     ).
% 0.58/1.02  
% 0.58/1.02  %------ Positive definition of v1_xboole_0 
% 0.58/1.02  fof(lit_def,axiom,
% 0.58/1.02      (! [X0] : 
% 0.58/1.02        ( v1_xboole_0(X0) <=>
% 0.58/1.02            $true
% 0.58/1.02        )
% 0.58/1.02      )
% 0.58/1.02     ).
% 0.58/1.02  % SZS output end Model for theBenchmark.p
% 0.58/1.02  ------                               Statistics
% 0.58/1.02  
% 0.58/1.02  ------ General
% 0.58/1.02  
% 0.58/1.02  abstr_ref_over_cycles:                  0
% 0.58/1.02  abstr_ref_under_cycles:                 0
% 0.58/1.02  gc_basic_clause_elim:                   0
% 0.58/1.02  forced_gc_time:                         0
% 0.58/1.02  parsing_time:                           0.005
% 0.58/1.02  unif_index_cands_time:                  0.
% 0.58/1.02  unif_index_add_time:                    0.
% 0.58/1.02  orderings_time:                         0.
% 0.58/1.02  out_proof_time:                         0.
% 0.58/1.02  total_time:                             0.029
% 0.58/1.02  num_of_symbols:                         38
% 0.58/1.02  num_of_terms:                           145
% 0.58/1.02  
% 0.58/1.02  ------ Preprocessing
% 0.58/1.02  
% 0.58/1.02  num_of_splits:                          0
% 0.58/1.02  num_of_split_atoms:                     0
% 0.58/1.02  num_of_reused_defs:                     0
% 0.58/1.02  num_eq_ax_congr_red:                    0
% 0.58/1.02  num_of_sem_filtered_clauses:            4
% 0.58/1.02  num_of_subtypes:                        0
% 0.58/1.02  monotx_restored_types:                  0
% 0.58/1.02  sat_num_of_epr_types:                   0
% 0.58/1.02  sat_num_of_non_cyclic_types:            0
% 0.58/1.02  sat_guarded_non_collapsed_types:        0
% 0.58/1.02  num_pure_diseq_elim:                    0
% 0.58/1.02  simp_replaced_by:                       0
% 0.58/1.02  res_preprocessed:                       4
% 0.58/1.02  prep_upred:                             0
% 0.58/1.02  prep_unflattend:                        0
% 0.58/1.02  smt_new_axioms:                         0
% 0.58/1.02  pred_elim_cands:                        0
% 0.58/1.02  pred_elim:                              0
% 0.58/1.02  pred_elim_cl:                           0
% 0.58/1.02  pred_elim_cycles:                       0
% 0.58/1.02  merged_defs:                            0
% 0.58/1.02  merged_defs_ncl:                        0
% 0.58/1.02  bin_hyper_res:                          0
% 0.58/1.02  prep_cycles:                            2
% 0.58/1.02  pred_elim_time:                         0.
% 0.58/1.02  splitting_time:                         0.
% 0.58/1.02  sem_filter_time:                        0.
% 0.58/1.02  monotx_time:                            0.
% 0.58/1.02  subtype_inf_time:                       0.
% 0.58/1.02  
% 0.58/1.02  ------ Problem properties
% 0.58/1.02  
% 0.58/1.02  clauses:                                0
% 0.58/1.02  conjectures:                            0
% 0.58/1.02  epr:                                    0
% 0.58/1.02  horn:                                   0
% 0.58/1.02  ground:                                 0
% 0.58/1.02  unary:                                  0
% 0.58/1.02  binary:                                 0
% 0.58/1.02  lits:                                   0
% 0.58/1.02  lits_eq:                                0
% 0.58/1.02  fd_pure:                                0
% 0.58/1.02  fd_pseudo:                              0
% 0.58/1.02  fd_cond:                                0
% 0.58/1.02  fd_pseudo_cond:                         0
% 0.58/1.02  ac_symbols:                             0
% 0.58/1.02  
% 0.58/1.02  ------ Propositional Solver
% 0.58/1.02  
% 0.58/1.02  prop_solver_calls:                      12
% 0.58/1.02  prop_fast_solver_calls:                 10
% 0.58/1.02  smt_solver_calls:                       0
% 0.58/1.02  smt_fast_solver_calls:                  0
% 0.58/1.02  prop_num_of_clauses:                    9
% 0.58/1.02  prop_preprocess_simplified:             58
% 0.58/1.02  prop_fo_subsumed:                       0
% 0.58/1.02  prop_solver_time:                       0.
% 0.58/1.02  smt_solver_time:                        0.
% 0.58/1.02  smt_fast_solver_time:                   0.
% 0.58/1.02  prop_fast_solver_time:                  0.
% 0.58/1.02  prop_unsat_core_time:                   0.
% 0.58/1.02  
% 0.58/1.02  ------ QBF
% 0.58/1.02  
% 0.58/1.02  qbf_q_res:                              0
% 0.58/1.02  qbf_num_tautologies:                    0
% 0.58/1.02  qbf_prep_cycles:                        0
% 0.58/1.02  
% 0.58/1.02  ------ BMC1
% 0.58/1.02  
% 0.58/1.02  bmc1_current_bound:                     -1
% 0.58/1.02  bmc1_last_solved_bound:                 -1
% 0.58/1.02  bmc1_unsat_core_size:                   -1
% 0.58/1.02  bmc1_unsat_core_parents_size:           -1
% 0.58/1.02  bmc1_merge_next_fun:                    0
% 0.58/1.02  bmc1_unsat_core_clauses_time:           0.
% 0.58/1.02  
% 0.58/1.02  ------ Instantiation
% 0.58/1.02  
% 0.58/1.02  inst_num_of_clauses:                    0
% 0.58/1.02  inst_num_in_passive:                    0
% 0.58/1.02  inst_num_in_active:                     0
% 0.58/1.02  inst_num_in_unprocessed:                0
% 0.58/1.02  inst_num_of_loops:                      1
% 0.58/1.02  inst_num_of_learning_restarts:          0
% 0.58/1.02  inst_num_moves_active_passive:          0
% 0.58/1.02  inst_lit_activity:                      0
% 0.58/1.02  inst_lit_activity_moves:                0
% 0.58/1.02  inst_num_tautologies:                   0
% 0.58/1.02  inst_num_prop_implied:                  0
% 0.58/1.02  inst_num_existing_simplified:           0
% 0.58/1.02  inst_num_eq_res_simplified:             0
% 0.58/1.02  inst_num_child_elim:                    0
% 0.58/1.02  inst_num_of_dismatching_blockings:      0
% 0.58/1.02  inst_num_of_non_proper_insts:           0
% 0.58/1.02  inst_num_of_duplicates:                 0
% 0.58/1.02  inst_inst_num_from_inst_to_res:         0
% 0.58/1.02  inst_dismatching_checking_time:         0.
% 0.58/1.02  
% 0.58/1.02  ------ Resolution
% 0.58/1.02  
% 0.58/1.02  res_num_of_clauses:                     0
% 0.58/1.02  res_num_in_passive:                     0
% 0.58/1.02  res_num_in_active:                      0
% 0.58/1.02  res_num_of_loops:                       6
% 0.58/1.02  res_forward_subset_subsumed:            0
% 0.58/1.02  res_backward_subset_subsumed:           0
% 0.58/1.02  res_forward_subsumed:                   0
% 0.58/1.02  res_backward_subsumed:                  0
% 0.58/1.02  res_forward_subsumption_resolution:     0
% 0.58/1.02  res_backward_subsumption_resolution:    0
% 0.58/1.02  res_clause_to_clause_subsumption:       0
% 0.58/1.02  res_orphan_elimination:                 0
% 0.58/1.02  res_tautology_del:                      0
% 0.58/1.02  res_num_eq_res_simplified:              0
% 0.58/1.02  res_num_sel_changes:                    0
% 0.58/1.02  res_moves_from_active_to_pass:          0
% 0.58/1.02  
% 0.58/1.02  ------ Superposition
% 0.58/1.02  
% 0.58/1.02  sup_time_total:                         0.
% 0.58/1.02  sup_time_generating:                    0.
% 0.58/1.02  sup_time_sim_full:                      0.
% 0.58/1.02  sup_time_sim_immed:                     0.
% 0.58/1.02  
% 0.58/1.02  sup_num_of_clauses:                     0
% 0.58/1.02  sup_num_in_active:                      0
% 0.58/1.02  sup_num_in_passive:                     0
% 0.58/1.02  sup_num_of_loops:                       0
% 0.58/1.02  sup_fw_superposition:                   0
% 0.58/1.02  sup_bw_superposition:                   0
% 0.58/1.02  sup_immediate_simplified:               0
% 0.58/1.02  sup_given_eliminated:                   0
% 0.58/1.02  comparisons_done:                       0
% 0.58/1.02  comparisons_avoided:                    0
% 0.58/1.02  
% 0.58/1.02  ------ Simplifications
% 0.58/1.02  
% 0.58/1.02  
% 0.58/1.02  sim_fw_subset_subsumed:                 0
% 0.58/1.02  sim_bw_subset_subsumed:                 0
% 0.58/1.02  sim_fw_subsumed:                        0
% 0.58/1.02  sim_bw_subsumed:                        0
% 0.58/1.02  sim_fw_subsumption_res:                 0
% 0.58/1.02  sim_bw_subsumption_res:                 0
% 0.58/1.02  sim_tautology_del:                      0
% 0.58/1.02  sim_eq_tautology_del:                   0
% 0.58/1.02  sim_eq_res_simp:                        0
% 0.58/1.02  sim_fw_demodulated:                     0
% 0.58/1.02  sim_bw_demodulated:                     0
% 0.58/1.02  sim_light_normalised:                   0
% 0.58/1.02  sim_joinable_taut:                      0
% 0.58/1.02  sim_joinable_simp:                      0
% 0.58/1.02  sim_ac_normalised:                      0
% 0.58/1.02  sim_smt_subsumption:                    0
% 0.58/1.02  
%------------------------------------------------------------------------------
