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
% DateTime   : Thu Dec  3 12:11:42 EST 2020

% Result     : CounterSatisfiable 2.84s
% Output     : Model 2.84s
% Verified   : 
% Statistics : Number of formulae       :    4 (   4 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    0
%              Number of atoms          :   11 (  11 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    7 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%------ Negative definition of r1_tarski 
fof(lit_def,axiom,(
    ! [X0_40,X1_40] :
      ( ~ r1_tarski(X0_40,X1_40)
    <=> $false ) )).

%------ Positive definition of r2_hidden 
fof(lit_def_001,axiom,(
    ! [X0_40,X1_40] :
      ( r2_hidden(X0_40,X1_40)
    <=> $true ) )).

%------ Negative definition of m1_subset_1 
fof(lit_def_002,axiom,(
    ! [X0_40,X1_40] :
      ( ~ m1_subset_1(X0_40,X1_40)
    <=> ( ( X0_40 = sK3
          & X1_40 = u1_struct_0(sK1) )
        | ( X1_40 = u1_struct_0(sK1)
          & X0_40 != u1_struct_0(sK1) ) ) ) )).

%------ Positive definition of v1_xboole_0 
fof(lit_def_003,axiom,(
    ! [X0_40] :
      ( v1_xboole_0(X0_40)
    <=> X0_40 = u1_struct_0(sK1) ) )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:35:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.84/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.01  
% 2.84/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.84/1.01  
% 2.84/1.01  ------  iProver source info
% 2.84/1.01  
% 2.84/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.84/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.84/1.01  git: non_committed_changes: false
% 2.84/1.01  git: last_make_outside_of_git: false
% 2.84/1.01  
% 2.84/1.01  ------ 
% 2.84/1.01  
% 2.84/1.01  ------ Input Options
% 2.84/1.01  
% 2.84/1.01  --out_options                           all
% 2.84/1.01  --tptp_safe_out                         true
% 2.84/1.01  --problem_path                          ""
% 2.84/1.01  --include_path                          ""
% 2.84/1.01  --clausifier                            res/vclausify_rel
% 2.84/1.01  --clausifier_options                    --mode clausify
% 2.84/1.01  --stdin                                 false
% 2.84/1.01  --stats_out                             all
% 2.84/1.01  
% 2.84/1.01  ------ General Options
% 2.84/1.01  
% 2.84/1.01  --fof                                   false
% 2.84/1.01  --time_out_real                         305.
% 2.84/1.01  --time_out_virtual                      -1.
% 2.84/1.01  --symbol_type_check                     false
% 2.84/1.01  --clausify_out                          false
% 2.84/1.01  --sig_cnt_out                           false
% 2.84/1.01  --trig_cnt_out                          false
% 2.84/1.01  --trig_cnt_out_tolerance                1.
% 2.84/1.01  --trig_cnt_out_sk_spl                   false
% 2.84/1.01  --abstr_cl_out                          false
% 2.84/1.01  
% 2.84/1.01  ------ Global Options
% 2.84/1.01  
% 2.84/1.01  --schedule                              default
% 2.84/1.01  --add_important_lit                     false
% 2.84/1.01  --prop_solver_per_cl                    1000
% 2.84/1.01  --min_unsat_core                        false
% 2.84/1.01  --soft_assumptions                      false
% 2.84/1.01  --soft_lemma_size                       3
% 2.84/1.01  --prop_impl_unit_size                   0
% 2.84/1.01  --prop_impl_unit                        []
% 2.84/1.01  --share_sel_clauses                     true
% 2.84/1.01  --reset_solvers                         false
% 2.84/1.01  --bc_imp_inh                            [conj_cone]
% 2.84/1.01  --conj_cone_tolerance                   3.
% 2.84/1.01  --extra_neg_conj                        none
% 2.84/1.01  --large_theory_mode                     true
% 2.84/1.01  --prolific_symb_bound                   200
% 2.84/1.01  --lt_threshold                          2000
% 2.84/1.01  --clause_weak_htbl                      true
% 2.84/1.01  --gc_record_bc_elim                     false
% 2.84/1.01  
% 2.84/1.01  ------ Preprocessing Options
% 2.84/1.01  
% 2.84/1.01  --preprocessing_flag                    true
% 2.84/1.01  --time_out_prep_mult                    0.1
% 2.84/1.01  --splitting_mode                        input
% 2.84/1.01  --splitting_grd                         true
% 2.84/1.01  --splitting_cvd                         false
% 2.84/1.01  --splitting_cvd_svl                     false
% 2.84/1.01  --splitting_nvd                         32
% 2.84/1.01  --sub_typing                            true
% 2.84/1.01  --prep_gs_sim                           true
% 2.84/1.01  --prep_unflatten                        true
% 2.84/1.01  --prep_res_sim                          true
% 2.84/1.01  --prep_upred                            true
% 2.84/1.01  --prep_sem_filter                       exhaustive
% 2.84/1.01  --prep_sem_filter_out                   false
% 2.84/1.01  --pred_elim                             true
% 2.84/1.01  --res_sim_input                         true
% 2.84/1.01  --eq_ax_congr_red                       true
% 2.84/1.01  --pure_diseq_elim                       true
% 2.84/1.01  --brand_transform                       false
% 2.84/1.01  --non_eq_to_eq                          false
% 2.84/1.01  --prep_def_merge                        true
% 2.84/1.01  --prep_def_merge_prop_impl              false
% 2.84/1.01  --prep_def_merge_mbd                    true
% 2.84/1.01  --prep_def_merge_tr_red                 false
% 2.84/1.01  --prep_def_merge_tr_cl                  false
% 2.84/1.01  --smt_preprocessing                     true
% 2.84/1.01  --smt_ac_axioms                         fast
% 2.84/1.01  --preprocessed_out                      false
% 2.84/1.01  --preprocessed_stats                    false
% 2.84/1.01  
% 2.84/1.01  ------ Abstraction refinement Options
% 2.84/1.01  
% 2.84/1.01  --abstr_ref                             []
% 2.84/1.01  --abstr_ref_prep                        false
% 2.84/1.01  --abstr_ref_until_sat                   false
% 2.84/1.01  --abstr_ref_sig_restrict                funpre
% 2.84/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.84/1.01  --abstr_ref_under                       []
% 2.84/1.01  
% 2.84/1.01  ------ SAT Options
% 2.84/1.01  
% 2.84/1.01  --sat_mode                              false
% 2.84/1.01  --sat_fm_restart_options                ""
% 2.84/1.01  --sat_gr_def                            false
% 2.84/1.01  --sat_epr_types                         true
% 2.84/1.01  --sat_non_cyclic_types                  false
% 2.84/1.01  --sat_finite_models                     false
% 2.84/1.01  --sat_fm_lemmas                         false
% 2.84/1.01  --sat_fm_prep                           false
% 2.84/1.01  --sat_fm_uc_incr                        true
% 2.84/1.01  --sat_out_model                         small
% 2.84/1.01  --sat_out_clauses                       false
% 2.84/1.01  
% 2.84/1.01  ------ QBF Options
% 2.84/1.01  
% 2.84/1.01  --qbf_mode                              false
% 2.84/1.01  --qbf_elim_univ                         false
% 2.84/1.01  --qbf_dom_inst                          none
% 2.84/1.01  --qbf_dom_pre_inst                      false
% 2.84/1.01  --qbf_sk_in                             false
% 2.84/1.01  --qbf_pred_elim                         true
% 2.84/1.01  --qbf_split                             512
% 2.84/1.01  
% 2.84/1.01  ------ BMC1 Options
% 2.84/1.01  
% 2.84/1.01  --bmc1_incremental                      false
% 2.84/1.01  --bmc1_axioms                           reachable_all
% 2.84/1.01  --bmc1_min_bound                        0
% 2.84/1.01  --bmc1_max_bound                        -1
% 2.84/1.01  --bmc1_max_bound_default                -1
% 2.84/1.01  --bmc1_symbol_reachability              true
% 2.84/1.01  --bmc1_property_lemmas                  false
% 2.84/1.01  --bmc1_k_induction                      false
% 2.84/1.01  --bmc1_non_equiv_states                 false
% 2.84/1.01  --bmc1_deadlock                         false
% 2.84/1.01  --bmc1_ucm                              false
% 2.84/1.01  --bmc1_add_unsat_core                   none
% 2.84/1.01  --bmc1_unsat_core_children              false
% 2.84/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.84/1.01  --bmc1_out_stat                         full
% 2.84/1.01  --bmc1_ground_init                      false
% 2.84/1.01  --bmc1_pre_inst_next_state              false
% 2.84/1.01  --bmc1_pre_inst_state                   false
% 2.84/1.01  --bmc1_pre_inst_reach_state             false
% 2.84/1.01  --bmc1_out_unsat_core                   false
% 2.84/1.01  --bmc1_aig_witness_out                  false
% 2.84/1.01  --bmc1_verbose                          false
% 2.84/1.01  --bmc1_dump_clauses_tptp                false
% 2.84/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.84/1.01  --bmc1_dump_file                        -
% 2.84/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.84/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.84/1.01  --bmc1_ucm_extend_mode                  1
% 2.84/1.01  --bmc1_ucm_init_mode                    2
% 2.84/1.01  --bmc1_ucm_cone_mode                    none
% 2.84/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.84/1.01  --bmc1_ucm_relax_model                  4
% 2.84/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.84/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.84/1.01  --bmc1_ucm_layered_model                none
% 2.84/1.01  --bmc1_ucm_max_lemma_size               10
% 2.84/1.01  
% 2.84/1.01  ------ AIG Options
% 2.84/1.01  
% 2.84/1.01  --aig_mode                              false
% 2.84/1.01  
% 2.84/1.01  ------ Instantiation Options
% 2.84/1.01  
% 2.84/1.01  --instantiation_flag                    true
% 2.84/1.01  --inst_sos_flag                         false
% 2.84/1.01  --inst_sos_phase                        true
% 2.84/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.84/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.84/1.01  --inst_lit_sel_side                     num_symb
% 2.84/1.01  --inst_solver_per_active                1400
% 2.84/1.01  --inst_solver_calls_frac                1.
% 2.84/1.01  --inst_passive_queue_type               priority_queues
% 2.84/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.84/1.01  --inst_passive_queues_freq              [25;2]
% 2.84/1.01  --inst_dismatching                      true
% 2.84/1.01  --inst_eager_unprocessed_to_passive     true
% 2.84/1.01  --inst_prop_sim_given                   true
% 2.84/1.01  --inst_prop_sim_new                     false
% 2.84/1.01  --inst_subs_new                         false
% 2.84/1.01  --inst_eq_res_simp                      false
% 2.84/1.01  --inst_subs_given                       false
% 2.84/1.01  --inst_orphan_elimination               true
% 2.84/1.01  --inst_learning_loop_flag               true
% 2.84/1.01  --inst_learning_start                   3000
% 2.84/1.01  --inst_learning_factor                  2
% 2.84/1.01  --inst_start_prop_sim_after_learn       3
% 2.84/1.01  --inst_sel_renew                        solver
% 2.84/1.01  --inst_lit_activity_flag                true
% 2.84/1.01  --inst_restr_to_given                   false
% 2.84/1.01  --inst_activity_threshold               500
% 2.84/1.01  --inst_out_proof                        true
% 2.84/1.01  
% 2.84/1.01  ------ Resolution Options
% 2.84/1.01  
% 2.84/1.01  --resolution_flag                       true
% 2.84/1.01  --res_lit_sel                           adaptive
% 2.84/1.01  --res_lit_sel_side                      none
% 2.84/1.01  --res_ordering                          kbo
% 2.84/1.01  --res_to_prop_solver                    active
% 2.84/1.01  --res_prop_simpl_new                    false
% 2.84/1.01  --res_prop_simpl_given                  true
% 2.84/1.01  --res_passive_queue_type                priority_queues
% 2.84/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.84/1.01  --res_passive_queues_freq               [15;5]
% 2.84/1.01  --res_forward_subs                      full
% 2.84/1.01  --res_backward_subs                     full
% 2.84/1.01  --res_forward_subs_resolution           true
% 2.84/1.01  --res_backward_subs_resolution          true
% 2.84/1.01  --res_orphan_elimination                true
% 2.84/1.01  --res_time_limit                        2.
% 2.84/1.01  --res_out_proof                         true
% 2.84/1.01  
% 2.84/1.01  ------ Superposition Options
% 2.84/1.01  
% 2.84/1.01  --superposition_flag                    true
% 2.84/1.01  --sup_passive_queue_type                priority_queues
% 2.84/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.84/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.84/1.01  --demod_completeness_check              fast
% 2.84/1.01  --demod_use_ground                      true
% 2.84/1.01  --sup_to_prop_solver                    passive
% 2.84/1.01  --sup_prop_simpl_new                    true
% 2.84/1.01  --sup_prop_simpl_given                  true
% 2.84/1.01  --sup_fun_splitting                     false
% 2.84/1.01  --sup_smt_interval                      50000
% 2.84/1.01  
% 2.84/1.01  ------ Superposition Simplification Setup
% 2.84/1.01  
% 2.84/1.01  --sup_indices_passive                   []
% 2.84/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.84/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.01  --sup_full_bw                           [BwDemod]
% 2.84/1.01  --sup_immed_triv                        [TrivRules]
% 2.84/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.84/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.01  --sup_immed_bw_main                     []
% 2.84/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.84/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.01  
% 2.84/1.01  ------ Combination Options
% 2.84/1.01  
% 2.84/1.01  --comb_res_mult                         3
% 2.84/1.01  --comb_sup_mult                         2
% 2.84/1.01  --comb_inst_mult                        10
% 2.84/1.01  
% 2.84/1.01  ------ Debug Options
% 2.84/1.01  
% 2.84/1.01  --dbg_backtrace                         false
% 2.84/1.01  --dbg_dump_prop_clauses                 false
% 2.84/1.01  --dbg_dump_prop_clauses_file            -
% 2.84/1.01  --dbg_out_stat                          false
% 2.84/1.01  ------ Parsing...
% 2.84/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.84/1.01  
% 2.84/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.84/1.01  
% 2.84/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.84/1.01  ------ Proving...
% 2.84/1.01  ------ Problem Properties 
% 2.84/1.01  
% 2.84/1.01  
% 2.84/1.01  clauses                                 12
% 2.84/1.01  conjectures                             2
% 2.84/1.01  EPR                                     5
% 2.84/1.01  Horn                                    9
% 2.84/1.01  unary                                   2
% 2.84/1.01  binary                                  5
% 2.84/1.01  lits                                    27
% 2.84/1.01  lits eq                                 0
% 2.84/1.01  fd_pure                                 0
% 2.84/1.01  fd_pseudo                               0
% 2.84/1.01  fd_cond                                 0
% 2.84/1.01  fd_pseudo_cond                          0
% 2.84/1.01  AC symbols                              0
% 2.84/1.01  
% 2.84/1.01  ------ Schedule dynamic 5 is on 
% 2.84/1.01  
% 2.84/1.01  ------ no equalities: superposition off 
% 2.84/1.01  
% 2.84/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.84/1.01  
% 2.84/1.01  
% 2.84/1.01  ------ 
% 2.84/1.01  Current options:
% 2.84/1.01  ------ 
% 2.84/1.01  
% 2.84/1.01  ------ Input Options
% 2.84/1.01  
% 2.84/1.01  --out_options                           all
% 2.84/1.01  --tptp_safe_out                         true
% 2.84/1.01  --problem_path                          ""
% 2.84/1.01  --include_path                          ""
% 2.84/1.01  --clausifier                            res/vclausify_rel
% 2.84/1.01  --clausifier_options                    --mode clausify
% 2.84/1.01  --stdin                                 false
% 2.84/1.01  --stats_out                             all
% 2.84/1.01  
% 2.84/1.01  ------ General Options
% 2.84/1.01  
% 2.84/1.01  --fof                                   false
% 2.84/1.01  --time_out_real                         305.
% 2.84/1.01  --time_out_virtual                      -1.
% 2.84/1.01  --symbol_type_check                     false
% 2.84/1.01  --clausify_out                          false
% 2.84/1.01  --sig_cnt_out                           false
% 2.84/1.01  --trig_cnt_out                          false
% 2.84/1.01  --trig_cnt_out_tolerance                1.
% 2.84/1.01  --trig_cnt_out_sk_spl                   false
% 2.84/1.01  --abstr_cl_out                          false
% 2.84/1.01  
% 2.84/1.01  ------ Global Options
% 2.84/1.01  
% 2.84/1.01  --schedule                              default
% 2.84/1.01  --add_important_lit                     false
% 2.84/1.01  --prop_solver_per_cl                    1000
% 2.84/1.01  --min_unsat_core                        false
% 2.84/1.01  --soft_assumptions                      false
% 2.84/1.01  --soft_lemma_size                       3
% 2.84/1.01  --prop_impl_unit_size                   0
% 2.84/1.01  --prop_impl_unit                        []
% 2.84/1.01  --share_sel_clauses                     true
% 2.84/1.01  --reset_solvers                         false
% 2.84/1.01  --bc_imp_inh                            [conj_cone]
% 2.84/1.01  --conj_cone_tolerance                   3.
% 2.84/1.01  --extra_neg_conj                        none
% 2.84/1.01  --large_theory_mode                     true
% 2.84/1.01  --prolific_symb_bound                   200
% 2.84/1.01  --lt_threshold                          2000
% 2.84/1.01  --clause_weak_htbl                      true
% 2.84/1.01  --gc_record_bc_elim                     false
% 2.84/1.01  
% 2.84/1.01  ------ Preprocessing Options
% 2.84/1.01  
% 2.84/1.01  --preprocessing_flag                    true
% 2.84/1.01  --time_out_prep_mult                    0.1
% 2.84/1.01  --splitting_mode                        input
% 2.84/1.01  --splitting_grd                         true
% 2.84/1.01  --splitting_cvd                         false
% 2.84/1.01  --splitting_cvd_svl                     false
% 2.84/1.01  --splitting_nvd                         32
% 2.84/1.01  --sub_typing                            true
% 2.84/1.01  --prep_gs_sim                           true
% 2.84/1.01  --prep_unflatten                        true
% 2.84/1.01  --prep_res_sim                          true
% 2.84/1.01  --prep_upred                            true
% 2.84/1.01  --prep_sem_filter                       exhaustive
% 2.84/1.01  --prep_sem_filter_out                   false
% 2.84/1.01  --pred_elim                             true
% 2.84/1.01  --res_sim_input                         true
% 2.84/1.01  --eq_ax_congr_red                       true
% 2.84/1.01  --pure_diseq_elim                       true
% 2.84/1.01  --brand_transform                       false
% 2.84/1.01  --non_eq_to_eq                          false
% 2.84/1.01  --prep_def_merge                        true
% 2.84/1.01  --prep_def_merge_prop_impl              false
% 2.84/1.01  --prep_def_merge_mbd                    true
% 2.84/1.01  --prep_def_merge_tr_red                 false
% 2.84/1.01  --prep_def_merge_tr_cl                  false
% 2.84/1.01  --smt_preprocessing                     true
% 2.84/1.01  --smt_ac_axioms                         fast
% 2.84/1.01  --preprocessed_out                      false
% 2.84/1.01  --preprocessed_stats                    false
% 2.84/1.01  
% 2.84/1.01  ------ Abstraction refinement Options
% 2.84/1.01  
% 2.84/1.01  --abstr_ref                             []
% 2.84/1.01  --abstr_ref_prep                        false
% 2.84/1.01  --abstr_ref_until_sat                   false
% 2.84/1.01  --abstr_ref_sig_restrict                funpre
% 2.84/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.84/1.01  --abstr_ref_under                       []
% 2.84/1.01  
% 2.84/1.01  ------ SAT Options
% 2.84/1.01  
% 2.84/1.01  --sat_mode                              false
% 2.84/1.01  --sat_fm_restart_options                ""
% 2.84/1.01  --sat_gr_def                            false
% 2.84/1.01  --sat_epr_types                         true
% 2.84/1.01  --sat_non_cyclic_types                  false
% 2.84/1.01  --sat_finite_models                     false
% 2.84/1.01  --sat_fm_lemmas                         false
% 2.84/1.01  --sat_fm_prep                           false
% 2.84/1.01  --sat_fm_uc_incr                        true
% 2.84/1.01  --sat_out_model                         small
% 2.84/1.01  --sat_out_clauses                       false
% 2.84/1.01  
% 2.84/1.01  ------ QBF Options
% 2.84/1.01  
% 2.84/1.01  --qbf_mode                              false
% 2.84/1.01  --qbf_elim_univ                         false
% 2.84/1.01  --qbf_dom_inst                          none
% 2.84/1.01  --qbf_dom_pre_inst                      false
% 2.84/1.01  --qbf_sk_in                             false
% 2.84/1.01  --qbf_pred_elim                         true
% 2.84/1.01  --qbf_split                             512
% 2.84/1.01  
% 2.84/1.01  ------ BMC1 Options
% 2.84/1.01  
% 2.84/1.01  --bmc1_incremental                      false
% 2.84/1.01  --bmc1_axioms                           reachable_all
% 2.84/1.01  --bmc1_min_bound                        0
% 2.84/1.01  --bmc1_max_bound                        -1
% 2.84/1.01  --bmc1_max_bound_default                -1
% 2.84/1.01  --bmc1_symbol_reachability              true
% 2.84/1.01  --bmc1_property_lemmas                  false
% 2.84/1.01  --bmc1_k_induction                      false
% 2.84/1.01  --bmc1_non_equiv_states                 false
% 2.84/1.01  --bmc1_deadlock                         false
% 2.84/1.01  --bmc1_ucm                              false
% 2.84/1.01  --bmc1_add_unsat_core                   none
% 2.84/1.01  --bmc1_unsat_core_children              false
% 2.84/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.84/1.01  --bmc1_out_stat                         full
% 2.84/1.01  --bmc1_ground_init                      false
% 2.84/1.01  --bmc1_pre_inst_next_state              false
% 2.84/1.01  --bmc1_pre_inst_state                   false
% 2.84/1.01  --bmc1_pre_inst_reach_state             false
% 2.84/1.01  --bmc1_out_unsat_core                   false
% 2.84/1.01  --bmc1_aig_witness_out                  false
% 2.84/1.01  --bmc1_verbose                          false
% 2.84/1.01  --bmc1_dump_clauses_tptp                false
% 2.84/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.84/1.01  --bmc1_dump_file                        -
% 2.84/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.84/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.84/1.01  --bmc1_ucm_extend_mode                  1
% 2.84/1.01  --bmc1_ucm_init_mode                    2
% 2.84/1.01  --bmc1_ucm_cone_mode                    none
% 2.84/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.84/1.01  --bmc1_ucm_relax_model                  4
% 2.84/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.84/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.84/1.01  --bmc1_ucm_layered_model                none
% 2.84/1.01  --bmc1_ucm_max_lemma_size               10
% 2.84/1.01  
% 2.84/1.01  ------ AIG Options
% 2.84/1.01  
% 2.84/1.01  --aig_mode                              false
% 2.84/1.01  
% 2.84/1.01  ------ Instantiation Options
% 2.84/1.01  
% 2.84/1.01  --instantiation_flag                    true
% 2.84/1.01  --inst_sos_flag                         false
% 2.84/1.01  --inst_sos_phase                        true
% 2.84/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.84/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.84/1.01  --inst_lit_sel_side                     none
% 2.84/1.01  --inst_solver_per_active                1400
% 2.84/1.01  --inst_solver_calls_frac                1.
% 2.84/1.01  --inst_passive_queue_type               priority_queues
% 2.84/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.84/1.01  --inst_passive_queues_freq              [25;2]
% 2.84/1.01  --inst_dismatching                      true
% 2.84/1.01  --inst_eager_unprocessed_to_passive     true
% 2.84/1.01  --inst_prop_sim_given                   true
% 2.84/1.01  --inst_prop_sim_new                     false
% 2.84/1.01  --inst_subs_new                         false
% 2.84/1.01  --inst_eq_res_simp                      false
% 2.84/1.01  --inst_subs_given                       false
% 2.84/1.01  --inst_orphan_elimination               true
% 2.84/1.01  --inst_learning_loop_flag               true
% 2.84/1.01  --inst_learning_start                   3000
% 2.84/1.01  --inst_learning_factor                  2
% 2.84/1.01  --inst_start_prop_sim_after_learn       3
% 2.84/1.01  --inst_sel_renew                        solver
% 2.84/1.01  --inst_lit_activity_flag                true
% 2.84/1.01  --inst_restr_to_given                   false
% 2.84/1.01  --inst_activity_threshold               500
% 2.84/1.01  --inst_out_proof                        true
% 2.84/1.01  
% 2.84/1.01  ------ Resolution Options
% 2.84/1.01  
% 2.84/1.01  --resolution_flag                       false
% 2.84/1.01  --res_lit_sel                           adaptive
% 2.84/1.01  --res_lit_sel_side                      none
% 2.84/1.01  --res_ordering                          kbo
% 2.84/1.01  --res_to_prop_solver                    active
% 2.84/1.01  --res_prop_simpl_new                    false
% 2.84/1.01  --res_prop_simpl_given                  true
% 2.84/1.01  --res_passive_queue_type                priority_queues
% 2.84/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.84/1.01  --res_passive_queues_freq               [15;5]
% 2.84/1.01  --res_forward_subs                      full
% 2.84/1.01  --res_backward_subs                     full
% 2.84/1.01  --res_forward_subs_resolution           true
% 2.84/1.01  --res_backward_subs_resolution          true
% 2.84/1.01  --res_orphan_elimination                true
% 2.84/1.01  --res_time_limit                        2.
% 2.84/1.01  --res_out_proof                         true
% 2.84/1.01  
% 2.84/1.01  ------ Superposition Options
% 2.84/1.01  
% 2.84/1.01  --superposition_flag                    false
% 2.84/1.01  --sup_passive_queue_type                priority_queues
% 2.84/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.84/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.84/1.01  --demod_completeness_check              fast
% 2.84/1.01  --demod_use_ground                      true
% 2.84/1.01  --sup_to_prop_solver                    passive
% 2.84/1.01  --sup_prop_simpl_new                    true
% 2.84/1.01  --sup_prop_simpl_given                  true
% 2.84/1.01  --sup_fun_splitting                     false
% 2.84/1.01  --sup_smt_interval                      50000
% 2.84/1.01  
% 2.84/1.01  ------ Superposition Simplification Setup
% 2.84/1.01  
% 2.84/1.01  --sup_indices_passive                   []
% 2.84/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.84/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.84/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.01  --sup_full_bw                           [BwDemod]
% 2.84/1.01  --sup_immed_triv                        [TrivRules]
% 2.84/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.84/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.01  --sup_immed_bw_main                     []
% 2.84/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.84/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.84/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.84/1.01  
% 2.84/1.01  ------ Combination Options
% 2.84/1.01  
% 2.84/1.01  --comb_res_mult                         3
% 2.84/1.01  --comb_sup_mult                         2
% 2.84/1.01  --comb_inst_mult                        10
% 2.84/1.01  
% 2.84/1.01  ------ Debug Options
% 2.84/1.01  
% 2.84/1.01  --dbg_backtrace                         false
% 2.84/1.01  --dbg_dump_prop_clauses                 false
% 2.84/1.01  --dbg_dump_prop_clauses_file            -
% 2.84/1.01  --dbg_out_stat                          false
% 2.84/1.01  
% 2.84/1.01  
% 2.84/1.01  
% 2.84/1.01  
% 2.84/1.01  ------ Proving...
% 2.84/1.01  
% 2.84/1.01  
% 2.84/1.01  % SZS status CounterSatisfiable for theBenchmark.p
% 2.84/1.01  
% 2.84/1.01  ------ Building Model...Done
% 2.84/1.01  
% 2.84/1.01  %------ The model is defined over ground terms (initial term algebra).
% 2.84/1.01  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 2.84/1.01  %------ where \phi is a formula over the term algebra.
% 2.84/1.01  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 2.84/1.01  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 2.84/1.01  %------ See help for --sat_out_model for different model outputs.
% 2.84/1.01  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 2.84/1.01  %------ where the first argument stands for the sort ($i in the unsorted case)
% 2.84/1.01  % SZS output start Model for theBenchmark.p
% 2.84/1.01  
% 2.84/1.01  %------ Negative definition of r1_tarski 
% 2.84/1.01  fof(lit_def,axiom,
% 2.84/1.01      (! [X0_40,X1_40] : 
% 2.84/1.01        ( ~(r1_tarski(X0_40,X1_40)) <=>
% 2.84/1.01            $false
% 2.84/1.01        )
% 2.84/1.01      )
% 2.84/1.01     ).
% 2.84/1.01  
% 2.84/1.01  %------ Positive definition of r2_hidden 
% 2.84/1.01  fof(lit_def,axiom,
% 2.84/1.01      (! [X0_40,X1_40] : 
% 2.84/1.01        ( r2_hidden(X0_40,X1_40) <=>
% 2.84/1.01            $true
% 2.84/1.01        )
% 2.84/1.01      )
% 2.84/1.01     ).
% 2.84/1.01  
% 2.84/1.01  %------ Negative definition of m1_subset_1 
% 2.84/1.01  fof(lit_def,axiom,
% 2.84/1.01      (! [X0_40,X1_40] : 
% 2.84/1.01        ( ~(m1_subset_1(X0_40,X1_40)) <=>
% 2.84/1.01             (
% 2.84/1.01                (
% 2.84/1.01                  ( X0_40=sK3 & X1_40=u1_struct_0(sK1) )
% 2.84/1.01                )
% 2.84/1.01  
% 2.84/1.01               | 
% 2.84/1.01                (
% 2.84/1.01                  ( X1_40=u1_struct_0(sK1) )
% 2.84/1.01                 &
% 2.84/1.01                  ( X0_40!=u1_struct_0(sK1) )
% 2.84/1.01                )
% 2.84/1.01  
% 2.84/1.01             )
% 2.84/1.01        )
% 2.84/1.01      )
% 2.84/1.01     ).
% 2.84/1.01  
% 2.84/1.01  %------ Positive definition of v1_xboole_0 
% 2.84/1.01  fof(lit_def,axiom,
% 2.84/1.01      (! [X0_40] : 
% 2.84/1.01        ( v1_xboole_0(X0_40) <=>
% 2.84/1.01             (
% 2.84/1.01                (
% 2.84/1.01                  ( X0_40=u1_struct_0(sK1) )
% 2.84/1.01                )
% 2.84/1.01  
% 2.84/1.01             )
% 2.84/1.01        )
% 2.84/1.01      )
% 2.84/1.01     ).
% 2.84/1.01  % SZS output end Model for theBenchmark.p
% 2.84/1.01  ------                               Statistics
% 2.84/1.01  
% 2.84/1.01  ------ General
% 2.84/1.01  
% 2.84/1.01  abstr_ref_over_cycles:                  0
% 2.84/1.01  abstr_ref_under_cycles:                 0
% 2.84/1.01  gc_basic_clause_elim:                   0
% 2.84/1.01  forced_gc_time:                         0
% 2.84/1.01  parsing_time:                           0.025
% 2.84/1.01  unif_index_cands_time:                  0.
% 2.84/1.01  unif_index_add_time:                    0.
% 2.84/1.01  orderings_time:                         0.
% 2.84/1.01  out_proof_time:                         0.
% 2.84/1.01  total_time:                             0.066
% 2.84/1.01  num_of_symbols:                         45
% 2.84/1.01  num_of_terms:                           529
% 2.84/1.01  
% 2.84/1.01  ------ Preprocessing
% 2.84/1.01  
% 2.84/1.01  num_of_splits:                          0
% 2.84/1.01  num_of_split_atoms:                     0
% 2.84/1.01  num_of_reused_defs:                     0
% 2.84/1.01  num_eq_ax_congr_red:                    0
% 2.84/1.01  num_of_sem_filtered_clauses:            0
% 2.84/1.01  num_of_subtypes:                        2
% 2.84/1.01  monotx_restored_types:                  0
% 2.84/1.01  sat_num_of_epr_types:                   0
% 2.84/1.01  sat_num_of_non_cyclic_types:            0
% 2.84/1.01  sat_guarded_non_collapsed_types:        0
% 2.84/1.01  num_pure_diseq_elim:                    0
% 2.84/1.01  simp_replaced_by:                       0
% 2.84/1.01  res_preprocessed:                       27
% 2.84/1.01  prep_upred:                             0
% 2.84/1.01  prep_unflattend:                        0
% 2.84/1.01  smt_new_axioms:                         0
% 2.84/1.01  pred_elim_cands:                        4
% 2.84/1.01  pred_elim:                              2
% 2.84/1.01  pred_elim_cl:                           3
% 2.84/1.01  pred_elim_cycles:                       4
% 2.84/1.01  merged_defs:                            4
% 2.84/1.01  merged_defs_ncl:                        0
% 2.84/1.01  bin_hyper_res:                          4
% 2.84/1.01  prep_cycles:                            2
% 2.84/1.01  pred_elim_time:                         0.003
% 2.84/1.01  splitting_time:                         0.
% 2.84/1.01  sem_filter_time:                        0.
% 2.84/1.01  monotx_time:                            0.
% 2.84/1.01  subtype_inf_time:                       0.
% 2.84/1.01  
% 2.84/1.01  ------ Problem properties
% 2.84/1.01  
% 2.84/1.01  clauses:                                12
% 2.84/1.01  conjectures:                            2
% 2.84/1.01  epr:                                    5
% 2.84/1.01  horn:                                   9
% 2.84/1.01  ground:                                 2
% 2.84/1.01  unary:                                  2
% 2.84/1.01  binary:                                 5
% 2.84/1.01  lits:                                   27
% 2.84/1.01  lits_eq:                                0
% 2.84/1.01  fd_pure:                                0
% 2.84/1.01  fd_pseudo:                              0
% 2.84/1.01  fd_cond:                                0
% 2.84/1.01  fd_pseudo_cond:                         0
% 2.84/1.01  ac_symbols:                             0
% 2.84/1.01  
% 2.84/1.01  ------ Propositional Solver
% 2.84/1.01  
% 2.84/1.01  prop_solver_calls:                      16
% 2.84/1.01  prop_fast_solver_calls:                 156
% 2.84/1.01  smt_solver_calls:                       0
% 2.84/1.01  smt_fast_solver_calls:                  0
% 2.84/1.01  prop_num_of_clauses:                    188
% 2.84/1.01  prop_preprocess_simplified:             1030
% 2.84/1.01  prop_fo_subsumed:                       2
% 2.84/1.01  prop_solver_time:                       0.
% 2.84/1.01  smt_solver_time:                        0.
% 2.84/1.01  smt_fast_solver_time:                   0.
% 2.84/1.01  prop_fast_solver_time:                  0.
% 2.84/1.01  prop_unsat_core_time:                   0.
% 2.84/1.01  
% 2.84/1.01  ------ QBF
% 2.84/1.01  
% 2.84/1.01  qbf_q_res:                              0
% 2.84/1.01  qbf_num_tautologies:                    0
% 2.84/1.01  qbf_prep_cycles:                        0
% 2.84/1.01  
% 2.84/1.01  ------ BMC1
% 2.84/1.01  
% 2.84/1.01  bmc1_current_bound:                     -1
% 2.84/1.01  bmc1_last_solved_bound:                 -1
% 2.84/1.01  bmc1_unsat_core_size:                   -1
% 2.84/1.01  bmc1_unsat_core_parents_size:           -1
% 2.84/1.01  bmc1_merge_next_fun:                    0
% 2.84/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.84/1.01  
% 2.84/1.01  ------ Instantiation
% 2.84/1.01  
% 2.84/1.01  inst_num_of_clauses:                    36
% 2.84/1.01  inst_num_in_passive:                    0
% 2.84/1.01  inst_num_in_active:                     36
% 2.84/1.01  inst_num_in_unprocessed:                0
% 2.84/1.01  inst_num_of_loops:                      49
% 2.84/1.01  inst_num_of_learning_restarts:          0
% 2.84/1.01  inst_num_moves_active_passive:          7
% 2.84/1.01  inst_lit_activity:                      0
% 2.84/1.01  inst_lit_activity_moves:                0
% 2.84/1.01  inst_num_tautologies:                   0
% 2.84/1.01  inst_num_prop_implied:                  0
% 2.84/1.01  inst_num_existing_simplified:           0
% 2.84/1.01  inst_num_eq_res_simplified:             0
% 2.84/1.01  inst_num_child_elim:                    0
% 2.84/1.01  inst_num_of_dismatching_blockings:      2
% 2.84/1.01  inst_num_of_non_proper_insts:           19
% 2.84/1.01  inst_num_of_duplicates:                 0
% 2.84/1.01  inst_inst_num_from_inst_to_res:         0
% 2.84/1.01  inst_dismatching_checking_time:         0.
% 2.84/1.01  
% 2.84/1.01  ------ Resolution
% 2.84/1.01  
% 2.84/1.01  res_num_of_clauses:                     0
% 2.84/1.01  res_num_in_passive:                     0
% 2.84/1.01  res_num_in_active:                      0
% 2.84/1.01  res_num_of_loops:                       29
% 2.84/1.01  res_forward_subset_subsumed:            1
% 2.84/1.01  res_backward_subset_subsumed:           0
% 2.84/1.01  res_forward_subsumed:                   0
% 2.84/1.01  res_backward_subsumed:                  0
% 2.84/1.01  res_forward_subsumption_resolution:     0
% 2.84/1.01  res_backward_subsumption_resolution:    0
% 2.84/1.01  res_clause_to_clause_subsumption:       12
% 2.84/1.01  res_orphan_elimination:                 0
% 2.84/1.01  res_tautology_del:                      11
% 2.84/1.01  res_num_eq_res_simplified:              0
% 2.84/1.01  res_num_sel_changes:                    0
% 2.84/1.01  res_moves_from_active_to_pass:          0
% 2.84/1.01  
% 2.84/1.01  ------ Superposition
% 2.84/1.01  
% 2.84/1.01  sup_time_total:                         0.
% 2.84/1.01  sup_time_generating:                    0.
% 2.84/1.01  sup_time_sim_full:                      0.
% 2.84/1.01  sup_time_sim_immed:                     0.
% 2.84/1.01  
% 2.84/1.01  sup_num_of_clauses:                     0
% 2.84/1.01  sup_num_in_active:                      0
% 2.84/1.01  sup_num_in_passive:                     0
% 2.84/1.01  sup_num_of_loops:                       0
% 2.84/1.01  sup_fw_superposition:                   0
% 2.84/1.01  sup_bw_superposition:                   0
% 2.84/1.01  sup_immediate_simplified:               0
% 2.84/1.01  sup_given_eliminated:                   0
% 2.84/1.01  comparisons_done:                       0
% 2.84/1.01  comparisons_avoided:                    0
% 2.84/1.01  
% 2.84/1.01  ------ Simplifications
% 2.84/1.01  
% 2.84/1.01  
% 2.84/1.01  sim_fw_subset_subsumed:                 0
% 2.84/1.01  sim_bw_subset_subsumed:                 0
% 2.84/1.01  sim_fw_subsumed:                        0
% 2.84/1.01  sim_bw_subsumed:                        0
% 2.84/1.01  sim_fw_subsumption_res:                 0
% 2.84/1.01  sim_bw_subsumption_res:                 0
% 2.84/1.01  sim_tautology_del:                      0
% 2.84/1.01  sim_eq_tautology_del:                   0
% 2.84/1.01  sim_eq_res_simp:                        0
% 2.84/1.01  sim_fw_demodulated:                     0
% 2.84/1.01  sim_bw_demodulated:                     0
% 2.84/1.01  sim_light_normalised:                   0
% 2.84/1.01  sim_joinable_taut:                      0
% 2.84/1.01  sim_joinable_simp:                      0
% 2.84/1.01  sim_ac_normalised:                      0
% 2.84/1.01  sim_smt_subsumption:                    0
% 2.84/1.01  
%------------------------------------------------------------------------------
