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
% DateTime   : Thu Dec  3 12:20:39 EST 2020

% Result     : CounterSatisfiable 0.70s
% Output     : Model 0.70s
% Verified   : 
% Statistics : Number of formulae       :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :   14 (  14 expanded)
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
    <=> $false ) )).

%------ Positive definition of r2_hidden 
fof(lit_def_002,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
    <=> $true ) )).

%------ Positive definition of m1_subset_1 
fof(lit_def_003,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
    <=> $true ) )).

%------ Negative definition of l1_orders_2 
fof(lit_def_004,axiom,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
    <=> $true ) )).

%------ Negative definition of v3_orders_2 
fof(lit_def_005,axiom,(
    ! [X0] :
      ( ~ v3_orders_2(X0)
    <=> $true ) )).

%------ Positive definition of v2_struct_0 
fof(lit_def_006,axiom,(
    ! [X0] :
      ( v2_struct_0(X0)
    <=> $false ) )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:04:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.70/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.70/1.03  
% 0.70/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.70/1.03  
% 0.70/1.03  ------  iProver source info
% 0.70/1.03  
% 0.70/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.70/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.70/1.03  git: non_committed_changes: false
% 0.70/1.03  git: last_make_outside_of_git: false
% 0.70/1.03  
% 0.70/1.03  ------ 
% 0.70/1.03  
% 0.70/1.03  ------ Input Options
% 0.70/1.03  
% 0.70/1.03  --out_options                           all
% 0.70/1.03  --tptp_safe_out                         true
% 0.70/1.03  --problem_path                          ""
% 0.70/1.03  --include_path                          ""
% 0.70/1.03  --clausifier                            res/vclausify_rel
% 0.70/1.03  --clausifier_options                    --mode clausify
% 0.70/1.03  --stdin                                 false
% 0.70/1.03  --stats_out                             all
% 0.70/1.03  
% 0.70/1.03  ------ General Options
% 0.70/1.03  
% 0.70/1.03  --fof                                   false
% 0.70/1.03  --time_out_real                         305.
% 0.70/1.03  --time_out_virtual                      -1.
% 0.70/1.03  --symbol_type_check                     false
% 0.70/1.03  --clausify_out                          false
% 0.70/1.03  --sig_cnt_out                           false
% 0.70/1.03  --trig_cnt_out                          false
% 0.70/1.03  --trig_cnt_out_tolerance                1.
% 0.70/1.03  --trig_cnt_out_sk_spl                   false
% 0.70/1.03  --abstr_cl_out                          false
% 0.70/1.03  
% 0.70/1.03  ------ Global Options
% 0.70/1.03  
% 0.70/1.03  --schedule                              default
% 0.70/1.03  --add_important_lit                     false
% 0.70/1.03  --prop_solver_per_cl                    1000
% 0.70/1.03  --min_unsat_core                        false
% 0.70/1.03  --soft_assumptions                      false
% 0.70/1.03  --soft_lemma_size                       3
% 0.70/1.03  --prop_impl_unit_size                   0
% 0.70/1.03  --prop_impl_unit                        []
% 0.70/1.03  --share_sel_clauses                     true
% 0.70/1.03  --reset_solvers                         false
% 0.70/1.03  --bc_imp_inh                            [conj_cone]
% 0.70/1.03  --conj_cone_tolerance                   3.
% 0.70/1.03  --extra_neg_conj                        none
% 0.70/1.03  --large_theory_mode                     true
% 0.70/1.03  --prolific_symb_bound                   200
% 0.70/1.03  --lt_threshold                          2000
% 0.70/1.03  --clause_weak_htbl                      true
% 0.70/1.03  --gc_record_bc_elim                     false
% 0.70/1.03  
% 0.70/1.03  ------ Preprocessing Options
% 0.70/1.03  
% 0.70/1.03  --preprocessing_flag                    true
% 0.70/1.03  --time_out_prep_mult                    0.1
% 0.70/1.03  --splitting_mode                        input
% 0.70/1.03  --splitting_grd                         true
% 0.70/1.03  --splitting_cvd                         false
% 0.70/1.03  --splitting_cvd_svl                     false
% 0.70/1.03  --splitting_nvd                         32
% 0.70/1.03  --sub_typing                            true
% 0.70/1.03  --prep_gs_sim                           true
% 0.70/1.03  --prep_unflatten                        true
% 0.70/1.03  --prep_res_sim                          true
% 0.70/1.03  --prep_upred                            true
% 0.70/1.03  --prep_sem_filter                       exhaustive
% 0.70/1.03  --prep_sem_filter_out                   false
% 0.70/1.03  --pred_elim                             true
% 0.70/1.03  --res_sim_input                         true
% 0.70/1.03  --eq_ax_congr_red                       true
% 0.70/1.03  --pure_diseq_elim                       true
% 0.70/1.03  --brand_transform                       false
% 0.70/1.03  --non_eq_to_eq                          false
% 0.70/1.03  --prep_def_merge                        true
% 0.70/1.03  --prep_def_merge_prop_impl              false
% 0.70/1.03  --prep_def_merge_mbd                    true
% 0.70/1.03  --prep_def_merge_tr_red                 false
% 0.70/1.03  --prep_def_merge_tr_cl                  false
% 0.70/1.03  --smt_preprocessing                     true
% 0.70/1.03  --smt_ac_axioms                         fast
% 0.70/1.03  --preprocessed_out                      false
% 0.70/1.03  --preprocessed_stats                    false
% 0.70/1.03  
% 0.70/1.03  ------ Abstraction refinement Options
% 0.70/1.03  
% 0.70/1.03  --abstr_ref                             []
% 0.70/1.03  --abstr_ref_prep                        false
% 0.70/1.03  --abstr_ref_until_sat                   false
% 0.70/1.03  --abstr_ref_sig_restrict                funpre
% 0.70/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.70/1.03  --abstr_ref_under                       []
% 0.70/1.03  
% 0.70/1.03  ------ SAT Options
% 0.70/1.03  
% 0.70/1.03  --sat_mode                              false
% 0.70/1.03  --sat_fm_restart_options                ""
% 0.70/1.03  --sat_gr_def                            false
% 0.70/1.03  --sat_epr_types                         true
% 0.70/1.03  --sat_non_cyclic_types                  false
% 0.70/1.03  --sat_finite_models                     false
% 0.70/1.03  --sat_fm_lemmas                         false
% 0.70/1.03  --sat_fm_prep                           false
% 0.70/1.03  --sat_fm_uc_incr                        true
% 0.70/1.03  --sat_out_model                         small
% 0.70/1.03  --sat_out_clauses                       false
% 0.70/1.03  
% 0.70/1.03  ------ QBF Options
% 0.70/1.03  
% 0.70/1.03  --qbf_mode                              false
% 0.70/1.03  --qbf_elim_univ                         false
% 0.70/1.03  --qbf_dom_inst                          none
% 0.70/1.03  --qbf_dom_pre_inst                      false
% 0.70/1.03  --qbf_sk_in                             false
% 0.70/1.03  --qbf_pred_elim                         true
% 0.70/1.03  --qbf_split                             512
% 0.70/1.03  
% 0.70/1.03  ------ BMC1 Options
% 0.70/1.03  
% 0.70/1.03  --bmc1_incremental                      false
% 0.70/1.03  --bmc1_axioms                           reachable_all
% 0.70/1.03  --bmc1_min_bound                        0
% 0.70/1.03  --bmc1_max_bound                        -1
% 0.70/1.03  --bmc1_max_bound_default                -1
% 0.70/1.03  --bmc1_symbol_reachability              true
% 0.70/1.03  --bmc1_property_lemmas                  false
% 0.70/1.03  --bmc1_k_induction                      false
% 0.70/1.03  --bmc1_non_equiv_states                 false
% 0.70/1.03  --bmc1_deadlock                         false
% 0.70/1.03  --bmc1_ucm                              false
% 0.70/1.03  --bmc1_add_unsat_core                   none
% 0.70/1.04  --bmc1_unsat_core_children              false
% 0.70/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.70/1.04  --bmc1_out_stat                         full
% 0.70/1.04  --bmc1_ground_init                      false
% 0.70/1.04  --bmc1_pre_inst_next_state              false
% 0.70/1.04  --bmc1_pre_inst_state                   false
% 0.70/1.04  --bmc1_pre_inst_reach_state             false
% 0.70/1.04  --bmc1_out_unsat_core                   false
% 0.70/1.04  --bmc1_aig_witness_out                  false
% 0.70/1.04  --bmc1_verbose                          false
% 0.70/1.04  --bmc1_dump_clauses_tptp                false
% 0.70/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.70/1.04  --bmc1_dump_file                        -
% 0.70/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.70/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.70/1.04  --bmc1_ucm_extend_mode                  1
% 0.70/1.04  --bmc1_ucm_init_mode                    2
% 0.70/1.04  --bmc1_ucm_cone_mode                    none
% 0.70/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.70/1.04  --bmc1_ucm_relax_model                  4
% 0.70/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.70/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.70/1.04  --bmc1_ucm_layered_model                none
% 0.70/1.04  --bmc1_ucm_max_lemma_size               10
% 0.70/1.04  
% 0.70/1.04  ------ AIG Options
% 0.70/1.04  
% 0.70/1.04  --aig_mode                              false
% 0.70/1.04  
% 0.70/1.04  ------ Instantiation Options
% 0.70/1.04  
% 0.70/1.04  --instantiation_flag                    true
% 0.70/1.04  --inst_sos_flag                         false
% 0.70/1.04  --inst_sos_phase                        true
% 0.70/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.70/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.70/1.04  --inst_lit_sel_side                     num_symb
% 0.70/1.04  --inst_solver_per_active                1400
% 0.70/1.04  --inst_solver_calls_frac                1.
% 0.70/1.04  --inst_passive_queue_type               priority_queues
% 0.70/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.70/1.04  --inst_passive_queues_freq              [25;2]
% 0.70/1.04  --inst_dismatching                      true
% 0.70/1.04  --inst_eager_unprocessed_to_passive     true
% 0.70/1.04  --inst_prop_sim_given                   true
% 0.70/1.04  --inst_prop_sim_new                     false
% 0.70/1.04  --inst_subs_new                         false
% 0.70/1.04  --inst_eq_res_simp                      false
% 0.70/1.04  --inst_subs_given                       false
% 0.70/1.04  --inst_orphan_elimination               true
% 0.70/1.04  --inst_learning_loop_flag               true
% 0.70/1.04  --inst_learning_start                   3000
% 0.70/1.04  --inst_learning_factor                  2
% 0.70/1.04  --inst_start_prop_sim_after_learn       3
% 0.70/1.04  --inst_sel_renew                        solver
% 0.70/1.04  --inst_lit_activity_flag                true
% 0.70/1.04  --inst_restr_to_given                   false
% 0.70/1.04  --inst_activity_threshold               500
% 0.70/1.04  --inst_out_proof                        true
% 0.70/1.04  
% 0.70/1.04  ------ Resolution Options
% 0.70/1.04  
% 0.70/1.04  --resolution_flag                       true
% 0.70/1.04  --res_lit_sel                           adaptive
% 0.70/1.04  --res_lit_sel_side                      none
% 0.70/1.04  --res_ordering                          kbo
% 0.70/1.04  --res_to_prop_solver                    active
% 0.70/1.04  --res_prop_simpl_new                    false
% 0.70/1.04  --res_prop_simpl_given                  true
% 0.70/1.04  --res_passive_queue_type                priority_queues
% 0.70/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.70/1.04  --res_passive_queues_freq               [15;5]
% 0.70/1.04  --res_forward_subs                      full
% 0.70/1.04  --res_backward_subs                     full
% 0.70/1.04  --res_forward_subs_resolution           true
% 0.70/1.04  --res_backward_subs_resolution          true
% 0.70/1.04  --res_orphan_elimination                true
% 0.70/1.04  --res_time_limit                        2.
% 0.70/1.04  --res_out_proof                         true
% 0.70/1.04  
% 0.70/1.04  ------ Superposition Options
% 0.70/1.04  
% 0.70/1.04  --superposition_flag                    true
% 0.70/1.04  --sup_passive_queue_type                priority_queues
% 0.70/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.70/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.70/1.04  --demod_completeness_check              fast
% 0.70/1.04  --demod_use_ground                      true
% 0.70/1.04  --sup_to_prop_solver                    passive
% 0.70/1.04  --sup_prop_simpl_new                    true
% 0.70/1.04  --sup_prop_simpl_given                  true
% 0.70/1.04  --sup_fun_splitting                     false
% 0.70/1.04  --sup_smt_interval                      50000
% 0.70/1.04  
% 0.70/1.04  ------ Superposition Simplification Setup
% 0.70/1.04  
% 0.70/1.04  --sup_indices_passive                   []
% 0.70/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.70/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/1.04  --sup_full_bw                           [BwDemod]
% 0.70/1.04  --sup_immed_triv                        [TrivRules]
% 0.70/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.70/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/1.04  --sup_immed_bw_main                     []
% 0.70/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.70/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.70/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.70/1.04  
% 0.70/1.04  ------ Combination Options
% 0.70/1.04  
% 0.70/1.04  --comb_res_mult                         3
% 0.70/1.04  --comb_sup_mult                         2
% 0.70/1.04  --comb_inst_mult                        10
% 0.70/1.04  
% 0.70/1.04  ------ Debug Options
% 0.70/1.04  
% 0.70/1.04  --dbg_backtrace                         false
% 0.70/1.04  --dbg_dump_prop_clauses                 false
% 0.70/1.04  --dbg_dump_prop_clauses_file            -
% 0.70/1.04  --dbg_out_stat                          false
% 0.70/1.04  ------ Parsing...
% 0.70/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.70/1.04  
% 0.70/1.04  ------ Preprocessing... sf_s  rm: 35 0s  sf_e  pe_s  pe_e  sf_s  rm: 12 0s  sf_e  pe_s  pe_e 
% 0.70/1.04  
% 0.70/1.04  ------ Preprocessing...------  preprocesses with Option_epr_horn
% 0.70/1.04   gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.70/1.04  ------ Proving...
% 0.70/1.04  ------ Problem Properties 
% 0.70/1.04  
% 0.70/1.04  
% 0.70/1.04  clauses                                 0
% 0.70/1.04  conjectures                             0
% 0.70/1.04  EPR                                     0
% 0.70/1.04  Horn                                    0
% 0.70/1.04  unary                                   0
% 0.70/1.04  binary                                  0
% 0.70/1.04  lits                                    0
% 0.70/1.04  lits eq                                 0
% 0.70/1.04  fd_pure                                 0
% 0.70/1.04  fd_pseudo                               0
% 0.70/1.04  fd_cond                                 0
% 0.70/1.04  fd_pseudo_cond                          0
% 0.70/1.04  AC symbols                              0
% 0.70/1.04  
% 0.70/1.04  ------ Schedule EPR Horn non eq is on
% 0.70/1.04  
% 0.70/1.04  ------ no conjectures: strip conj schedule 
% 0.70/1.04  
% 0.70/1.04  ------ no equalities: superposition off 
% 0.70/1.04  
% 0.70/1.04  ------ pure equality problem: resolution off 
% 0.70/1.04  
% 0.70/1.04  ------ Option_epr_horn stripped conjectures Time Limit: Unbounded
% 0.70/1.04  
% 0.70/1.04  
% 0.70/1.04  ------ 
% 0.70/1.04  Current options:
% 0.70/1.04  ------ 
% 0.70/1.04  
% 0.70/1.04  ------ Input Options
% 0.70/1.04  
% 0.70/1.04  --out_options                           all
% 0.70/1.04  --tptp_safe_out                         true
% 0.70/1.04  --problem_path                          ""
% 0.70/1.04  --include_path                          ""
% 0.70/1.04  --clausifier                            res/vclausify_rel
% 0.70/1.04  --clausifier_options                    --mode clausify
% 0.70/1.04  --stdin                                 false
% 0.70/1.04  --stats_out                             all
% 0.70/1.04  
% 0.70/1.04  ------ General Options
% 0.70/1.04  
% 0.70/1.04  --fof                                   false
% 0.70/1.04  --time_out_real                         305.
% 0.70/1.04  --time_out_virtual                      -1.
% 0.70/1.04  --symbol_type_check                     false
% 0.70/1.04  --clausify_out                          false
% 0.70/1.04  --sig_cnt_out                           false
% 0.70/1.04  --trig_cnt_out                          false
% 0.70/1.04  --trig_cnt_out_tolerance                1.
% 0.70/1.04  --trig_cnt_out_sk_spl                   false
% 0.70/1.04  --abstr_cl_out                          false
% 0.70/1.04  
% 0.70/1.04  ------ Global Options
% 0.70/1.04  
% 0.70/1.04  --schedule                              default
% 0.70/1.04  --add_important_lit                     false
% 0.70/1.04  --prop_solver_per_cl                    1000
% 0.70/1.04  --min_unsat_core                        false
% 0.70/1.04  --soft_assumptions                      false
% 0.70/1.04  --soft_lemma_size                       3
% 0.70/1.04  --prop_impl_unit_size                   0
% 0.70/1.04  --prop_impl_unit                        []
% 0.70/1.04  --share_sel_clauses                     true
% 0.70/1.04  --reset_solvers                         false
% 0.70/1.04  --bc_imp_inh                            []
% 0.70/1.04  --conj_cone_tolerance                   1.5
% 0.70/1.04  --extra_neg_conj                        none
% 0.70/1.04  --large_theory_mode                     true
% 0.70/1.04  --prolific_symb_bound                   500
% 0.70/1.04  --lt_threshold                          2000
% 0.70/1.04  --clause_weak_htbl                      true
% 0.70/1.04  --gc_record_bc_elim                     false
% 0.70/1.04  
% 0.70/1.04  ------ Preprocessing Options
% 0.70/1.04  
% 0.70/1.04  --preprocessing_flag                    true
% 0.70/1.04  --time_out_prep_mult                    0.8
% 0.70/1.04  --splitting_mode                        none
% 0.70/1.04  --splitting_grd                         false
% 0.70/1.04  --splitting_cvd                         false
% 0.70/1.04  --splitting_cvd_svl                     false
% 0.70/1.04  --splitting_nvd                         128
% 0.70/1.04  --sub_typing                            true
% 0.70/1.04  --prep_gs_sim                           true
% 0.70/1.04  --prep_unflatten                        true
% 0.70/1.04  --prep_res_sim                          false
% 0.70/1.04  --prep_upred                            true
% 0.70/1.04  --prep_sem_filter                       exhaustive
% 0.70/1.04  --prep_sem_filter_out                   false
% 0.70/1.04  --pred_elim                             false
% 0.70/1.04  --res_sim_input                         false
% 0.70/1.04  --eq_ax_congr_red                       true
% 0.70/1.04  --pure_diseq_elim                       true
% 0.70/1.04  --brand_transform                       false
% 0.70/1.04  --non_eq_to_eq                          false
% 0.70/1.04  --prep_def_merge                        true
% 0.70/1.04  --prep_def_merge_prop_impl              false
% 0.70/1.04  --prep_def_merge_mbd                    true
% 0.70/1.04  --prep_def_merge_tr_red                 false
% 0.70/1.04  --prep_def_merge_tr_cl                  false
% 0.70/1.04  --smt_preprocessing                     true
% 0.70/1.04  --smt_ac_axioms                         fast
% 0.70/1.04  --preprocessed_out                      false
% 0.70/1.04  --preprocessed_stats                    false
% 0.70/1.04  
% 0.70/1.04  ------ Abstraction refinement Options
% 0.70/1.04  
% 0.70/1.04  --abstr_ref                             []
% 0.70/1.04  --abstr_ref_prep                        false
% 0.70/1.04  --abstr_ref_until_sat                   false
% 0.70/1.04  --abstr_ref_sig_restrict                funpre
% 0.70/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 0.70/1.04  --abstr_ref_under                       []
% 0.70/1.04  
% 0.70/1.04  ------ SAT Options
% 0.70/1.04  
% 0.70/1.04  --sat_mode                              false
% 0.70/1.04  --sat_fm_restart_options                ""
% 0.70/1.04  --sat_gr_def                            false
% 0.70/1.04  --sat_epr_types                         true
% 0.70/1.04  --sat_non_cyclic_types                  false
% 0.70/1.04  --sat_finite_models                     false
% 0.70/1.04  --sat_fm_lemmas                         false
% 0.70/1.04  --sat_fm_prep                           false
% 0.70/1.04  --sat_fm_uc_incr                        true
% 0.70/1.04  --sat_out_model                         small
% 0.70/1.04  --sat_out_clauses                       false
% 0.70/1.04  
% 0.70/1.04  ------ QBF Options
% 0.70/1.04  
% 0.70/1.04  --qbf_mode                              false
% 0.70/1.04  --qbf_elim_univ                         false
% 0.70/1.04  --qbf_dom_inst                          none
% 0.70/1.04  --qbf_dom_pre_inst                      false
% 0.70/1.04  --qbf_sk_in                             false
% 0.70/1.04  --qbf_pred_elim                         true
% 0.70/1.04  --qbf_split                             512
% 0.70/1.04  
% 0.70/1.04  ------ BMC1 Options
% 0.70/1.04  
% 0.70/1.04  --bmc1_incremental                      false
% 0.70/1.04  --bmc1_axioms                           reachable_all
% 0.70/1.04  --bmc1_min_bound                        0
% 0.70/1.04  --bmc1_max_bound                        -1
% 0.70/1.04  --bmc1_max_bound_default                -1
% 0.70/1.04  --bmc1_symbol_reachability              true
% 0.70/1.04  --bmc1_property_lemmas                  false
% 0.70/1.04  --bmc1_k_induction                      false
% 0.70/1.04  --bmc1_non_equiv_states                 false
% 0.70/1.04  --bmc1_deadlock                         false
% 0.70/1.04  --bmc1_ucm                              false
% 0.70/1.04  --bmc1_add_unsat_core                   none
% 0.70/1.04  --bmc1_unsat_core_children              false
% 0.70/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 0.70/1.04  --bmc1_out_stat                         full
% 0.70/1.04  --bmc1_ground_init                      false
% 0.70/1.04  --bmc1_pre_inst_next_state              false
% 0.70/1.04  --bmc1_pre_inst_state                   false
% 0.70/1.04  --bmc1_pre_inst_reach_state             false
% 0.70/1.04  --bmc1_out_unsat_core                   false
% 0.70/1.04  --bmc1_aig_witness_out                  false
% 0.70/1.04  --bmc1_verbose                          false
% 0.70/1.04  --bmc1_dump_clauses_tptp                false
% 0.70/1.04  --bmc1_dump_unsat_core_tptp             false
% 0.70/1.04  --bmc1_dump_file                        -
% 0.70/1.04  --bmc1_ucm_expand_uc_limit              128
% 0.70/1.04  --bmc1_ucm_n_expand_iterations          6
% 0.70/1.04  --bmc1_ucm_extend_mode                  1
% 0.70/1.04  --bmc1_ucm_init_mode                    2
% 0.70/1.04  --bmc1_ucm_cone_mode                    none
% 0.70/1.04  --bmc1_ucm_reduced_relation_type        0
% 0.70/1.04  --bmc1_ucm_relax_model                  4
% 0.70/1.04  --bmc1_ucm_full_tr_after_sat            true
% 0.70/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 0.70/1.04  --bmc1_ucm_layered_model                none
% 0.70/1.04  --bmc1_ucm_max_lemma_size               10
% 0.70/1.04  
% 0.70/1.04  ------ AIG Options
% 0.70/1.04  
% 0.70/1.04  --aig_mode                              false
% 0.70/1.04  
% 0.70/1.04  ------ Instantiation Options
% 0.70/1.04  
% 0.70/1.04  --instantiation_flag                    true
% 0.70/1.04  --inst_sos_flag                         false
% 0.70/1.04  --inst_sos_phase                        true
% 0.70/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.70/1.04  --inst_lit_sel                          [+prop;-num_symb]
% 0.70/1.04  --inst_lit_sel_side                     num_symb
% 0.70/1.04  --inst_solver_per_active                100
% 0.70/1.04  --inst_solver_calls_frac                1.
% 0.70/1.04  --inst_passive_queue_type               priority_queues
% 0.70/1.04  --inst_passive_queues                   [[+ground;+num_symb;+min_def_symb];[-num_lits;+age;+conj_non_prolific_symb]]
% 0.70/1.04  --inst_passive_queues_freq              [1000;5]
% 0.70/1.04  --inst_dismatching                      false
% 0.70/1.04  --inst_eager_unprocessed_to_passive     false
% 0.70/1.04  --inst_prop_sim_given                   false
% 0.70/1.04  --inst_prop_sim_new                     true
% 0.70/1.04  --inst_subs_new                         false
% 0.70/1.04  --inst_eq_res_simp                      false
% 0.70/1.04  --inst_subs_given                       false
% 0.70/1.04  --inst_orphan_elimination               false
% 0.70/1.04  --inst_learning_loop_flag               true
% 0.70/1.04  --inst_learning_start                   3000
% 0.70/1.04  --inst_learning_factor                  4
% 0.70/1.04  --inst_start_prop_sim_after_learn       0
% 0.70/1.04  --inst_sel_renew                        solver
% 0.70/1.04  --inst_lit_activity_flag                true
% 0.70/1.04  --inst_restr_to_given                   true
% 0.70/1.04  --inst_activity_threshold               10000
% 0.70/1.04  --inst_out_proof                        true
% 0.70/1.04  
% 0.70/1.04  ------ Resolution Options
% 0.70/1.04  
% 0.70/1.04  --resolution_flag                       false
% 0.70/1.04  --res_lit_sel                           neg_min
% 0.70/1.04  --res_lit_sel_side                      none
% 0.70/1.04  --res_ordering                          kbo
% 0.70/1.04  --res_to_prop_solver                    active
% 0.70/1.04  --res_prop_simpl_new                    false
% 0.70/1.04  --res_prop_simpl_given                  true
% 0.70/1.04  --res_passive_queue_type                priority_queues
% 0.70/1.04  --res_passive_queues                    [[+conj_non_prolific_symb;-num_symb;-num_symb];[+age;-num_symb]]
% 0.70/1.04  --res_passive_queues_freq               [10;5]
% 0.70/1.04  --res_forward_subs                      subset_subsumption
% 0.70/1.04  --res_backward_subs                     subset_subsumption
% 0.70/1.04  --res_forward_subs_resolution           false
% 0.70/1.04  --res_backward_subs_resolution          false
% 0.70/1.04  --res_orphan_elimination                true
% 0.70/1.04  --res_time_limit                        2.
% 0.70/1.04  --res_out_proof                         true
% 0.70/1.04  
% 0.70/1.04  ------ Superposition Options
% 0.70/1.04  
% 0.70/1.04  --superposition_flag                    false
% 0.70/1.04  --sup_passive_queue_type                priority_queues
% 0.70/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.70/1.04  --sup_passive_queues_freq               [8;1;4]
% 0.70/1.04  --demod_completeness_check              fast
% 0.70/1.04  --demod_use_ground                      true
% 0.70/1.04  --sup_to_prop_solver                    passive
% 0.70/1.04  --sup_prop_simpl_new                    true
% 0.70/1.04  --sup_prop_simpl_given                  true
% 0.70/1.04  --sup_fun_splitting                     false
% 0.70/1.04  --sup_smt_interval                      50000
% 0.70/1.04  
% 0.70/1.04  ------ Superposition Simplification Setup
% 0.70/1.04  
% 0.70/1.04  --sup_indices_passive                   []
% 0.70/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.70/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 0.70/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/1.04  --sup_full_bw                           [BwDemod]
% 0.70/1.04  --sup_immed_triv                        [TrivRules]
% 0.70/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.70/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/1.04  --sup_immed_bw_main                     []
% 0.70/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.70/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 0.70/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.70/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.70/1.04  
% 0.70/1.04  ------ Combination Options
% 0.70/1.04  
% 0.70/1.04  --comb_res_mult                         10
% 0.70/1.04  --comb_sup_mult                         2
% 0.70/1.04  --comb_inst_mult                        3
% 0.70/1.04  
% 0.70/1.04  ------ Debug Options
% 0.70/1.04  
% 0.70/1.04  --dbg_backtrace                         false
% 0.70/1.04  --dbg_dump_prop_clauses                 false
% 0.70/1.04  --dbg_dump_prop_clauses_file            -
% 0.70/1.04  --dbg_out_stat                          false
% 0.70/1.04  
% 0.70/1.04  
% 0.70/1.04  
% 0.70/1.04  
% 0.70/1.04  ------ Proving...
% 0.70/1.04  
% 0.70/1.04  
% 0.70/1.04  % SZS status CounterSatisfiable for theBenchmark.p
% 0.70/1.04  
% 0.70/1.04  ------ Building Model...Done
% 0.70/1.04  
% 0.70/1.04  %------ The model is defined over ground terms (initial term algebra).
% 0.70/1.04  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 0.70/1.04  %------ where \phi is a formula over the term algebra.
% 0.70/1.04  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 0.70/1.04  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 0.70/1.04  %------ See help for --sat_out_model for different model outputs.
% 0.70/1.04  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 0.70/1.04  %------ where the first argument stands for the sort ($i in the unsorted case)
% 0.70/1.04  % SZS output start Model for theBenchmark.p
% 0.70/1.04  
% 0.70/1.04  %------ Negative definition of equality_sorted 
% 0.70/1.04  fof(lit_def,axiom,
% 0.70/1.04      (! [X0_0,X0,X1] : 
% 0.70/1.04        ( ~(equality_sorted(X0_0,X0,X1)) <=>
% 0.70/1.04            $false
% 0.70/1.04        )
% 0.70/1.04      )
% 0.70/1.04     ).
% 0.70/1.04  
% 0.70/1.04  %------ Positive definition of v1_xboole_0 
% 0.70/1.04  fof(lit_def,axiom,
% 0.70/1.04      (! [X0] : 
% 0.70/1.04        ( v1_xboole_0(X0) <=>
% 0.70/1.04            $false
% 0.70/1.04        )
% 0.70/1.04      )
% 0.70/1.04     ).
% 0.70/1.04  
% 0.70/1.04  %------ Positive definition of r2_hidden 
% 0.70/1.04  fof(lit_def,axiom,
% 0.70/1.04      (! [X0,X1] : 
% 0.70/1.04        ( r2_hidden(X0,X1) <=>
% 0.70/1.04            $true
% 0.70/1.04        )
% 0.70/1.04      )
% 0.70/1.04     ).
% 0.70/1.04  
% 0.70/1.04  %------ Positive definition of m1_subset_1 
% 0.70/1.04  fof(lit_def,axiom,
% 0.70/1.04      (! [X0,X1] : 
% 0.70/1.04        ( m1_subset_1(X0,X1) <=>
% 0.70/1.04            $true
% 0.70/1.04        )
% 0.70/1.04      )
% 0.70/1.04     ).
% 0.70/1.04  
% 0.70/1.04  %------ Negative definition of l1_orders_2 
% 0.70/1.04  fof(lit_def,axiom,
% 0.70/1.04      (! [X0] : 
% 0.70/1.04        ( ~(l1_orders_2(X0)) <=>
% 0.70/1.04            $true
% 0.70/1.04        )
% 0.70/1.04      )
% 0.70/1.04     ).
% 0.70/1.04  
% 0.70/1.04  %------ Negative definition of v3_orders_2 
% 0.70/1.04  fof(lit_def,axiom,
% 0.70/1.04      (! [X0] : 
% 0.70/1.04        ( ~(v3_orders_2(X0)) <=>
% 0.70/1.04            $true
% 0.70/1.04        )
% 0.70/1.04      )
% 0.70/1.04     ).
% 0.70/1.04  
% 0.70/1.04  %------ Positive definition of v2_struct_0 
% 0.70/1.04  fof(lit_def,axiom,
% 0.70/1.04      (! [X0] : 
% 0.70/1.04        ( v2_struct_0(X0) <=>
% 0.70/1.04            $false
% 0.70/1.04        )
% 0.70/1.04      )
% 0.70/1.04     ).
% 0.70/1.04  % SZS output end Model for theBenchmark.p
% 0.70/1.04  ------                               Statistics
% 0.70/1.04  
% 0.70/1.04  ------ General
% 0.70/1.04  
% 0.70/1.04  abstr_ref_over_cycles:                  0
% 0.70/1.04  abstr_ref_under_cycles:                 0
% 0.70/1.04  gc_basic_clause_elim:                   0
% 0.70/1.04  forced_gc_time:                         0
% 0.70/1.04  parsing_time:                           0.013
% 0.70/1.04  unif_index_cands_time:                  0.
% 0.70/1.04  unif_index_add_time:                    0.
% 0.70/1.04  orderings_time:                         0.
% 0.70/1.04  out_proof_time:                         0.
% 0.70/1.04  total_time:                             0.045
% 0.70/1.04  num_of_symbols:                         46
% 0.70/1.04  num_of_terms:                           390
% 0.70/1.04  
% 0.70/1.04  ------ Preprocessing
% 0.70/1.04  
% 0.70/1.04  num_of_splits:                          0
% 0.70/1.04  num_of_split_atoms:                     0
% 0.70/1.04  num_of_reused_defs:                     0
% 0.70/1.04  num_eq_ax_congr_red:                    9
% 0.70/1.04  num_of_sem_filtered_clauses:            23
% 0.70/1.04  num_of_subtypes:                        0
% 0.70/1.04  monotx_restored_types:                  0
% 0.70/1.04  sat_num_of_epr_types:                   0
% 0.70/1.04  sat_num_of_non_cyclic_types:            0
% 0.70/1.04  sat_guarded_non_collapsed_types:        0
% 0.70/1.04  num_pure_diseq_elim:                    0
% 0.70/1.04  simp_replaced_by:                       0
% 0.70/1.04  res_preprocessed:                       23
% 0.70/1.04  prep_upred:                             0
% 0.70/1.04  prep_unflattend:                        0
% 0.70/1.04  smt_new_axioms:                         0
% 0.70/1.04  pred_elim_cands:                        0
% 0.70/1.04  pred_elim:                              0
% 0.70/1.04  pred_elim_cl:                           0
% 0.70/1.04  pred_elim_cycles:                       0
% 0.70/1.04  merged_defs:                            0
% 0.70/1.04  merged_defs_ncl:                        0
% 0.70/1.04  bin_hyper_res:                          0
% 0.70/1.04  prep_cycles:                            2
% 0.70/1.04  pred_elim_time:                         0.
% 0.70/1.04  splitting_time:                         0.
% 0.70/1.04  sem_filter_time:                        0.
% 0.70/1.04  monotx_time:                            0.
% 0.70/1.04  subtype_inf_time:                       0.
% 0.70/1.04  
% 0.70/1.04  ------ Problem properties
% 0.70/1.04  
% 0.70/1.04  clauses:                                0
% 0.70/1.04  conjectures:                            0
% 0.70/1.04  epr:                                    0
% 0.70/1.04  horn:                                   0
% 0.70/1.04  ground:                                 0
% 0.70/1.04  unary:                                  0
% 0.70/1.04  binary:                                 0
% 0.70/1.04  lits:                                   0
% 0.70/1.04  lits_eq:                                0
% 0.70/1.04  fd_pure:                                0
% 0.70/1.04  fd_pseudo:                              0
% 0.70/1.04  fd_cond:                                0
% 0.70/1.04  fd_pseudo_cond:                         0
% 0.70/1.04  ac_symbols:                             0
% 0.70/1.04  
% 0.70/1.04  ------ Propositional Solver
% 0.70/1.04  
% 0.70/1.04  prop_solver_calls:                      12
% 0.70/1.04  prop_fast_solver_calls:                 104
% 0.70/1.04  smt_solver_calls:                       0
% 0.70/1.04  smt_fast_solver_calls:                  0
% 0.70/1.04  prop_num_of_clauses:                    74
% 0.70/1.04  prop_preprocess_simplified:             530
% 0.70/1.04  prop_fo_subsumed:                       0
% 0.70/1.04  prop_solver_time:                       0.
% 0.70/1.04  smt_solver_time:                        0.
% 0.70/1.04  smt_fast_solver_time:                   0.
% 0.70/1.04  prop_fast_solver_time:                  0.
% 0.70/1.04  prop_unsat_core_time:                   0.
% 0.70/1.04  
% 0.70/1.04  ------ QBF
% 0.70/1.04  
% 0.70/1.04  qbf_q_res:                              0
% 0.70/1.04  qbf_num_tautologies:                    0
% 0.70/1.04  qbf_prep_cycles:                        0
% 0.70/1.04  
% 0.70/1.04  ------ BMC1
% 0.70/1.04  
% 0.70/1.04  bmc1_current_bound:                     -1
% 0.70/1.04  bmc1_last_solved_bound:                 -1
% 0.70/1.04  bmc1_unsat_core_size:                   -1
% 0.70/1.04  bmc1_unsat_core_parents_size:           -1
% 0.70/1.04  bmc1_merge_next_fun:                    0
% 0.70/1.04  bmc1_unsat_core_clauses_time:           0.
% 0.70/1.04  
% 0.70/1.04  ------ Instantiation
% 0.70/1.04  
% 0.70/1.04  inst_num_of_clauses:                    0
% 0.70/1.04  inst_num_in_passive:                    0
% 0.70/1.04  inst_num_in_active:                     0
% 0.70/1.04  inst_num_in_unprocessed:                0
% 0.70/1.04  inst_num_of_loops:                      1
% 0.70/1.04  inst_num_of_learning_restarts:          0
% 0.70/1.04  inst_num_moves_active_passive:          0
% 0.70/1.04  inst_lit_activity:                      0
% 0.70/1.04  inst_lit_activity_moves:                0
% 0.70/1.04  inst_num_tautologies:                   0
% 0.70/1.04  inst_num_prop_implied:                  0
% 0.70/1.04  inst_num_existing_simplified:           0
% 0.70/1.04  inst_num_eq_res_simplified:             0
% 0.70/1.04  inst_num_child_elim:                    0
% 0.70/1.04  inst_num_of_dismatching_blockings:      0
% 0.70/1.04  inst_num_of_non_proper_insts:           0
% 0.70/1.04  inst_num_of_duplicates:                 0
% 0.70/1.04  inst_inst_num_from_inst_to_res:         0
% 0.70/1.04  inst_dismatching_checking_time:         0.
% 0.70/1.04  
% 0.70/1.04  ------ Resolution
% 0.70/1.04  
% 0.70/1.04  res_num_of_clauses:                     0
% 0.70/1.04  res_num_in_passive:                     0
% 0.70/1.04  res_num_in_active:                      0
% 0.70/1.04  res_num_of_loops:                       25
% 0.70/1.04  res_forward_subset_subsumed:            0
% 0.70/1.04  res_backward_subset_subsumed:           0
% 0.70/1.04  res_forward_subsumed:                   0
% 0.70/1.04  res_backward_subsumed:                  0
% 0.70/1.04  res_forward_subsumption_resolution:     0
% 0.70/1.04  res_backward_subsumption_resolution:    0
% 0.70/1.04  res_clause_to_clause_subsumption:       0
% 0.70/1.04  res_orphan_elimination:                 0
% 0.70/1.04  res_tautology_del:                      0
% 0.70/1.04  res_num_eq_res_simplified:              0
% 0.70/1.04  res_num_sel_changes:                    0
% 0.70/1.04  res_moves_from_active_to_pass:          0
% 0.70/1.04  
% 0.70/1.04  ------ Superposition
% 0.70/1.04  
% 0.70/1.04  sup_time_total:                         0.
% 0.70/1.04  sup_time_generating:                    0.
% 0.70/1.04  sup_time_sim_full:                      0.
% 0.70/1.04  sup_time_sim_immed:                     0.
% 0.70/1.04  
% 0.70/1.04  sup_num_of_clauses:                     0
% 0.70/1.04  sup_num_in_active:                      0
% 0.70/1.04  sup_num_in_passive:                     0
% 0.70/1.04  sup_num_of_loops:                       0
% 0.70/1.04  sup_fw_superposition:                   0
% 0.70/1.04  sup_bw_superposition:                   0
% 0.70/1.04  sup_immediate_simplified:               0
% 0.70/1.04  sup_given_eliminated:                   0
% 0.70/1.04  comparisons_done:                       0
% 0.70/1.04  comparisons_avoided:                    0
% 0.70/1.04  
% 0.70/1.04  ------ Simplifications
% 0.70/1.04  
% 0.70/1.04  
% 0.70/1.04  sim_fw_subset_subsumed:                 0
% 0.70/1.04  sim_bw_subset_subsumed:                 0
% 0.70/1.04  sim_fw_subsumed:                        0
% 0.70/1.04  sim_bw_subsumed:                        0
% 0.70/1.04  sim_fw_subsumption_res:                 0
% 0.70/1.04  sim_bw_subsumption_res:                 0
% 0.70/1.04  sim_tautology_del:                      0
% 0.70/1.04  sim_eq_tautology_del:                   0
% 0.70/1.04  sim_eq_res_simp:                        0
% 0.70/1.04  sim_fw_demodulated:                     0
% 0.70/1.04  sim_bw_demodulated:                     0
% 0.70/1.04  sim_light_normalised:                   0
% 0.70/1.04  sim_joinable_taut:                      0
% 0.70/1.04  sim_joinable_simp:                      0
% 0.70/1.04  sim_ac_normalised:                      0
% 0.70/1.04  sim_smt_subsumption:                    0
% 0.70/1.04  
%------------------------------------------------------------------------------
