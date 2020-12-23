%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:17 EST 2020

% Result     : CounterSatisfiable 1.26s
% Output     : Model 1.26s
% Verified   : 
% Statistics : Number of formulae       :    2 (   2 expanded)
%              Number of leaves         :    2 (   2 expanded)
%              Depth                    :    0
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   11 (   8 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%------ Positive definition of r1_xboole_0 
fof(lit_def,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> ( ( X0 = sK0
          & X1 = k3_xboole_0(sK1,sK2) )
        | ( X0 = k3_xboole_0(sK1,sK2)
          & X1 = sK0 ) ) ) )).

%------ Negative definition of r1_tarski 
fof(lit_def_001,axiom,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
    <=> ( ? [X2] :
            ( X0 = k3_xboole_0(X2,sK0)
            & X1 = k3_xboole_0(sK1,sK2) )
        | ? [X2,X3] :
            ( X0 = k3_xboole_0(X2,X3)
            & X1 = k3_xboole_0(sK1,sK2)
            & X3 != sK0 )
        | X1 = sK1
        | X1 = k3_xboole_0(sK1,sK2) ) ) )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:43:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.26/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.26/1.00  
% 1.26/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.26/1.00  
% 1.26/1.00  ------  iProver source info
% 1.26/1.00  
% 1.26/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.26/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.26/1.00  git: non_committed_changes: false
% 1.26/1.00  git: last_make_outside_of_git: false
% 1.26/1.00  
% 1.26/1.00  ------ 
% 1.26/1.00  
% 1.26/1.00  ------ Input Options
% 1.26/1.00  
% 1.26/1.00  --out_options                           all
% 1.26/1.00  --tptp_safe_out                         true
% 1.26/1.00  --problem_path                          ""
% 1.26/1.00  --include_path                          ""
% 1.26/1.00  --clausifier                            res/vclausify_rel
% 1.26/1.00  --clausifier_options                    --mode clausify
% 1.26/1.00  --stdin                                 false
% 1.26/1.00  --stats_out                             all
% 1.26/1.00  
% 1.26/1.00  ------ General Options
% 1.26/1.00  
% 1.26/1.00  --fof                                   false
% 1.26/1.00  --time_out_real                         305.
% 1.26/1.00  --time_out_virtual                      -1.
% 1.26/1.00  --symbol_type_check                     false
% 1.26/1.00  --clausify_out                          false
% 1.26/1.00  --sig_cnt_out                           false
% 1.26/1.00  --trig_cnt_out                          false
% 1.26/1.00  --trig_cnt_out_tolerance                1.
% 1.26/1.00  --trig_cnt_out_sk_spl                   false
% 1.26/1.00  --abstr_cl_out                          false
% 1.26/1.00  
% 1.26/1.00  ------ Global Options
% 1.26/1.00  
% 1.26/1.00  --schedule                              default
% 1.26/1.00  --add_important_lit                     false
% 1.26/1.00  --prop_solver_per_cl                    1000
% 1.26/1.00  --min_unsat_core                        false
% 1.26/1.00  --soft_assumptions                      false
% 1.26/1.00  --soft_lemma_size                       3
% 1.26/1.00  --prop_impl_unit_size                   0
% 1.26/1.00  --prop_impl_unit                        []
% 1.26/1.00  --share_sel_clauses                     true
% 1.26/1.00  --reset_solvers                         false
% 1.26/1.00  --bc_imp_inh                            [conj_cone]
% 1.26/1.00  --conj_cone_tolerance                   3.
% 1.26/1.00  --extra_neg_conj                        none
% 1.26/1.00  --large_theory_mode                     true
% 1.26/1.00  --prolific_symb_bound                   200
% 1.26/1.00  --lt_threshold                          2000
% 1.26/1.00  --clause_weak_htbl                      true
% 1.26/1.00  --gc_record_bc_elim                     false
% 1.26/1.00  
% 1.26/1.00  ------ Preprocessing Options
% 1.26/1.00  
% 1.26/1.00  --preprocessing_flag                    true
% 1.26/1.00  --time_out_prep_mult                    0.1
% 1.26/1.00  --splitting_mode                        input
% 1.26/1.00  --splitting_grd                         true
% 1.26/1.00  --splitting_cvd                         false
% 1.26/1.00  --splitting_cvd_svl                     false
% 1.26/1.00  --splitting_nvd                         32
% 1.26/1.00  --sub_typing                            true
% 1.26/1.00  --prep_gs_sim                           true
% 1.26/1.00  --prep_unflatten                        true
% 1.26/1.00  --prep_res_sim                          true
% 1.26/1.00  --prep_upred                            true
% 1.26/1.00  --prep_sem_filter                       exhaustive
% 1.26/1.00  --prep_sem_filter_out                   false
% 1.26/1.00  --pred_elim                             true
% 1.26/1.00  --res_sim_input                         true
% 1.26/1.00  --eq_ax_congr_red                       true
% 1.26/1.00  --pure_diseq_elim                       true
% 1.26/1.00  --brand_transform                       false
% 1.26/1.00  --non_eq_to_eq                          false
% 1.26/1.00  --prep_def_merge                        true
% 1.26/1.00  --prep_def_merge_prop_impl              false
% 1.26/1.00  --prep_def_merge_mbd                    true
% 1.26/1.00  --prep_def_merge_tr_red                 false
% 1.26/1.00  --prep_def_merge_tr_cl                  false
% 1.26/1.00  --smt_preprocessing                     true
% 1.26/1.00  --smt_ac_axioms                         fast
% 1.26/1.00  --preprocessed_out                      false
% 1.26/1.00  --preprocessed_stats                    false
% 1.26/1.00  
% 1.26/1.00  ------ Abstraction refinement Options
% 1.26/1.00  
% 1.26/1.00  --abstr_ref                             []
% 1.26/1.00  --abstr_ref_prep                        false
% 1.26/1.00  --abstr_ref_until_sat                   false
% 1.26/1.00  --abstr_ref_sig_restrict                funpre
% 1.26/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.26/1.00  --abstr_ref_under                       []
% 1.26/1.00  
% 1.26/1.00  ------ SAT Options
% 1.26/1.00  
% 1.26/1.00  --sat_mode                              false
% 1.26/1.00  --sat_fm_restart_options                ""
% 1.26/1.00  --sat_gr_def                            false
% 1.26/1.00  --sat_epr_types                         true
% 1.26/1.00  --sat_non_cyclic_types                  false
% 1.26/1.00  --sat_finite_models                     false
% 1.26/1.00  --sat_fm_lemmas                         false
% 1.26/1.00  --sat_fm_prep                           false
% 1.26/1.00  --sat_fm_uc_incr                        true
% 1.26/1.00  --sat_out_model                         small
% 1.26/1.00  --sat_out_clauses                       false
% 1.26/1.00  
% 1.26/1.00  ------ QBF Options
% 1.26/1.00  
% 1.26/1.00  --qbf_mode                              false
% 1.26/1.00  --qbf_elim_univ                         false
% 1.26/1.00  --qbf_dom_inst                          none
% 1.26/1.00  --qbf_dom_pre_inst                      false
% 1.26/1.00  --qbf_sk_in                             false
% 1.26/1.00  --qbf_pred_elim                         true
% 1.26/1.00  --qbf_split                             512
% 1.26/1.00  
% 1.26/1.00  ------ BMC1 Options
% 1.26/1.00  
% 1.26/1.00  --bmc1_incremental                      false
% 1.26/1.00  --bmc1_axioms                           reachable_all
% 1.26/1.00  --bmc1_min_bound                        0
% 1.26/1.00  --bmc1_max_bound                        -1
% 1.26/1.00  --bmc1_max_bound_default                -1
% 1.26/1.00  --bmc1_symbol_reachability              true
% 1.26/1.00  --bmc1_property_lemmas                  false
% 1.26/1.00  --bmc1_k_induction                      false
% 1.26/1.00  --bmc1_non_equiv_states                 false
% 1.26/1.00  --bmc1_deadlock                         false
% 1.26/1.00  --bmc1_ucm                              false
% 1.26/1.00  --bmc1_add_unsat_core                   none
% 1.26/1.00  --bmc1_unsat_core_children              false
% 1.26/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.26/1.00  --bmc1_out_stat                         full
% 1.26/1.00  --bmc1_ground_init                      false
% 1.26/1.00  --bmc1_pre_inst_next_state              false
% 1.26/1.00  --bmc1_pre_inst_state                   false
% 1.26/1.00  --bmc1_pre_inst_reach_state             false
% 1.26/1.00  --bmc1_out_unsat_core                   false
% 1.26/1.00  --bmc1_aig_witness_out                  false
% 1.26/1.00  --bmc1_verbose                          false
% 1.26/1.00  --bmc1_dump_clauses_tptp                false
% 1.26/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.26/1.00  --bmc1_dump_file                        -
% 1.26/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.26/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.26/1.00  --bmc1_ucm_extend_mode                  1
% 1.26/1.00  --bmc1_ucm_init_mode                    2
% 1.26/1.00  --bmc1_ucm_cone_mode                    none
% 1.26/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.26/1.00  --bmc1_ucm_relax_model                  4
% 1.26/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.26/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.26/1.00  --bmc1_ucm_layered_model                none
% 1.26/1.00  --bmc1_ucm_max_lemma_size               10
% 1.26/1.00  
% 1.26/1.00  ------ AIG Options
% 1.26/1.00  
% 1.26/1.00  --aig_mode                              false
% 1.26/1.00  
% 1.26/1.00  ------ Instantiation Options
% 1.26/1.00  
% 1.26/1.00  --instantiation_flag                    true
% 1.26/1.00  --inst_sos_flag                         false
% 1.26/1.00  --inst_sos_phase                        true
% 1.26/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.26/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.26/1.00  --inst_lit_sel_side                     num_symb
% 1.26/1.00  --inst_solver_per_active                1400
% 1.26/1.00  --inst_solver_calls_frac                1.
% 1.26/1.00  --inst_passive_queue_type               priority_queues
% 1.26/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.26/1.00  --inst_passive_queues_freq              [25;2]
% 1.26/1.00  --inst_dismatching                      true
% 1.26/1.00  --inst_eager_unprocessed_to_passive     true
% 1.26/1.00  --inst_prop_sim_given                   true
% 1.26/1.00  --inst_prop_sim_new                     false
% 1.26/1.00  --inst_subs_new                         false
% 1.26/1.00  --inst_eq_res_simp                      false
% 1.26/1.00  --inst_subs_given                       false
% 1.26/1.00  --inst_orphan_elimination               true
% 1.26/1.00  --inst_learning_loop_flag               true
% 1.26/1.00  --inst_learning_start                   3000
% 1.26/1.00  --inst_learning_factor                  2
% 1.26/1.00  --inst_start_prop_sim_after_learn       3
% 1.26/1.00  --inst_sel_renew                        solver
% 1.26/1.00  --inst_lit_activity_flag                true
% 1.26/1.00  --inst_restr_to_given                   false
% 1.26/1.00  --inst_activity_threshold               500
% 1.26/1.00  --inst_out_proof                        true
% 1.26/1.00  
% 1.26/1.00  ------ Resolution Options
% 1.26/1.00  
% 1.26/1.00  --resolution_flag                       true
% 1.26/1.00  --res_lit_sel                           adaptive
% 1.26/1.00  --res_lit_sel_side                      none
% 1.26/1.00  --res_ordering                          kbo
% 1.26/1.00  --res_to_prop_solver                    active
% 1.26/1.00  --res_prop_simpl_new                    false
% 1.26/1.00  --res_prop_simpl_given                  true
% 1.26/1.00  --res_passive_queue_type                priority_queues
% 1.26/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.26/1.00  --res_passive_queues_freq               [15;5]
% 1.26/1.00  --res_forward_subs                      full
% 1.26/1.00  --res_backward_subs                     full
% 1.26/1.00  --res_forward_subs_resolution           true
% 1.26/1.00  --res_backward_subs_resolution          true
% 1.26/1.00  --res_orphan_elimination                true
% 1.26/1.00  --res_time_limit                        2.
% 1.26/1.00  --res_out_proof                         true
% 1.26/1.00  
% 1.26/1.00  ------ Superposition Options
% 1.26/1.00  
% 1.26/1.00  --superposition_flag                    true
% 1.26/1.00  --sup_passive_queue_type                priority_queues
% 1.26/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.26/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.26/1.00  --demod_completeness_check              fast
% 1.26/1.00  --demod_use_ground                      true
% 1.26/1.00  --sup_to_prop_solver                    passive
% 1.26/1.00  --sup_prop_simpl_new                    true
% 1.26/1.00  --sup_prop_simpl_given                  true
% 1.26/1.00  --sup_fun_splitting                     false
% 1.26/1.00  --sup_smt_interval                      50000
% 1.26/1.00  
% 1.26/1.00  ------ Superposition Simplification Setup
% 1.26/1.00  
% 1.26/1.00  --sup_indices_passive                   []
% 1.26/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.26/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.26/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.26/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.26/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.26/1.00  --sup_full_bw                           [BwDemod]
% 1.26/1.00  --sup_immed_triv                        [TrivRules]
% 1.26/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.26/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.26/1.00  --sup_immed_bw_main                     []
% 1.26/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.26/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.26/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.26/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.26/1.00  
% 1.26/1.00  ------ Combination Options
% 1.26/1.00  
% 1.26/1.00  --comb_res_mult                         3
% 1.26/1.00  --comb_sup_mult                         2
% 1.26/1.00  --comb_inst_mult                        10
% 1.26/1.00  
% 1.26/1.00  ------ Debug Options
% 1.26/1.00  
% 1.26/1.00  --dbg_backtrace                         false
% 1.26/1.00  --dbg_dump_prop_clauses                 false
% 1.26/1.00  --dbg_dump_prop_clauses_file            -
% 1.26/1.00  --dbg_out_stat                          false
% 1.26/1.00  ------ Parsing...
% 1.26/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.26/1.00  
% 1.26/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.26/1.00  
% 1.26/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.26/1.00  ------ Proving...
% 1.26/1.00  ------ Problem Properties 
% 1.26/1.00  
% 1.26/1.00  
% 1.26/1.00  clauses                                 7
% 1.26/1.00  conjectures                             3
% 1.26/1.00  EPR                                     4
% 1.26/1.00  Horn                                    7
% 1.26/1.00  unary                                   3
% 1.26/1.00  binary                                  2
% 1.26/1.00  lits                                    14
% 1.26/1.00  lits eq                                 0
% 1.26/1.00  fd_pure                                 0
% 1.26/1.00  fd_pseudo                               0
% 1.26/1.00  fd_cond                                 0
% 1.26/1.00  fd_pseudo_cond                          0
% 1.26/1.00  AC symbols                              0
% 1.26/1.00  
% 1.26/1.00  ------ Schedule dynamic 5 is on 
% 1.26/1.00  
% 1.26/1.00  ------ no equalities: superposition off 
% 1.26/1.00  
% 1.26/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.26/1.00  
% 1.26/1.00  
% 1.26/1.00  ------ 
% 1.26/1.00  Current options:
% 1.26/1.00  ------ 
% 1.26/1.00  
% 1.26/1.00  ------ Input Options
% 1.26/1.00  
% 1.26/1.00  --out_options                           all
% 1.26/1.00  --tptp_safe_out                         true
% 1.26/1.00  --problem_path                          ""
% 1.26/1.00  --include_path                          ""
% 1.26/1.00  --clausifier                            res/vclausify_rel
% 1.26/1.00  --clausifier_options                    --mode clausify
% 1.26/1.00  --stdin                                 false
% 1.26/1.00  --stats_out                             all
% 1.26/1.00  
% 1.26/1.00  ------ General Options
% 1.26/1.00  
% 1.26/1.00  --fof                                   false
% 1.26/1.00  --time_out_real                         305.
% 1.26/1.00  --time_out_virtual                      -1.
% 1.26/1.00  --symbol_type_check                     false
% 1.26/1.00  --clausify_out                          false
% 1.26/1.00  --sig_cnt_out                           false
% 1.26/1.00  --trig_cnt_out                          false
% 1.26/1.00  --trig_cnt_out_tolerance                1.
% 1.26/1.00  --trig_cnt_out_sk_spl                   false
% 1.26/1.00  --abstr_cl_out                          false
% 1.26/1.00  
% 1.26/1.00  ------ Global Options
% 1.26/1.00  
% 1.26/1.00  --schedule                              default
% 1.26/1.00  --add_important_lit                     false
% 1.26/1.00  --prop_solver_per_cl                    1000
% 1.26/1.00  --min_unsat_core                        false
% 1.26/1.00  --soft_assumptions                      false
% 1.26/1.00  --soft_lemma_size                       3
% 1.26/1.00  --prop_impl_unit_size                   0
% 1.26/1.00  --prop_impl_unit                        []
% 1.26/1.00  --share_sel_clauses                     true
% 1.26/1.00  --reset_solvers                         false
% 1.26/1.00  --bc_imp_inh                            [conj_cone]
% 1.26/1.00  --conj_cone_tolerance                   3.
% 1.26/1.00  --extra_neg_conj                        none
% 1.26/1.00  --large_theory_mode                     true
% 1.26/1.00  --prolific_symb_bound                   200
% 1.26/1.00  --lt_threshold                          2000
% 1.26/1.00  --clause_weak_htbl                      true
% 1.26/1.00  --gc_record_bc_elim                     false
% 1.26/1.00  
% 1.26/1.00  ------ Preprocessing Options
% 1.26/1.00  
% 1.26/1.00  --preprocessing_flag                    true
% 1.26/1.00  --time_out_prep_mult                    0.1
% 1.26/1.00  --splitting_mode                        input
% 1.26/1.00  --splitting_grd                         true
% 1.26/1.00  --splitting_cvd                         false
% 1.26/1.00  --splitting_cvd_svl                     false
% 1.26/1.00  --splitting_nvd                         32
% 1.26/1.00  --sub_typing                            true
% 1.26/1.00  --prep_gs_sim                           true
% 1.26/1.00  --prep_unflatten                        true
% 1.26/1.00  --prep_res_sim                          true
% 1.26/1.00  --prep_upred                            true
% 1.26/1.00  --prep_sem_filter                       exhaustive
% 1.26/1.00  --prep_sem_filter_out                   false
% 1.26/1.00  --pred_elim                             true
% 1.26/1.00  --res_sim_input                         true
% 1.26/1.00  --eq_ax_congr_red                       true
% 1.26/1.00  --pure_diseq_elim                       true
% 1.26/1.00  --brand_transform                       false
% 1.26/1.00  --non_eq_to_eq                          false
% 1.26/1.00  --prep_def_merge                        true
% 1.26/1.00  --prep_def_merge_prop_impl              false
% 1.26/1.00  --prep_def_merge_mbd                    true
% 1.26/1.00  --prep_def_merge_tr_red                 false
% 1.26/1.00  --prep_def_merge_tr_cl                  false
% 1.26/1.00  --smt_preprocessing                     true
% 1.26/1.00  --smt_ac_axioms                         fast
% 1.26/1.00  --preprocessed_out                      false
% 1.26/1.00  --preprocessed_stats                    false
% 1.26/1.00  
% 1.26/1.00  ------ Abstraction refinement Options
% 1.26/1.00  
% 1.26/1.00  --abstr_ref                             []
% 1.26/1.00  --abstr_ref_prep                        false
% 1.26/1.00  --abstr_ref_until_sat                   false
% 1.26/1.00  --abstr_ref_sig_restrict                funpre
% 1.26/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.26/1.00  --abstr_ref_under                       []
% 1.26/1.00  
% 1.26/1.00  ------ SAT Options
% 1.26/1.00  
% 1.26/1.00  --sat_mode                              false
% 1.26/1.00  --sat_fm_restart_options                ""
% 1.26/1.00  --sat_gr_def                            false
% 1.26/1.00  --sat_epr_types                         true
% 1.26/1.00  --sat_non_cyclic_types                  false
% 1.26/1.00  --sat_finite_models                     false
% 1.26/1.00  --sat_fm_lemmas                         false
% 1.26/1.00  --sat_fm_prep                           false
% 1.26/1.00  --sat_fm_uc_incr                        true
% 1.26/1.00  --sat_out_model                         small
% 1.26/1.00  --sat_out_clauses                       false
% 1.26/1.00  
% 1.26/1.00  ------ QBF Options
% 1.26/1.00  
% 1.26/1.00  --qbf_mode                              false
% 1.26/1.00  --qbf_elim_univ                         false
% 1.26/1.00  --qbf_dom_inst                          none
% 1.26/1.00  --qbf_dom_pre_inst                      false
% 1.26/1.00  --qbf_sk_in                             false
% 1.26/1.00  --qbf_pred_elim                         true
% 1.26/1.00  --qbf_split                             512
% 1.26/1.00  
% 1.26/1.00  ------ BMC1 Options
% 1.26/1.00  
% 1.26/1.00  --bmc1_incremental                      false
% 1.26/1.00  --bmc1_axioms                           reachable_all
% 1.26/1.00  --bmc1_min_bound                        0
% 1.26/1.00  --bmc1_max_bound                        -1
% 1.26/1.00  --bmc1_max_bound_default                -1
% 1.26/1.00  --bmc1_symbol_reachability              true
% 1.26/1.00  --bmc1_property_lemmas                  false
% 1.26/1.00  --bmc1_k_induction                      false
% 1.26/1.00  --bmc1_non_equiv_states                 false
% 1.26/1.00  --bmc1_deadlock                         false
% 1.26/1.00  --bmc1_ucm                              false
% 1.26/1.00  --bmc1_add_unsat_core                   none
% 1.26/1.00  --bmc1_unsat_core_children              false
% 1.26/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.26/1.00  --bmc1_out_stat                         full
% 1.26/1.00  --bmc1_ground_init                      false
% 1.26/1.00  --bmc1_pre_inst_next_state              false
% 1.26/1.00  --bmc1_pre_inst_state                   false
% 1.26/1.00  --bmc1_pre_inst_reach_state             false
% 1.26/1.00  --bmc1_out_unsat_core                   false
% 1.26/1.00  --bmc1_aig_witness_out                  false
% 1.26/1.00  --bmc1_verbose                          false
% 1.26/1.00  --bmc1_dump_clauses_tptp                false
% 1.26/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.26/1.00  --bmc1_dump_file                        -
% 1.26/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.26/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.26/1.00  --bmc1_ucm_extend_mode                  1
% 1.26/1.00  --bmc1_ucm_init_mode                    2
% 1.26/1.00  --bmc1_ucm_cone_mode                    none
% 1.26/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.26/1.00  --bmc1_ucm_relax_model                  4
% 1.26/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.26/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.26/1.00  --bmc1_ucm_layered_model                none
% 1.26/1.00  --bmc1_ucm_max_lemma_size               10
% 1.26/1.00  
% 1.26/1.00  ------ AIG Options
% 1.26/1.00  
% 1.26/1.00  --aig_mode                              false
% 1.26/1.00  
% 1.26/1.00  ------ Instantiation Options
% 1.26/1.00  
% 1.26/1.00  --instantiation_flag                    true
% 1.26/1.00  --inst_sos_flag                         false
% 1.26/1.00  --inst_sos_phase                        true
% 1.26/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.26/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.26/1.00  --inst_lit_sel_side                     none
% 1.26/1.00  --inst_solver_per_active                1400
% 1.26/1.00  --inst_solver_calls_frac                1.
% 1.26/1.00  --inst_passive_queue_type               priority_queues
% 1.26/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.26/1.00  --inst_passive_queues_freq              [25;2]
% 1.26/1.00  --inst_dismatching                      true
% 1.26/1.00  --inst_eager_unprocessed_to_passive     true
% 1.26/1.00  --inst_prop_sim_given                   true
% 1.26/1.00  --inst_prop_sim_new                     false
% 1.26/1.00  --inst_subs_new                         false
% 1.26/1.00  --inst_eq_res_simp                      false
% 1.26/1.00  --inst_subs_given                       false
% 1.26/1.00  --inst_orphan_elimination               true
% 1.26/1.00  --inst_learning_loop_flag               true
% 1.26/1.00  --inst_learning_start                   3000
% 1.26/1.00  --inst_learning_factor                  2
% 1.26/1.00  --inst_start_prop_sim_after_learn       3
% 1.26/1.00  --inst_sel_renew                        solver
% 1.26/1.00  --inst_lit_activity_flag                true
% 1.26/1.00  --inst_restr_to_given                   false
% 1.26/1.00  --inst_activity_threshold               500
% 1.26/1.00  --inst_out_proof                        true
% 1.26/1.00  
% 1.26/1.00  ------ Resolution Options
% 1.26/1.00  
% 1.26/1.00  --resolution_flag                       false
% 1.26/1.00  --res_lit_sel                           adaptive
% 1.26/1.00  --res_lit_sel_side                      none
% 1.26/1.00  --res_ordering                          kbo
% 1.26/1.00  --res_to_prop_solver                    active
% 1.26/1.00  --res_prop_simpl_new                    false
% 1.26/1.00  --res_prop_simpl_given                  true
% 1.26/1.00  --res_passive_queue_type                priority_queues
% 1.26/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.26/1.00  --res_passive_queues_freq               [15;5]
% 1.26/1.00  --res_forward_subs                      full
% 1.26/1.00  --res_backward_subs                     full
% 1.26/1.00  --res_forward_subs_resolution           true
% 1.26/1.00  --res_backward_subs_resolution          true
% 1.26/1.00  --res_orphan_elimination                true
% 1.26/1.00  --res_time_limit                        2.
% 1.26/1.00  --res_out_proof                         true
% 1.26/1.00  
% 1.26/1.00  ------ Superposition Options
% 1.26/1.00  
% 1.26/1.00  --superposition_flag                    false
% 1.26/1.00  --sup_passive_queue_type                priority_queues
% 1.26/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.26/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.26/1.00  --demod_completeness_check              fast
% 1.26/1.00  --demod_use_ground                      true
% 1.26/1.00  --sup_to_prop_solver                    passive
% 1.26/1.00  --sup_prop_simpl_new                    true
% 1.26/1.00  --sup_prop_simpl_given                  true
% 1.26/1.00  --sup_fun_splitting                     false
% 1.26/1.00  --sup_smt_interval                      50000
% 1.26/1.00  
% 1.26/1.00  ------ Superposition Simplification Setup
% 1.26/1.00  
% 1.26/1.00  --sup_indices_passive                   []
% 1.26/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.26/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.26/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.26/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.26/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.26/1.00  --sup_full_bw                           [BwDemod]
% 1.26/1.00  --sup_immed_triv                        [TrivRules]
% 1.26/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.26/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.26/1.00  --sup_immed_bw_main                     []
% 1.26/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.26/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.26/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.26/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.26/1.00  
% 1.26/1.00  ------ Combination Options
% 1.26/1.00  
% 1.26/1.00  --comb_res_mult                         3
% 1.26/1.00  --comb_sup_mult                         2
% 1.26/1.00  --comb_inst_mult                        10
% 1.26/1.00  
% 1.26/1.00  ------ Debug Options
% 1.26/1.00  
% 1.26/1.00  --dbg_backtrace                         false
% 1.26/1.00  --dbg_dump_prop_clauses                 false
% 1.26/1.00  --dbg_dump_prop_clauses_file            -
% 1.26/1.00  --dbg_out_stat                          false
% 1.26/1.00  
% 1.26/1.00  
% 1.26/1.00  
% 1.26/1.00  
% 1.26/1.00  ------ Proving...
% 1.26/1.00  
% 1.26/1.00  
% 1.26/1.00  % SZS status CounterSatisfiable for theBenchmark.p
% 1.26/1.00  
% 1.26/1.00  ------ Building Model...Done
% 1.26/1.00  
% 1.26/1.00  %------ The model is defined over ground terms (initial term algebra).
% 1.26/1.00  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 1.26/1.00  %------ where \phi is a formula over the term algebra.
% 1.26/1.00  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 1.26/1.00  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 1.26/1.00  %------ See help for --sat_out_model for different model outputs.
% 1.26/1.00  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 1.26/1.00  %------ where the first argument stands for the sort ($i in the unsorted case)
% 1.26/1.00  % SZS output start Model for theBenchmark.p
% 1.26/1.00  
% 1.26/1.00  %------ Positive definition of r1_xboole_0 
% 1.26/1.00  fof(lit_def,axiom,
% 1.26/1.00      (! [X0,X1] : 
% 1.26/1.00        ( r1_xboole_0(X0,X1) <=>
% 1.26/1.00             (
% 1.26/1.00                (
% 1.26/1.00                  ( X0=sK0 & X1=k3_xboole_0(sK1,sK2) )
% 1.26/1.00                )
% 1.26/1.00  
% 1.26/1.00               | 
% 1.26/1.00                (
% 1.26/1.00                  ( X0=k3_xboole_0(sK1,sK2) & X1=sK0 )
% 1.26/1.00                )
% 1.26/1.00  
% 1.26/1.00             )
% 1.26/1.00        )
% 1.26/1.00      )
% 1.26/1.00     ).
% 1.26/1.00  
% 1.26/1.00  %------ Negative definition of r1_tarski 
% 1.26/1.00  fof(lit_def,axiom,
% 1.26/1.00      (! [X0,X1] : 
% 1.26/1.00        ( ~(r1_tarski(X0,X1)) <=>
% 1.26/1.00             (
% 1.26/1.00              ? [X2] : 
% 1.26/1.00                (
% 1.26/1.00                  ( X0=k3_xboole_0(X2,sK0) & X1=k3_xboole_0(sK1,sK2) )
% 1.26/1.00                )
% 1.26/1.00  
% 1.26/1.00               | 
% 1.26/1.00              ? [X2,X3] : 
% 1.26/1.00                (
% 1.26/1.00                  ( X0=k3_xboole_0(X2,X3) & X1=k3_xboole_0(sK1,sK2) )
% 1.26/1.00                 &
% 1.26/1.00                  ( X3!=sK0 )
% 1.26/1.00                )
% 1.26/1.00  
% 1.26/1.00               | 
% 1.26/1.00                (
% 1.26/1.00                  ( X1=sK1 )
% 1.26/1.00                )
% 1.26/1.00  
% 1.26/1.00               | 
% 1.26/1.00                (
% 1.26/1.00                  ( X1=k3_xboole_0(sK1,sK2) )
% 1.26/1.00                )
% 1.26/1.00  
% 1.26/1.00             )
% 1.26/1.00        )
% 1.26/1.00      )
% 1.26/1.00     ).
% 1.26/1.00  % SZS output end Model for theBenchmark.p
% 1.26/1.00  ------                               Statistics
% 1.26/1.00  
% 1.26/1.00  ------ General
% 1.26/1.00  
% 1.26/1.00  abstr_ref_over_cycles:                  0
% 1.26/1.00  abstr_ref_under_cycles:                 0
% 1.26/1.00  gc_basic_clause_elim:                   0
% 1.26/1.00  forced_gc_time:                         0
% 1.26/1.00  parsing_time:                           0.028
% 1.26/1.00  unif_index_cands_time:                  0.
% 1.26/1.00  unif_index_add_time:                    0.
% 1.26/1.00  orderings_time:                         0.
% 1.26/1.00  out_proof_time:                         0.
% 1.26/1.00  total_time:                             0.194
% 1.26/1.00  num_of_symbols:                         37
% 1.26/1.00  num_of_terms:                           12289
% 1.26/1.00  
% 1.26/1.00  ------ Preprocessing
% 1.26/1.00  
% 1.26/1.00  num_of_splits:                          0
% 1.26/1.00  num_of_split_atoms:                     0
% 1.26/1.00  num_of_reused_defs:                     0
% 1.26/1.00  num_eq_ax_congr_red:                    0
% 1.26/1.00  num_of_sem_filtered_clauses:            0
% 1.26/1.00  num_of_subtypes:                        1
% 1.26/1.00  monotx_restored_types:                  0
% 1.26/1.00  sat_num_of_epr_types:                   0
% 1.26/1.00  sat_num_of_non_cyclic_types:            0
% 1.26/1.00  sat_guarded_non_collapsed_types:        0
% 1.26/1.00  num_pure_diseq_elim:                    0
% 1.26/1.00  simp_replaced_by:                       0
% 1.26/1.00  res_preprocessed:                       7
% 1.26/1.00  prep_upred:                             0
% 1.26/1.00  prep_unflattend:                        0
% 1.26/1.00  smt_new_axioms:                         0
% 1.26/1.00  pred_elim_cands:                        2
% 1.26/1.00  pred_elim:                              0
% 1.26/1.00  pred_elim_cl:                           0
% 1.26/1.00  pred_elim_cycles:                       1
% 1.26/1.00  merged_defs:                            0
% 1.26/1.00  merged_defs_ncl:                        0
% 1.26/1.00  bin_hyper_res:                          0
% 1.26/1.00  prep_cycles:                            1
% 1.26/1.00  pred_elim_time:                         0.
% 1.26/1.00  splitting_time:                         0.
% 1.26/1.00  sem_filter_time:                        0.
% 1.26/1.00  monotx_time:                            0.
% 1.26/1.00  subtype_inf_time:                       0.
% 1.26/1.00  
% 1.26/1.00  ------ Problem properties
% 1.26/1.00  
% 1.26/1.00  clauses:                                7
% 1.26/1.00  conjectures:                            3
% 1.26/1.00  epr:                                    4
% 1.26/1.00  horn:                                   7
% 1.26/1.00  ground:                                 3
% 1.26/1.00  unary:                                  3
% 1.26/1.00  binary:                                 2
% 1.26/1.00  lits:                                   14
% 1.26/1.00  lits_eq:                                0
% 1.26/1.00  fd_pure:                                0
% 1.26/1.00  fd_pseudo:                              0
% 1.26/1.00  fd_cond:                                0
% 1.26/1.00  fd_pseudo_cond:                         0
% 1.26/1.00  ac_symbols:                             0
% 1.26/1.00  
% 1.26/1.00  ------ Propositional Solver
% 1.26/1.00  
% 1.26/1.00  prop_solver_calls:                      19
% 1.26/1.00  prop_fast_solver_calls:                 28
% 1.26/1.00  smt_solver_calls:                       0
% 1.26/1.00  smt_fast_solver_calls:                  0
% 1.26/1.00  prop_num_of_clauses:                    2898
% 1.26/1.00  prop_preprocess_simplified:             5280
% 1.26/1.00  prop_fo_subsumed:                       0
% 1.26/1.00  prop_solver_time:                       0.
% 1.26/1.00  smt_solver_time:                        0.
% 1.26/1.00  smt_fast_solver_time:                   0.
% 1.26/1.00  prop_fast_solver_time:                  0.
% 1.26/1.00  prop_unsat_core_time:                   0.
% 1.26/1.00  
% 1.26/1.00  ------ QBF
% 1.26/1.00  
% 1.26/1.00  qbf_q_res:                              0
% 1.26/1.00  qbf_num_tautologies:                    0
% 1.26/1.00  qbf_prep_cycles:                        0
% 1.26/1.00  
% 1.26/1.00  ------ BMC1
% 1.26/1.00  
% 1.26/1.00  bmc1_current_bound:                     -1
% 1.26/1.00  bmc1_last_solved_bound:                 -1
% 1.26/1.00  bmc1_unsat_core_size:                   -1
% 1.26/1.00  bmc1_unsat_core_parents_size:           -1
% 1.26/1.00  bmc1_merge_next_fun:                    0
% 1.26/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.26/1.00  
% 1.26/1.00  ------ Instantiation
% 1.26/1.00  
% 1.26/1.00  inst_num_of_clauses:                    876
% 1.26/1.00  inst_num_in_passive:                    0
% 1.26/1.00  inst_num_in_active:                     876
% 1.26/1.00  inst_num_in_unprocessed:                0
% 1.26/1.00  inst_num_of_loops:                      913
% 1.26/1.00  inst_num_of_learning_restarts:          0
% 1.26/1.00  inst_num_moves_active_passive:          31
% 1.26/1.00  inst_lit_activity:                      0
% 1.26/1.00  inst_lit_activity_moves:                1
% 1.26/1.00  inst_num_tautologies:                   0
% 1.26/1.00  inst_num_prop_implied:                  0
% 1.26/1.00  inst_num_existing_simplified:           0
% 1.26/1.00  inst_num_eq_res_simplified:             0
% 1.26/1.00  inst_num_child_elim:                    0
% 1.26/1.00  inst_num_of_dismatching_blockings:      217
% 1.26/1.00  inst_num_of_non_proper_insts:           205
% 1.26/1.00  inst_num_of_duplicates:                 0
% 1.26/1.00  inst_inst_num_from_inst_to_res:         0
% 1.26/1.00  inst_dismatching_checking_time:         0.
% 1.26/1.00  
% 1.26/1.00  ------ Resolution
% 1.26/1.00  
% 1.26/1.00  res_num_of_clauses:                     0
% 1.26/1.00  res_num_in_passive:                     0
% 1.26/1.00  res_num_in_active:                      0
% 1.26/1.00  res_num_of_loops:                       8
% 1.26/1.00  res_forward_subset_subsumed:            1
% 1.26/1.00  res_backward_subset_subsumed:           0
% 1.26/1.00  res_forward_subsumed:                   0
% 1.26/1.00  res_backward_subsumed:                  0
% 1.26/1.00  res_forward_subsumption_resolution:     0
% 1.26/1.00  res_backward_subsumption_resolution:    0
% 1.26/1.00  res_clause_to_clause_subsumption:       0
% 1.26/1.00  res_orphan_elimination:                 0
% 1.26/1.00  res_tautology_del:                      0
% 1.26/1.00  res_num_eq_res_simplified:              0
% 1.26/1.00  res_num_sel_changes:                    0
% 1.26/1.00  res_moves_from_active_to_pass:          0
% 1.26/1.00  
% 1.26/1.00  ------ Superposition
% 1.26/1.00  
% 1.26/1.00  sup_time_total:                         0.
% 1.26/1.00  sup_time_generating:                    0.
% 1.26/1.00  sup_time_sim_full:                      0.
% 1.26/1.00  sup_time_sim_immed:                     0.
% 1.26/1.00  
% 1.26/1.00  sup_num_of_clauses:                     0
% 1.26/1.00  sup_num_in_active:                      0
% 1.26/1.00  sup_num_in_passive:                     0
% 1.26/1.00  sup_num_of_loops:                       0
% 1.26/1.00  sup_fw_superposition:                   0
% 1.26/1.00  sup_bw_superposition:                   0
% 1.26/1.00  sup_immediate_simplified:               0
% 1.26/1.00  sup_given_eliminated:                   0
% 1.26/1.00  comparisons_done:                       0
% 1.26/1.00  comparisons_avoided:                    0
% 1.26/1.00  
% 1.26/1.00  ------ Simplifications
% 1.26/1.00  
% 1.26/1.00  
% 1.26/1.00  sim_fw_subset_subsumed:                 0
% 1.26/1.00  sim_bw_subset_subsumed:                 0
% 1.26/1.00  sim_fw_subsumed:                        0
% 1.26/1.00  sim_bw_subsumed:                        0
% 1.26/1.00  sim_fw_subsumption_res:                 0
% 1.26/1.00  sim_bw_subsumption_res:                 0
% 1.26/1.00  sim_tautology_del:                      0
% 1.26/1.00  sim_eq_tautology_del:                   0
% 1.26/1.00  sim_eq_res_simp:                        0
% 1.26/1.00  sim_fw_demodulated:                     0
% 1.26/1.00  sim_bw_demodulated:                     0
% 1.26/1.00  sim_light_normalised:                   0
% 1.26/1.00  sim_joinable_taut:                      0
% 1.26/1.00  sim_joinable_simp:                      0
% 1.26/1.00  sim_ac_normalised:                      0
% 1.26/1.00  sim_smt_subsumption:                    0
% 1.26/1.00  
%------------------------------------------------------------------------------
