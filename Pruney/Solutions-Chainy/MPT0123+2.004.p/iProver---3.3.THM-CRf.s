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
% DateTime   : Thu Dec  3 11:26:12 EST 2020

% Result     : Theorem 0.48s
% Output     : CNFRefutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   16 (  30 expanded)
%              Number of clauses        :    4 (   4 expanded)
%              Number of leaves         :    4 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   17 (  31 expanded)
%              Number of equality atoms :   16 (  30 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f4])).

fof(f6,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).

fof(f10,plain,(
    k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) ),
    inference(definition_unfolding,[],[f10,f8,f8,f8,f8,f8])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f9,f8,f8,f8])).

cnf(c_1,negated_conjecture,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_0,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_11,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(demodulation,[status(thm)],[c_1,c_0])).

cnf(c_12,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n017.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 09:26:31 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 0.48/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.48/0.93  
% 0.48/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.48/0.93  
% 0.48/0.93  ------  iProver source info
% 0.48/0.93  
% 0.48/0.93  git: date: 2020-06-30 10:37:57 +0100
% 0.48/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.48/0.93  git: non_committed_changes: false
% 0.48/0.93  git: last_make_outside_of_git: false
% 0.48/0.93  
% 0.48/0.93  ------ 
% 0.48/0.93  
% 0.48/0.93  ------ Input Options
% 0.48/0.93  
% 0.48/0.93  --out_options                           all
% 0.48/0.93  --tptp_safe_out                         true
% 0.48/0.93  --problem_path                          ""
% 0.48/0.93  --include_path                          ""
% 0.48/0.93  --clausifier                            res/vclausify_rel
% 0.48/0.93  --clausifier_options                    --mode clausify
% 0.48/0.93  --stdin                                 false
% 0.48/0.93  --stats_out                             all
% 0.48/0.93  
% 0.48/0.93  ------ General Options
% 0.48/0.93  
% 0.48/0.93  --fof                                   false
% 0.48/0.93  --time_out_real                         305.
% 0.48/0.93  --time_out_virtual                      -1.
% 0.48/0.93  --symbol_type_check                     false
% 0.48/0.93  --clausify_out                          false
% 0.48/0.93  --sig_cnt_out                           false
% 0.48/0.93  --trig_cnt_out                          false
% 0.48/0.93  --trig_cnt_out_tolerance                1.
% 0.48/0.93  --trig_cnt_out_sk_spl                   false
% 0.48/0.93  --abstr_cl_out                          false
% 0.48/0.93  
% 0.48/0.93  ------ Global Options
% 0.48/0.93  
% 0.48/0.93  --schedule                              default
% 0.48/0.93  --add_important_lit                     false
% 0.48/0.93  --prop_solver_per_cl                    1000
% 0.48/0.93  --min_unsat_core                        false
% 0.48/0.93  --soft_assumptions                      false
% 0.48/0.93  --soft_lemma_size                       3
% 0.48/0.93  --prop_impl_unit_size                   0
% 0.48/0.93  --prop_impl_unit                        []
% 0.48/0.93  --share_sel_clauses                     true
% 0.48/0.93  --reset_solvers                         false
% 0.48/0.93  --bc_imp_inh                            [conj_cone]
% 0.48/0.93  --conj_cone_tolerance                   3.
% 0.48/0.93  --extra_neg_conj                        none
% 0.48/0.93  --large_theory_mode                     true
% 0.48/0.93  --prolific_symb_bound                   200
% 0.48/0.93  --lt_threshold                          2000
% 0.48/0.93  --clause_weak_htbl                      true
% 0.48/0.93  --gc_record_bc_elim                     false
% 0.48/0.93  
% 0.48/0.93  ------ Preprocessing Options
% 0.48/0.93  
% 0.48/0.93  --preprocessing_flag                    true
% 0.48/0.93  --time_out_prep_mult                    0.1
% 0.48/0.93  --splitting_mode                        input
% 0.48/0.93  --splitting_grd                         true
% 0.48/0.93  --splitting_cvd                         false
% 0.48/0.93  --splitting_cvd_svl                     false
% 0.48/0.93  --splitting_nvd                         32
% 0.48/0.93  --sub_typing                            true
% 0.48/0.93  --prep_gs_sim                           true
% 0.48/0.93  --prep_unflatten                        true
% 0.48/0.93  --prep_res_sim                          true
% 0.48/0.93  --prep_upred                            true
% 0.48/0.93  --prep_sem_filter                       exhaustive
% 0.48/0.93  --prep_sem_filter_out                   false
% 0.48/0.93  --pred_elim                             true
% 0.48/0.93  --res_sim_input                         true
% 0.48/0.93  --eq_ax_congr_red                       true
% 0.48/0.93  --pure_diseq_elim                       true
% 0.48/0.93  --brand_transform                       false
% 0.48/0.93  --non_eq_to_eq                          false
% 0.48/0.93  --prep_def_merge                        true
% 0.48/0.93  --prep_def_merge_prop_impl              false
% 0.48/0.93  --prep_def_merge_mbd                    true
% 0.48/0.93  --prep_def_merge_tr_red                 false
% 0.48/0.93  --prep_def_merge_tr_cl                  false
% 0.48/0.93  --smt_preprocessing                     true
% 0.48/0.93  --smt_ac_axioms                         fast
% 0.48/0.93  --preprocessed_out                      false
% 0.48/0.93  --preprocessed_stats                    false
% 0.48/0.93  
% 0.48/0.93  ------ Abstraction refinement Options
% 0.48/0.93  
% 0.48/0.93  --abstr_ref                             []
% 0.48/0.93  --abstr_ref_prep                        false
% 0.48/0.93  --abstr_ref_until_sat                   false
% 0.48/0.93  --abstr_ref_sig_restrict                funpre
% 0.48/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 0.48/0.93  --abstr_ref_under                       []
% 0.48/0.93  
% 0.48/0.93  ------ SAT Options
% 0.48/0.93  
% 0.48/0.93  --sat_mode                              false
% 0.48/0.93  --sat_fm_restart_options                ""
% 0.48/0.93  --sat_gr_def                            false
% 0.48/0.93  --sat_epr_types                         true
% 0.48/0.93  --sat_non_cyclic_types                  false
% 0.48/0.93  --sat_finite_models                     false
% 0.48/0.93  --sat_fm_lemmas                         false
% 0.48/0.93  --sat_fm_prep                           false
% 0.48/0.93  --sat_fm_uc_incr                        true
% 0.48/0.93  --sat_out_model                         small
% 0.48/0.93  --sat_out_clauses                       false
% 0.48/0.93  
% 0.48/0.93  ------ QBF Options
% 0.48/0.93  
% 0.48/0.93  --qbf_mode                              false
% 0.48/0.93  --qbf_elim_univ                         false
% 0.48/0.93  --qbf_dom_inst                          none
% 0.48/0.93  --qbf_dom_pre_inst                      false
% 0.48/0.93  --qbf_sk_in                             false
% 0.48/0.93  --qbf_pred_elim                         true
% 0.48/0.93  --qbf_split                             512
% 0.48/0.93  
% 0.48/0.93  ------ BMC1 Options
% 0.48/0.93  
% 0.48/0.93  --bmc1_incremental                      false
% 0.48/0.93  --bmc1_axioms                           reachable_all
% 0.48/0.93  --bmc1_min_bound                        0
% 0.48/0.93  --bmc1_max_bound                        -1
% 0.48/0.93  --bmc1_max_bound_default                -1
% 0.48/0.93  --bmc1_symbol_reachability              true
% 0.48/0.93  --bmc1_property_lemmas                  false
% 0.48/0.93  --bmc1_k_induction                      false
% 0.48/0.93  --bmc1_non_equiv_states                 false
% 0.48/0.93  --bmc1_deadlock                         false
% 0.48/0.93  --bmc1_ucm                              false
% 0.48/0.93  --bmc1_add_unsat_core                   none
% 0.48/0.93  --bmc1_unsat_core_children              false
% 0.48/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 0.48/0.93  --bmc1_out_stat                         full
% 0.48/0.93  --bmc1_ground_init                      false
% 0.48/0.93  --bmc1_pre_inst_next_state              false
% 0.48/0.93  --bmc1_pre_inst_state                   false
% 0.48/0.93  --bmc1_pre_inst_reach_state             false
% 0.48/0.93  --bmc1_out_unsat_core                   false
% 0.48/0.93  --bmc1_aig_witness_out                  false
% 0.48/0.93  --bmc1_verbose                          false
% 0.48/0.93  --bmc1_dump_clauses_tptp                false
% 0.48/0.93  --bmc1_dump_unsat_core_tptp             false
% 0.48/0.93  --bmc1_dump_file                        -
% 0.48/0.93  --bmc1_ucm_expand_uc_limit              128
% 0.48/0.93  --bmc1_ucm_n_expand_iterations          6
% 0.48/0.93  --bmc1_ucm_extend_mode                  1
% 0.48/0.93  --bmc1_ucm_init_mode                    2
% 0.48/0.93  --bmc1_ucm_cone_mode                    none
% 0.48/0.93  --bmc1_ucm_reduced_relation_type        0
% 0.48/0.93  --bmc1_ucm_relax_model                  4
% 0.48/0.93  --bmc1_ucm_full_tr_after_sat            true
% 0.48/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 0.48/0.93  --bmc1_ucm_layered_model                none
% 0.48/0.93  --bmc1_ucm_max_lemma_size               10
% 0.48/0.93  
% 0.48/0.93  ------ AIG Options
% 0.48/0.93  
% 0.48/0.93  --aig_mode                              false
% 0.48/0.93  
% 0.48/0.93  ------ Instantiation Options
% 0.48/0.93  
% 0.48/0.93  --instantiation_flag                    true
% 0.48/0.93  --inst_sos_flag                         false
% 0.48/0.93  --inst_sos_phase                        true
% 0.48/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.48/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.48/0.93  --inst_lit_sel_side                     num_symb
% 0.48/0.93  --inst_solver_per_active                1400
% 0.48/0.93  --inst_solver_calls_frac                1.
% 0.48/0.93  --inst_passive_queue_type               priority_queues
% 0.48/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.48/0.93  --inst_passive_queues_freq              [25;2]
% 0.48/0.93  --inst_dismatching                      true
% 0.48/0.93  --inst_eager_unprocessed_to_passive     true
% 0.48/0.93  --inst_prop_sim_given                   true
% 0.48/0.93  --inst_prop_sim_new                     false
% 0.48/0.93  --inst_subs_new                         false
% 0.48/0.93  --inst_eq_res_simp                      false
% 0.48/0.93  --inst_subs_given                       false
% 0.48/0.93  --inst_orphan_elimination               true
% 0.48/0.93  --inst_learning_loop_flag               true
% 0.48/0.93  --inst_learning_start                   3000
% 0.48/0.93  --inst_learning_factor                  2
% 0.48/0.93  --inst_start_prop_sim_after_learn       3
% 0.48/0.93  --inst_sel_renew                        solver
% 0.48/0.93  --inst_lit_activity_flag                true
% 0.48/0.93  --inst_restr_to_given                   false
% 0.48/0.93  --inst_activity_threshold               500
% 0.48/0.93  --inst_out_proof                        true
% 0.48/0.93  
% 0.48/0.93  ------ Resolution Options
% 0.48/0.93  
% 0.48/0.93  --resolution_flag                       true
% 0.48/0.93  --res_lit_sel                           adaptive
% 0.48/0.93  --res_lit_sel_side                      none
% 0.48/0.93  --res_ordering                          kbo
% 0.48/0.93  --res_to_prop_solver                    active
% 0.48/0.93  --res_prop_simpl_new                    false
% 0.48/0.93  --res_prop_simpl_given                  true
% 0.48/0.93  --res_passive_queue_type                priority_queues
% 0.48/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.48/0.93  --res_passive_queues_freq               [15;5]
% 0.48/0.93  --res_forward_subs                      full
% 0.48/0.93  --res_backward_subs                     full
% 0.48/0.93  --res_forward_subs_resolution           true
% 0.48/0.93  --res_backward_subs_resolution          true
% 0.48/0.93  --res_orphan_elimination                true
% 0.48/0.93  --res_time_limit                        2.
% 0.48/0.93  --res_out_proof                         true
% 0.48/0.93  
% 0.48/0.93  ------ Superposition Options
% 0.48/0.93  
% 0.48/0.93  --superposition_flag                    true
% 0.48/0.93  --sup_passive_queue_type                priority_queues
% 0.48/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.48/0.93  --sup_passive_queues_freq               [8;1;4]
% 0.48/0.93  --demod_completeness_check              fast
% 0.48/0.93  --demod_use_ground                      true
% 0.48/0.93  --sup_to_prop_solver                    passive
% 0.48/0.93  --sup_prop_simpl_new                    true
% 0.48/0.93  --sup_prop_simpl_given                  true
% 0.48/0.93  --sup_fun_splitting                     false
% 0.48/0.93  --sup_smt_interval                      50000
% 0.48/0.93  
% 0.48/0.93  ------ Superposition Simplification Setup
% 0.48/0.93  
% 0.48/0.93  --sup_indices_passive                   []
% 0.48/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.48/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.48/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.48/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 0.48/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.48/0.93  --sup_full_bw                           [BwDemod]
% 0.48/0.93  --sup_immed_triv                        [TrivRules]
% 0.48/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.48/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.48/0.93  --sup_immed_bw_main                     []
% 0.48/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.48/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 0.48/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.48/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.48/0.93  
% 0.48/0.93  ------ Combination Options
% 0.48/0.93  
% 0.48/0.93  --comb_res_mult                         3
% 0.48/0.93  --comb_sup_mult                         2
% 0.48/0.93  --comb_inst_mult                        10
% 0.48/0.93  
% 0.48/0.93  ------ Debug Options
% 0.48/0.93  
% 0.48/0.93  --dbg_backtrace                         false
% 0.48/0.93  --dbg_dump_prop_clauses                 false
% 0.48/0.93  --dbg_dump_prop_clauses_file            -
% 0.48/0.93  --dbg_out_stat                          false
% 0.48/0.93  ------ Parsing...
% 0.48/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.48/0.93  
% 0.48/0.93  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 0.48/0.93  
% 0.48/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.48/0.93  
% 0.48/0.93  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.48/0.93  ------ Proving...
% 0.48/0.93  ------ Problem Properties 
% 0.48/0.93  
% 0.48/0.93  
% 0.48/0.93  clauses                                 2
% 0.48/0.93  conjectures                             1
% 0.48/0.93  EPR                                     0
% 0.48/0.93  Horn                                    2
% 0.48/0.93  unary                                   2
% 0.48/0.93  binary                                  0
% 0.48/0.93  lits                                    2
% 0.48/0.93  lits eq                                 2
% 0.48/0.93  fd_pure                                 0
% 0.48/0.93  fd_pseudo                               0
% 0.48/0.93  fd_cond                                 0
% 0.48/0.93  fd_pseudo_cond                          0
% 0.48/0.93  AC symbols                              0
% 0.48/0.93  
% 0.48/0.93  ------ Schedule UEQ
% 0.48/0.93  
% 0.48/0.93  ------ pure equality problem: resolution off 
% 0.48/0.93  
% 0.48/0.93  ------ Option_UEQ Time Limit: Unbounded
% 0.48/0.93  
% 0.48/0.93  
% 0.48/0.93  ------ 
% 0.48/0.93  Current options:
% 0.48/0.93  ------ 
% 0.48/0.93  
% 0.48/0.93  ------ Input Options
% 0.48/0.93  
% 0.48/0.93  --out_options                           all
% 0.48/0.93  --tptp_safe_out                         true
% 0.48/0.93  --problem_path                          ""
% 0.48/0.93  --include_path                          ""
% 0.48/0.93  --clausifier                            res/vclausify_rel
% 0.48/0.93  --clausifier_options                    --mode clausify
% 0.48/0.93  --stdin                                 false
% 0.48/0.93  --stats_out                             all
% 0.48/0.93  
% 0.48/0.93  ------ General Options
% 0.48/0.93  
% 0.48/0.93  --fof                                   false
% 0.48/0.93  --time_out_real                         305.
% 0.48/0.93  --time_out_virtual                      -1.
% 0.48/0.93  --symbol_type_check                     false
% 0.48/0.93  --clausify_out                          false
% 0.48/0.93  --sig_cnt_out                           false
% 0.48/0.93  --trig_cnt_out                          false
% 0.48/0.93  --trig_cnt_out_tolerance                1.
% 0.48/0.93  --trig_cnt_out_sk_spl                   false
% 0.48/0.93  --abstr_cl_out                          false
% 0.48/0.93  
% 0.48/0.93  ------ Global Options
% 0.48/0.93  
% 0.48/0.93  --schedule                              default
% 0.48/0.93  --add_important_lit                     false
% 0.48/0.93  --prop_solver_per_cl                    1000
% 0.48/0.93  --min_unsat_core                        false
% 0.48/0.93  --soft_assumptions                      false
% 0.48/0.93  --soft_lemma_size                       3
% 0.48/0.93  --prop_impl_unit_size                   0
% 0.48/0.93  --prop_impl_unit                        []
% 0.48/0.93  --share_sel_clauses                     true
% 0.48/0.93  --reset_solvers                         false
% 0.48/0.93  --bc_imp_inh                            [conj_cone]
% 0.48/0.93  --conj_cone_tolerance                   3.
% 0.48/0.93  --extra_neg_conj                        none
% 0.48/0.93  --large_theory_mode                     true
% 0.48/0.93  --prolific_symb_bound                   200
% 0.48/0.93  --lt_threshold                          2000
% 0.48/0.93  --clause_weak_htbl                      true
% 0.48/0.93  --gc_record_bc_elim                     false
% 0.48/0.93  
% 0.48/0.93  ------ Preprocessing Options
% 0.48/0.93  
% 0.48/0.93  --preprocessing_flag                    true
% 0.48/0.93  --time_out_prep_mult                    0.1
% 0.48/0.93  --splitting_mode                        input
% 0.48/0.93  --splitting_grd                         true
% 0.48/0.93  --splitting_cvd                         false
% 0.48/0.93  --splitting_cvd_svl                     false
% 0.48/0.93  --splitting_nvd                         32
% 0.48/0.93  --sub_typing                            true
% 0.48/0.93  --prep_gs_sim                           true
% 0.48/0.93  --prep_unflatten                        true
% 0.48/0.93  --prep_res_sim                          true
% 0.48/0.93  --prep_upred                            true
% 0.48/0.93  --prep_sem_filter                       exhaustive
% 0.48/0.93  --prep_sem_filter_out                   false
% 0.48/0.93  --pred_elim                             true
% 0.48/0.93  --res_sim_input                         true
% 0.48/0.93  --eq_ax_congr_red                       true
% 0.48/0.93  --pure_diseq_elim                       true
% 0.48/0.93  --brand_transform                       false
% 0.48/0.93  --non_eq_to_eq                          false
% 0.48/0.93  --prep_def_merge                        true
% 0.48/0.93  --prep_def_merge_prop_impl              false
% 0.48/0.93  --prep_def_merge_mbd                    true
% 0.48/0.93  --prep_def_merge_tr_red                 false
% 0.48/0.93  --prep_def_merge_tr_cl                  false
% 0.48/0.93  --smt_preprocessing                     true
% 0.48/0.93  --smt_ac_axioms                         fast
% 0.48/0.93  --preprocessed_out                      false
% 0.48/0.93  --preprocessed_stats                    false
% 0.48/0.93  
% 0.48/0.93  ------ Abstraction refinement Options
% 0.48/0.93  
% 0.48/0.93  --abstr_ref                             []
% 0.48/0.93  --abstr_ref_prep                        false
% 0.48/0.93  --abstr_ref_until_sat                   false
% 0.48/0.93  --abstr_ref_sig_restrict                funpre
% 0.48/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 0.48/0.93  --abstr_ref_under                       []
% 0.48/0.93  
% 0.48/0.93  ------ SAT Options
% 0.48/0.93  
% 0.48/0.93  --sat_mode                              false
% 0.48/0.93  --sat_fm_restart_options                ""
% 0.48/0.93  --sat_gr_def                            false
% 0.48/0.93  --sat_epr_types                         true
% 0.48/0.93  --sat_non_cyclic_types                  false
% 0.48/0.93  --sat_finite_models                     false
% 0.48/0.93  --sat_fm_lemmas                         false
% 0.48/0.93  --sat_fm_prep                           false
% 0.48/0.93  --sat_fm_uc_incr                        true
% 0.48/0.93  --sat_out_model                         small
% 0.48/0.93  --sat_out_clauses                       false
% 0.48/0.93  
% 0.48/0.93  ------ QBF Options
% 0.48/0.93  
% 0.48/0.93  --qbf_mode                              false
% 0.48/0.93  --qbf_elim_univ                         false
% 0.48/0.93  --qbf_dom_inst                          none
% 0.48/0.93  --qbf_dom_pre_inst                      false
% 0.48/0.93  --qbf_sk_in                             false
% 0.48/0.93  --qbf_pred_elim                         true
% 0.48/0.93  --qbf_split                             512
% 0.48/0.93  
% 0.48/0.93  ------ BMC1 Options
% 0.48/0.93  
% 0.48/0.93  --bmc1_incremental                      false
% 0.48/0.93  --bmc1_axioms                           reachable_all
% 0.48/0.93  --bmc1_min_bound                        0
% 0.48/0.93  --bmc1_max_bound                        -1
% 0.48/0.93  --bmc1_max_bound_default                -1
% 0.48/0.93  --bmc1_symbol_reachability              true
% 0.48/0.93  --bmc1_property_lemmas                  false
% 0.48/0.93  --bmc1_k_induction                      false
% 0.48/0.93  --bmc1_non_equiv_states                 false
% 0.48/0.93  --bmc1_deadlock                         false
% 0.48/0.93  --bmc1_ucm                              false
% 0.48/0.93  --bmc1_add_unsat_core                   none
% 0.48/0.93  --bmc1_unsat_core_children              false
% 0.48/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 0.48/0.93  --bmc1_out_stat                         full
% 0.48/0.93  --bmc1_ground_init                      false
% 0.48/0.93  --bmc1_pre_inst_next_state              false
% 0.48/0.93  --bmc1_pre_inst_state                   false
% 0.48/0.93  --bmc1_pre_inst_reach_state             false
% 0.48/0.93  --bmc1_out_unsat_core                   false
% 0.48/0.93  --bmc1_aig_witness_out                  false
% 0.48/0.93  --bmc1_verbose                          false
% 0.48/0.93  --bmc1_dump_clauses_tptp                false
% 0.48/0.93  --bmc1_dump_unsat_core_tptp             false
% 0.48/0.93  --bmc1_dump_file                        -
% 0.48/0.93  --bmc1_ucm_expand_uc_limit              128
% 0.48/0.93  --bmc1_ucm_n_expand_iterations          6
% 0.48/0.93  --bmc1_ucm_extend_mode                  1
% 0.48/0.93  --bmc1_ucm_init_mode                    2
% 0.48/0.93  --bmc1_ucm_cone_mode                    none
% 0.48/0.93  --bmc1_ucm_reduced_relation_type        0
% 0.48/0.93  --bmc1_ucm_relax_model                  4
% 0.48/0.93  --bmc1_ucm_full_tr_after_sat            true
% 0.48/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 0.48/0.93  --bmc1_ucm_layered_model                none
% 0.48/0.93  --bmc1_ucm_max_lemma_size               10
% 0.48/0.93  
% 0.48/0.93  ------ AIG Options
% 0.48/0.93  
% 0.48/0.93  --aig_mode                              false
% 0.48/0.93  
% 0.48/0.93  ------ Instantiation Options
% 0.48/0.93  
% 0.48/0.93  --instantiation_flag                    false
% 0.48/0.93  --inst_sos_flag                         false
% 0.48/0.93  --inst_sos_phase                        true
% 0.48/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.48/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.48/0.93  --inst_lit_sel_side                     num_symb
% 0.48/0.93  --inst_solver_per_active                1400
% 0.48/0.93  --inst_solver_calls_frac                1.
% 0.48/0.93  --inst_passive_queue_type               priority_queues
% 0.48/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.48/0.93  --inst_passive_queues_freq              [25;2]
% 0.48/0.93  --inst_dismatching                      true
% 0.48/0.93  --inst_eager_unprocessed_to_passive     true
% 0.48/0.93  --inst_prop_sim_given                   true
% 0.48/0.93  --inst_prop_sim_new                     false
% 0.48/0.93  --inst_subs_new                         false
% 0.48/0.93  --inst_eq_res_simp                      false
% 0.48/0.93  --inst_subs_given                       false
% 0.48/0.93  --inst_orphan_elimination               true
% 0.48/0.93  --inst_learning_loop_flag               true
% 0.48/0.93  --inst_learning_start                   3000
% 0.48/0.93  --inst_learning_factor                  2
% 0.48/0.93  --inst_start_prop_sim_after_learn       3
% 0.48/0.93  --inst_sel_renew                        solver
% 0.48/0.93  --inst_lit_activity_flag                true
% 0.48/0.93  --inst_restr_to_given                   false
% 0.48/0.93  --inst_activity_threshold               500
% 0.48/0.93  --inst_out_proof                        true
% 0.48/0.93  
% 0.48/0.93  ------ Resolution Options
% 0.48/0.93  
% 0.48/0.93  --resolution_flag                       false
% 0.48/0.93  --res_lit_sel                           adaptive
% 0.48/0.93  --res_lit_sel_side                      none
% 0.48/0.93  --res_ordering                          kbo
% 0.48/0.93  --res_to_prop_solver                    active
% 0.48/0.93  --res_prop_simpl_new                    false
% 0.48/0.93  --res_prop_simpl_given                  true
% 0.48/0.93  --res_passive_queue_type                priority_queues
% 0.48/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.48/0.93  --res_passive_queues_freq               [15;5]
% 0.48/0.93  --res_forward_subs                      full
% 0.48/0.93  --res_backward_subs                     full
% 0.48/0.93  --res_forward_subs_resolution           true
% 0.48/0.93  --res_backward_subs_resolution          true
% 0.48/0.93  --res_orphan_elimination                true
% 0.48/0.93  --res_time_limit                        2.
% 0.48/0.93  --res_out_proof                         true
% 0.48/0.93  
% 0.48/0.93  ------ Superposition Options
% 0.48/0.93  
% 0.48/0.93  --superposition_flag                    true
% 0.48/0.93  --sup_passive_queue_type                priority_queues
% 0.48/0.93  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.48/0.93  --sup_passive_queues_freq               [8;1;4]
% 0.48/0.93  --demod_completeness_check              fast
% 0.48/0.93  --demod_use_ground                      true
% 0.48/0.93  --sup_to_prop_solver                    active
% 0.48/0.93  --sup_prop_simpl_new                    false
% 0.48/0.93  --sup_prop_simpl_given                  false
% 0.48/0.93  --sup_fun_splitting                     true
% 0.48/0.93  --sup_smt_interval                      10000
% 0.48/0.93  
% 0.48/0.93  ------ Superposition Simplification Setup
% 0.48/0.93  
% 0.48/0.93  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 0.48/0.93  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 0.48/0.93  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 0.48/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.48/0.93  --sup_full_triv                         [TrivRules]
% 0.48/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 0.48/0.93  --sup_full_bw                           [BwDemod;BwSubsumption]
% 0.48/0.93  --sup_immed_triv                        [TrivRules]
% 0.48/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.48/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 0.48/0.93  --sup_immed_bw_main                     []
% 0.48/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 0.48/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 0.48/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 0.48/0.93  --sup_input_bw                          [BwDemod;BwSubsumption]
% 0.48/0.93  
% 0.48/0.93  ------ Combination Options
% 0.48/0.93  
% 0.48/0.93  --comb_res_mult                         1
% 0.48/0.93  --comb_sup_mult                         1
% 0.48/0.93  --comb_inst_mult                        1000000
% 0.48/0.93  
% 0.48/0.93  ------ Debug Options
% 0.48/0.93  
% 0.48/0.93  --dbg_backtrace                         false
% 0.48/0.93  --dbg_dump_prop_clauses                 false
% 0.48/0.93  --dbg_dump_prop_clauses_file            -
% 0.48/0.93  --dbg_out_stat                          false
% 0.48/0.93  
% 0.48/0.93  
% 0.48/0.93  
% 0.48/0.93  
% 0.48/0.93  ------ Proving...
% 0.48/0.93  
% 0.48/0.93  
% 0.48/0.93  % SZS status Theorem for theBenchmark.p
% 0.48/0.93  
% 0.48/0.93   Resolution empty clause
% 0.48/0.93  
% 0.48/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 0.48/0.93  
% 0.48/0.93  fof(f3,conjecture,(
% 0.48/0.93    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.48/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.48/0.93  
% 0.48/0.93  fof(f4,negated_conjecture,(
% 0.48/0.93    ~! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.48/0.93    inference(negated_conjecture,[],[f3])).
% 0.48/0.93  
% 0.48/0.93  fof(f5,plain,(
% 0.48/0.93    ? [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.48/0.93    inference(ennf_transformation,[],[f4])).
% 0.48/0.93  
% 0.48/0.93  fof(f6,plain,(
% 0.48/0.93    ? [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) != k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) => k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 0.48/0.93    introduced(choice_axiom,[])).
% 0.48/0.93  
% 0.48/0.93  fof(f7,plain,(
% 0.48/0.93    k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 0.48/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).
% 0.48/0.93  
% 0.48/0.93  fof(f10,plain,(
% 0.48/0.93    k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 0.48/0.93    inference(cnf_transformation,[],[f7])).
% 0.48/0.93  
% 0.48/0.93  fof(f1,axiom,(
% 0.48/0.93    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.48/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.48/0.93  
% 0.48/0.93  fof(f8,plain,(
% 0.48/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.48/0.93    inference(cnf_transformation,[],[f1])).
% 0.48/0.93  
% 0.48/0.93  fof(f12,plain,(
% 0.48/0.93    k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))))),
% 0.48/0.93    inference(definition_unfolding,[],[f10,f8,f8,f8,f8,f8])).
% 0.48/0.93  
% 0.48/0.93  fof(f2,axiom,(
% 0.48/0.93    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k4_xboole_0(X1,X2))),
% 0.48/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.48/0.93  
% 0.48/0.93  fof(f9,plain,(
% 0.48/0.93    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 0.48/0.93    inference(cnf_transformation,[],[f2])).
% 0.48/0.93  
% 0.48/0.93  fof(f11,plain,(
% 0.48/0.93    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 0.48/0.93    inference(definition_unfolding,[],[f9,f8,f8,f8])).
% 0.48/0.93  
% 0.48/0.93  cnf(c_1,negated_conjecture,
% 0.48/0.93      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))) ),
% 0.48/0.93      inference(cnf_transformation,[],[f12]) ).
% 0.48/0.93  
% 0.48/0.93  cnf(c_0,plain,
% 0.48/0.93      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 0.48/0.93      inference(cnf_transformation,[],[f11]) ).
% 0.48/0.93  
% 0.48/0.93  cnf(c_11,plain,
% 0.48/0.93      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
% 0.48/0.93      inference(demodulation,[status(thm)],[c_1,c_0]) ).
% 0.48/0.93  
% 0.48/0.93  cnf(c_12,plain,
% 0.48/0.93      ( $false ),
% 0.48/0.93      inference(equality_resolution_simp,[status(thm)],[c_11]) ).
% 0.48/0.93  
% 0.48/0.93  
% 0.48/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 0.48/0.93  
% 0.48/0.93  ------                               Statistics
% 0.48/0.93  
% 0.48/0.93  ------ General
% 0.48/0.93  
% 0.48/0.93  abstr_ref_over_cycles:                  0
% 0.48/0.93  abstr_ref_under_cycles:                 0
% 0.48/0.93  gc_basic_clause_elim:                   0
% 0.48/0.93  forced_gc_time:                         0
% 0.48/0.93  parsing_time:                           0.008
% 0.48/0.93  unif_index_cands_time:                  0.
% 0.48/0.93  unif_index_add_time:                    0.
% 0.48/0.93  orderings_time:                         0.
% 0.48/0.93  out_proof_time:                         0.006
% 0.48/0.93  total_time:                             0.033
% 0.48/0.93  num_of_symbols:                         35
% 0.48/0.93  num_of_terms:                           86
% 0.48/0.93  
% 0.48/0.93  ------ Preprocessing
% 0.48/0.93  
% 0.48/0.93  num_of_splits:                          0
% 0.48/0.93  num_of_split_atoms:                     0
% 0.48/0.93  num_of_reused_defs:                     0
% 0.48/0.93  num_eq_ax_congr_red:                    0
% 0.48/0.93  num_of_sem_filtered_clauses:            0
% 0.48/0.93  num_of_subtypes:                        1
% 0.48/0.93  monotx_restored_types:                  0
% 0.48/0.93  sat_num_of_epr_types:                   0
% 0.48/0.93  sat_num_of_non_cyclic_types:            0
% 0.48/0.93  sat_guarded_non_collapsed_types:        0
% 0.48/0.93  num_pure_diseq_elim:                    0
% 0.48/0.93  simp_replaced_by:                       0
% 0.48/0.93  res_preprocessed:                       7
% 0.48/0.93  prep_upred:                             0
% 0.48/0.93  prep_unflattend:                        0
% 0.48/0.93  smt_new_axioms:                         0
% 0.48/0.93  pred_elim_cands:                        0
% 0.48/0.93  pred_elim:                              0
% 0.48/0.93  pred_elim_cl:                           0
% 0.48/0.93  pred_elim_cycles:                       0
% 0.48/0.93  merged_defs:                            0
% 0.48/0.93  merged_defs_ncl:                        0
% 0.48/0.93  bin_hyper_res:                          0
% 0.48/0.93  prep_cycles:                            2
% 0.48/0.93  pred_elim_time:                         0.
% 0.48/0.93  splitting_time:                         0.
% 0.48/0.93  sem_filter_time:                        0.
% 0.48/0.93  monotx_time:                            0.
% 0.48/0.93  subtype_inf_time:                       0.
% 0.48/0.93  
% 0.48/0.93  ------ Problem properties
% 0.48/0.93  
% 0.48/0.93  clauses:                                2
% 0.48/0.93  conjectures:                            1
% 0.48/0.93  epr:                                    0
% 0.48/0.93  horn:                                   2
% 0.48/0.93  ground:                                 1
% 0.48/0.93  unary:                                  2
% 0.48/0.94  binary:                                 0
% 0.48/0.94  lits:                                   2
% 0.48/0.94  lits_eq:                                2
% 0.48/0.94  fd_pure:                                0
% 0.48/0.94  fd_pseudo:                              0
% 0.48/0.94  fd_cond:                                0
% 0.48/0.94  fd_pseudo_cond:                         0
% 0.48/0.94  ac_symbols:                             0
% 0.48/0.94  
% 0.48/0.94  ------ Propositional Solver
% 0.48/0.94  
% 0.48/0.94  prop_solver_calls:                      13
% 0.48/0.94  prop_fast_solver_calls:                 22
% 0.48/0.94  smt_solver_calls:                       0
% 0.48/0.94  smt_fast_solver_calls:                  0
% 0.48/0.94  prop_num_of_clauses:                    8
% 0.48/0.94  prop_preprocess_simplified:             79
% 0.48/0.94  prop_fo_subsumed:                       0
% 0.48/0.94  prop_solver_time:                       0.
% 0.48/0.94  smt_solver_time:                        0.
% 0.48/0.94  smt_fast_solver_time:                   0.
% 0.48/0.94  prop_fast_solver_time:                  0.
% 0.48/0.94  prop_unsat_core_time:                   0.
% 0.48/0.94  
% 0.48/0.94  ------ QBF
% 0.48/0.94  
% 0.48/0.94  qbf_q_res:                              0
% 0.48/0.94  qbf_num_tautologies:                    0
% 0.48/0.94  qbf_prep_cycles:                        0
% 0.48/0.94  
% 0.48/0.94  ------ BMC1
% 0.48/0.94  
% 0.48/0.94  bmc1_current_bound:                     -1
% 0.48/0.94  bmc1_last_solved_bound:                 -1
% 0.48/0.94  bmc1_unsat_core_size:                   -1
% 0.48/0.94  bmc1_unsat_core_parents_size:           -1
% 0.48/0.94  bmc1_merge_next_fun:                    0
% 0.48/0.94  bmc1_unsat_core_clauses_time:           0.
% 0.48/0.94  
% 0.48/0.94  ------ Instantiation
% 0.48/0.94  
% 0.48/0.94  inst_num_of_clauses:                    0
% 0.48/0.94  inst_num_in_passive:                    0
% 0.48/0.94  inst_num_in_active:                     0
% 0.48/0.94  inst_num_in_unprocessed:                0
% 0.48/0.94  inst_num_of_loops:                      0
% 0.48/0.94  inst_num_of_learning_restarts:          0
% 0.48/0.94  inst_num_moves_active_passive:          0
% 0.48/0.94  inst_lit_activity:                      0
% 0.48/0.94  inst_lit_activity_moves:                0
% 0.48/0.94  inst_num_tautologies:                   0
% 0.48/0.94  inst_num_prop_implied:                  0
% 0.48/0.94  inst_num_existing_simplified:           0
% 0.48/0.94  inst_num_eq_res_simplified:             0
% 0.48/0.94  inst_num_child_elim:                    0
% 0.48/0.94  inst_num_of_dismatching_blockings:      0
% 0.48/0.94  inst_num_of_non_proper_insts:           0
% 0.48/0.94  inst_num_of_duplicates:                 0
% 0.48/0.94  inst_inst_num_from_inst_to_res:         0
% 0.48/0.94  inst_dismatching_checking_time:         0.
% 0.48/0.94  
% 0.48/0.94  ------ Resolution
% 0.48/0.94  
% 0.48/0.94  res_num_of_clauses:                     0
% 0.48/0.94  res_num_in_passive:                     0
% 0.48/0.94  res_num_in_active:                      0
% 0.48/0.94  res_num_of_loops:                       9
% 0.48/0.94  res_forward_subset_subsumed:            0
% 0.48/0.94  res_backward_subset_subsumed:           0
% 0.48/0.94  res_forward_subsumed:                   0
% 0.48/0.94  res_backward_subsumed:                  0
% 0.48/0.94  res_forward_subsumption_resolution:     0
% 0.48/0.94  res_backward_subsumption_resolution:    0
% 0.48/0.94  res_clause_to_clause_subsumption:       1
% 0.48/0.94  res_orphan_elimination:                 0
% 0.48/0.94  res_tautology_del:                      0
% 0.48/0.94  res_num_eq_res_simplified:              0
% 0.48/0.94  res_num_sel_changes:                    0
% 0.48/0.94  res_moves_from_active_to_pass:          0
% 0.48/0.94  
% 0.48/0.94  ------ Superposition
% 0.48/0.94  
% 0.48/0.94  sup_time_total:                         0.
% 0.48/0.94  sup_time_generating:                    0.
% 0.48/0.94  sup_time_sim_full:                      0.
% 0.48/0.94  sup_time_sim_immed:                     0.
% 0.48/0.94  
% 0.48/0.94  sup_num_of_clauses:                     0
% 0.48/0.94  sup_num_in_active:                      0
% 0.48/0.94  sup_num_in_passive:                     0
% 0.48/0.94  sup_num_of_loops:                       0
% 0.48/0.94  sup_fw_superposition:                   0
% 0.48/0.94  sup_bw_superposition:                   0
% 0.48/0.94  sup_immediate_simplified:               0
% 0.48/0.94  sup_given_eliminated:                   0
% 0.48/0.94  comparisons_done:                       0
% 0.48/0.94  comparisons_avoided:                    0
% 0.48/0.94  
% 0.48/0.94  ------ Simplifications
% 0.48/0.94  
% 0.48/0.94  
% 0.48/0.94  sim_fw_subset_subsumed:                 0
% 0.48/0.94  sim_bw_subset_subsumed:                 0
% 0.48/0.94  sim_fw_subsumed:                        0
% 0.48/0.94  sim_bw_subsumed:                        0
% 0.48/0.94  sim_fw_subsumption_res:                 0
% 0.48/0.94  sim_bw_subsumption_res:                 0
% 0.48/0.94  sim_tautology_del:                      0
% 0.48/0.94  sim_eq_tautology_del:                   0
% 0.48/0.94  sim_eq_res_simp:                        0
% 0.48/0.94  sim_fw_demodulated:                     1
% 0.48/0.94  sim_bw_demodulated:                     0
% 0.48/0.94  sim_light_normalised:                   0
% 0.48/0.94  sim_joinable_taut:                      0
% 0.48/0.94  sim_joinable_simp:                      0
% 0.48/0.94  sim_ac_normalised:                      0
% 0.48/0.94  sim_smt_subsumption:                    0
% 0.48/0.94  
%------------------------------------------------------------------------------
