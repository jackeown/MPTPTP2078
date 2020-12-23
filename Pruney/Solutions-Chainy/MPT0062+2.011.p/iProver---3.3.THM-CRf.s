%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:02 EST 2020

% Result     : Theorem 14.93s
% Output     : CNFRefutation 14.93s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    8 (  10 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  38 expanded)
%              Number of equality atoms :   33 (  37 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f15,f16])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f17,f16])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,conjecture,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f7])).

fof(f9,plain,(
    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f8])).

fof(f10,plain,
    ( ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))
   => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).

fof(f18,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f21,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(definition_unfolding,[],[f18,f16])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_2,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_81,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k2_xboole_0(X0,X2),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_4,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_1,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_23,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_70,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_4,c_23])).

cnf(c_87,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X0)) ),
    inference(light_normalisation,[status(thm)],[c_81,c_70])).

cnf(c_5,negated_conjecture,
    ( k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_39147,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_87,c_5])).

cnf(c_41544,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_39147])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:15:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 14.93/2.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.93/2.47  
% 14.93/2.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 14.93/2.47  
% 14.93/2.47  ------  iProver source info
% 14.93/2.47  
% 14.93/2.47  git: date: 2020-06-30 10:37:57 +0100
% 14.93/2.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 14.93/2.47  git: non_committed_changes: false
% 14.93/2.47  git: last_make_outside_of_git: false
% 14.93/2.47  
% 14.93/2.47  ------ 
% 14.93/2.47  
% 14.93/2.47  ------ Input Options
% 14.93/2.47  
% 14.93/2.47  --out_options                           all
% 14.93/2.47  --tptp_safe_out                         true
% 14.93/2.47  --problem_path                          ""
% 14.93/2.47  --include_path                          ""
% 14.93/2.47  --clausifier                            res/vclausify_rel
% 14.93/2.47  --clausifier_options                    --mode clausify
% 14.93/2.47  --stdin                                 false
% 14.93/2.47  --stats_out                             all
% 14.93/2.47  
% 14.93/2.47  ------ General Options
% 14.93/2.47  
% 14.93/2.47  --fof                                   false
% 14.93/2.47  --time_out_real                         305.
% 14.93/2.47  --time_out_virtual                      -1.
% 14.93/2.47  --symbol_type_check                     false
% 14.93/2.47  --clausify_out                          false
% 14.93/2.47  --sig_cnt_out                           false
% 14.93/2.47  --trig_cnt_out                          false
% 14.93/2.47  --trig_cnt_out_tolerance                1.
% 14.93/2.47  --trig_cnt_out_sk_spl                   false
% 14.93/2.47  --abstr_cl_out                          false
% 14.93/2.47  
% 14.93/2.47  ------ Global Options
% 14.93/2.47  
% 14.93/2.47  --schedule                              default
% 14.93/2.47  --add_important_lit                     false
% 14.93/2.47  --prop_solver_per_cl                    1000
% 14.93/2.47  --min_unsat_core                        false
% 14.93/2.47  --soft_assumptions                      false
% 14.93/2.47  --soft_lemma_size                       3
% 14.93/2.47  --prop_impl_unit_size                   0
% 14.93/2.47  --prop_impl_unit                        []
% 14.93/2.47  --share_sel_clauses                     true
% 14.93/2.47  --reset_solvers                         false
% 14.93/2.47  --bc_imp_inh                            [conj_cone]
% 14.93/2.47  --conj_cone_tolerance                   3.
% 14.93/2.47  --extra_neg_conj                        none
% 14.93/2.47  --large_theory_mode                     true
% 14.93/2.47  --prolific_symb_bound                   200
% 14.93/2.47  --lt_threshold                          2000
% 14.93/2.47  --clause_weak_htbl                      true
% 14.93/2.47  --gc_record_bc_elim                     false
% 14.93/2.47  
% 14.93/2.47  ------ Preprocessing Options
% 14.93/2.47  
% 14.93/2.47  --preprocessing_flag                    true
% 14.93/2.47  --time_out_prep_mult                    0.1
% 14.93/2.47  --splitting_mode                        input
% 14.93/2.47  --splitting_grd                         true
% 14.93/2.47  --splitting_cvd                         false
% 14.93/2.47  --splitting_cvd_svl                     false
% 14.93/2.47  --splitting_nvd                         32
% 14.93/2.47  --sub_typing                            true
% 14.93/2.47  --prep_gs_sim                           true
% 14.93/2.47  --prep_unflatten                        true
% 14.93/2.47  --prep_res_sim                          true
% 14.93/2.47  --prep_upred                            true
% 14.93/2.47  --prep_sem_filter                       exhaustive
% 14.93/2.47  --prep_sem_filter_out                   false
% 14.93/2.47  --pred_elim                             true
% 14.93/2.47  --res_sim_input                         true
% 14.93/2.47  --eq_ax_congr_red                       true
% 14.93/2.47  --pure_diseq_elim                       true
% 14.93/2.47  --brand_transform                       false
% 14.93/2.47  --non_eq_to_eq                          false
% 14.93/2.47  --prep_def_merge                        true
% 14.93/2.47  --prep_def_merge_prop_impl              false
% 14.93/2.47  --prep_def_merge_mbd                    true
% 14.93/2.47  --prep_def_merge_tr_red                 false
% 14.93/2.47  --prep_def_merge_tr_cl                  false
% 14.93/2.47  --smt_preprocessing                     true
% 14.93/2.47  --smt_ac_axioms                         fast
% 14.93/2.47  --preprocessed_out                      false
% 14.93/2.47  --preprocessed_stats                    false
% 14.93/2.47  
% 14.93/2.47  ------ Abstraction refinement Options
% 14.93/2.47  
% 14.93/2.47  --abstr_ref                             []
% 14.93/2.47  --abstr_ref_prep                        false
% 14.93/2.47  --abstr_ref_until_sat                   false
% 14.93/2.47  --abstr_ref_sig_restrict                funpre
% 14.93/2.47  --abstr_ref_af_restrict_to_split_sk     false
% 14.93/2.47  --abstr_ref_under                       []
% 14.93/2.47  
% 14.93/2.47  ------ SAT Options
% 14.93/2.47  
% 14.93/2.47  --sat_mode                              false
% 14.93/2.47  --sat_fm_restart_options                ""
% 14.93/2.47  --sat_gr_def                            false
% 14.93/2.47  --sat_epr_types                         true
% 14.93/2.47  --sat_non_cyclic_types                  false
% 14.93/2.47  --sat_finite_models                     false
% 14.93/2.47  --sat_fm_lemmas                         false
% 14.93/2.47  --sat_fm_prep                           false
% 14.93/2.47  --sat_fm_uc_incr                        true
% 14.93/2.47  --sat_out_model                         small
% 14.93/2.47  --sat_out_clauses                       false
% 14.93/2.47  
% 14.93/2.47  ------ QBF Options
% 14.93/2.47  
% 14.93/2.47  --qbf_mode                              false
% 14.93/2.47  --qbf_elim_univ                         false
% 14.93/2.47  --qbf_dom_inst                          none
% 14.93/2.47  --qbf_dom_pre_inst                      false
% 14.93/2.47  --qbf_sk_in                             false
% 14.93/2.47  --qbf_pred_elim                         true
% 14.93/2.47  --qbf_split                             512
% 14.93/2.47  
% 14.93/2.47  ------ BMC1 Options
% 14.93/2.47  
% 14.93/2.47  --bmc1_incremental                      false
% 14.93/2.47  --bmc1_axioms                           reachable_all
% 14.93/2.47  --bmc1_min_bound                        0
% 14.93/2.47  --bmc1_max_bound                        -1
% 14.93/2.47  --bmc1_max_bound_default                -1
% 14.93/2.47  --bmc1_symbol_reachability              true
% 14.93/2.47  --bmc1_property_lemmas                  false
% 14.93/2.47  --bmc1_k_induction                      false
% 14.93/2.47  --bmc1_non_equiv_states                 false
% 14.93/2.47  --bmc1_deadlock                         false
% 14.93/2.47  --bmc1_ucm                              false
% 14.93/2.47  --bmc1_add_unsat_core                   none
% 14.93/2.47  --bmc1_unsat_core_children              false
% 14.93/2.47  --bmc1_unsat_core_extrapolate_axioms    false
% 14.93/2.47  --bmc1_out_stat                         full
% 14.93/2.47  --bmc1_ground_init                      false
% 14.93/2.47  --bmc1_pre_inst_next_state              false
% 14.93/2.47  --bmc1_pre_inst_state                   false
% 14.93/2.47  --bmc1_pre_inst_reach_state             false
% 14.93/2.47  --bmc1_out_unsat_core                   false
% 14.93/2.47  --bmc1_aig_witness_out                  false
% 14.93/2.47  --bmc1_verbose                          false
% 14.93/2.47  --bmc1_dump_clauses_tptp                false
% 14.93/2.47  --bmc1_dump_unsat_core_tptp             false
% 14.93/2.47  --bmc1_dump_file                        -
% 14.93/2.47  --bmc1_ucm_expand_uc_limit              128
% 14.93/2.47  --bmc1_ucm_n_expand_iterations          6
% 14.93/2.47  --bmc1_ucm_extend_mode                  1
% 14.93/2.47  --bmc1_ucm_init_mode                    2
% 14.93/2.47  --bmc1_ucm_cone_mode                    none
% 14.93/2.47  --bmc1_ucm_reduced_relation_type        0
% 14.93/2.47  --bmc1_ucm_relax_model                  4
% 14.93/2.47  --bmc1_ucm_full_tr_after_sat            true
% 14.93/2.47  --bmc1_ucm_expand_neg_assumptions       false
% 14.93/2.47  --bmc1_ucm_layered_model                none
% 14.93/2.47  --bmc1_ucm_max_lemma_size               10
% 14.93/2.47  
% 14.93/2.47  ------ AIG Options
% 14.93/2.47  
% 14.93/2.47  --aig_mode                              false
% 14.93/2.47  
% 14.93/2.47  ------ Instantiation Options
% 14.93/2.47  
% 14.93/2.47  --instantiation_flag                    true
% 14.93/2.47  --inst_sos_flag                         false
% 14.93/2.47  --inst_sos_phase                        true
% 14.93/2.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 14.93/2.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 14.93/2.47  --inst_lit_sel_side                     num_symb
% 14.93/2.47  --inst_solver_per_active                1400
% 14.93/2.47  --inst_solver_calls_frac                1.
% 14.93/2.47  --inst_passive_queue_type               priority_queues
% 14.93/2.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 14.93/2.47  --inst_passive_queues_freq              [25;2]
% 14.93/2.47  --inst_dismatching                      true
% 14.93/2.47  --inst_eager_unprocessed_to_passive     true
% 14.93/2.47  --inst_prop_sim_given                   true
% 14.93/2.47  --inst_prop_sim_new                     false
% 14.93/2.47  --inst_subs_new                         false
% 14.93/2.47  --inst_eq_res_simp                      false
% 14.93/2.47  --inst_subs_given                       false
% 14.93/2.47  --inst_orphan_elimination               true
% 14.93/2.47  --inst_learning_loop_flag               true
% 14.93/2.47  --inst_learning_start                   3000
% 14.93/2.47  --inst_learning_factor                  2
% 14.93/2.47  --inst_start_prop_sim_after_learn       3
% 14.93/2.47  --inst_sel_renew                        solver
% 14.93/2.47  --inst_lit_activity_flag                true
% 14.93/2.47  --inst_restr_to_given                   false
% 14.93/2.47  --inst_activity_threshold               500
% 14.93/2.47  --inst_out_proof                        true
% 14.93/2.47  
% 14.93/2.47  ------ Resolution Options
% 14.93/2.47  
% 14.93/2.47  --resolution_flag                       true
% 14.93/2.47  --res_lit_sel                           adaptive
% 14.93/2.47  --res_lit_sel_side                      none
% 14.93/2.47  --res_ordering                          kbo
% 14.93/2.47  --res_to_prop_solver                    active
% 14.93/2.47  --res_prop_simpl_new                    false
% 14.93/2.47  --res_prop_simpl_given                  true
% 14.93/2.47  --res_passive_queue_type                priority_queues
% 14.93/2.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 14.93/2.47  --res_passive_queues_freq               [15;5]
% 14.93/2.47  --res_forward_subs                      full
% 14.93/2.47  --res_backward_subs                     full
% 14.93/2.47  --res_forward_subs_resolution           true
% 14.93/2.47  --res_backward_subs_resolution          true
% 14.93/2.47  --res_orphan_elimination                true
% 14.93/2.47  --res_time_limit                        2.
% 14.93/2.47  --res_out_proof                         true
% 14.93/2.47  
% 14.93/2.47  ------ Superposition Options
% 14.93/2.47  
% 14.93/2.47  --superposition_flag                    true
% 14.93/2.47  --sup_passive_queue_type                priority_queues
% 14.93/2.47  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 14.93/2.47  --sup_passive_queues_freq               [8;1;4]
% 14.93/2.47  --demod_completeness_check              fast
% 14.93/2.47  --demod_use_ground                      true
% 14.93/2.47  --sup_to_prop_solver                    passive
% 14.93/2.47  --sup_prop_simpl_new                    true
% 14.93/2.47  --sup_prop_simpl_given                  true
% 14.93/2.47  --sup_fun_splitting                     false
% 14.93/2.47  --sup_smt_interval                      50000
% 14.93/2.47  
% 14.93/2.47  ------ Superposition Simplification Setup
% 14.93/2.47  
% 14.93/2.47  --sup_indices_passive                   []
% 14.93/2.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.93/2.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.93/2.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.93/2.47  --sup_full_triv                         [TrivRules;PropSubs]
% 14.93/2.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.93/2.47  --sup_full_bw                           [BwDemod]
% 14.93/2.47  --sup_immed_triv                        [TrivRules]
% 14.93/2.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 14.93/2.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.93/2.47  --sup_immed_bw_main                     []
% 14.93/2.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.93/2.47  --sup_input_triv                        [Unflattening;TrivRules]
% 14.93/2.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.93/2.47  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.93/2.47  
% 14.93/2.47  ------ Combination Options
% 14.93/2.47  
% 14.93/2.47  --comb_res_mult                         3
% 14.93/2.47  --comb_sup_mult                         2
% 14.93/2.47  --comb_inst_mult                        10
% 14.93/2.47  
% 14.93/2.47  ------ Debug Options
% 14.93/2.47  
% 14.93/2.47  --dbg_backtrace                         false
% 14.93/2.47  --dbg_dump_prop_clauses                 false
% 14.93/2.47  --dbg_dump_prop_clauses_file            -
% 14.93/2.47  --dbg_out_stat                          false
% 14.93/2.47  ------ Parsing...
% 14.93/2.47  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 14.93/2.47  
% 14.93/2.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 14.93/2.47  
% 14.93/2.47  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 14.93/2.47  
% 14.93/2.47  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 14.93/2.47  ------ Proving...
% 14.93/2.47  ------ Problem Properties 
% 14.93/2.47  
% 14.93/2.47  
% 14.93/2.47  clauses                                 6
% 14.93/2.47  conjectures                             1
% 14.93/2.47  EPR                                     0
% 14.93/2.47  Horn                                    6
% 14.93/2.47  unary                                   6
% 14.93/2.47  binary                                  0
% 14.93/2.47  lits                                    6
% 14.93/2.47  lits eq                                 6
% 14.93/2.47  fd_pure                                 0
% 14.93/2.47  fd_pseudo                               0
% 14.93/2.47  fd_cond                                 0
% 14.93/2.47  fd_pseudo_cond                          0
% 14.93/2.47  AC symbols                              0
% 14.93/2.47  
% 14.93/2.47  ------ Schedule UEQ
% 14.93/2.47  
% 14.93/2.47  ------ pure equality problem: resolution off 
% 14.93/2.47  
% 14.93/2.47  ------ Option_UEQ Time Limit: Unbounded
% 14.93/2.47  
% 14.93/2.47  
% 14.93/2.47  ------ 
% 14.93/2.47  Current options:
% 14.93/2.47  ------ 
% 14.93/2.47  
% 14.93/2.47  ------ Input Options
% 14.93/2.47  
% 14.93/2.47  --out_options                           all
% 14.93/2.47  --tptp_safe_out                         true
% 14.93/2.47  --problem_path                          ""
% 14.93/2.47  --include_path                          ""
% 14.93/2.47  --clausifier                            res/vclausify_rel
% 14.93/2.47  --clausifier_options                    --mode clausify
% 14.93/2.47  --stdin                                 false
% 14.93/2.47  --stats_out                             all
% 14.93/2.47  
% 14.93/2.47  ------ General Options
% 14.93/2.47  
% 14.93/2.47  --fof                                   false
% 14.93/2.47  --time_out_real                         305.
% 14.93/2.47  --time_out_virtual                      -1.
% 14.93/2.47  --symbol_type_check                     false
% 14.93/2.47  --clausify_out                          false
% 14.93/2.47  --sig_cnt_out                           false
% 14.93/2.47  --trig_cnt_out                          false
% 14.93/2.47  --trig_cnt_out_tolerance                1.
% 14.93/2.47  --trig_cnt_out_sk_spl                   false
% 14.93/2.47  --abstr_cl_out                          false
% 14.93/2.47  
% 14.93/2.47  ------ Global Options
% 14.93/2.47  
% 14.93/2.47  --schedule                              default
% 14.93/2.47  --add_important_lit                     false
% 14.93/2.47  --prop_solver_per_cl                    1000
% 14.93/2.47  --min_unsat_core                        false
% 14.93/2.47  --soft_assumptions                      false
% 14.93/2.47  --soft_lemma_size                       3
% 14.93/2.47  --prop_impl_unit_size                   0
% 14.93/2.47  --prop_impl_unit                        []
% 14.93/2.47  --share_sel_clauses                     true
% 14.93/2.47  --reset_solvers                         false
% 14.93/2.47  --bc_imp_inh                            [conj_cone]
% 14.93/2.47  --conj_cone_tolerance                   3.
% 14.93/2.47  --extra_neg_conj                        none
% 14.93/2.47  --large_theory_mode                     true
% 14.93/2.47  --prolific_symb_bound                   200
% 14.93/2.47  --lt_threshold                          2000
% 14.93/2.47  --clause_weak_htbl                      true
% 14.93/2.47  --gc_record_bc_elim                     false
% 14.93/2.47  
% 14.93/2.47  ------ Preprocessing Options
% 14.93/2.47  
% 14.93/2.47  --preprocessing_flag                    true
% 14.93/2.47  --time_out_prep_mult                    0.1
% 14.93/2.47  --splitting_mode                        input
% 14.93/2.47  --splitting_grd                         true
% 14.93/2.47  --splitting_cvd                         false
% 14.93/2.47  --splitting_cvd_svl                     false
% 14.93/2.47  --splitting_nvd                         32
% 14.93/2.47  --sub_typing                            true
% 14.93/2.47  --prep_gs_sim                           true
% 14.93/2.47  --prep_unflatten                        true
% 14.93/2.47  --prep_res_sim                          true
% 14.93/2.47  --prep_upred                            true
% 14.93/2.47  --prep_sem_filter                       exhaustive
% 14.93/2.47  --prep_sem_filter_out                   false
% 14.93/2.47  --pred_elim                             true
% 14.93/2.47  --res_sim_input                         true
% 14.93/2.47  --eq_ax_congr_red                       true
% 14.93/2.47  --pure_diseq_elim                       true
% 14.93/2.47  --brand_transform                       false
% 14.93/2.47  --non_eq_to_eq                          false
% 14.93/2.47  --prep_def_merge                        true
% 14.93/2.47  --prep_def_merge_prop_impl              false
% 14.93/2.47  --prep_def_merge_mbd                    true
% 14.93/2.47  --prep_def_merge_tr_red                 false
% 14.93/2.47  --prep_def_merge_tr_cl                  false
% 14.93/2.47  --smt_preprocessing                     true
% 14.93/2.47  --smt_ac_axioms                         fast
% 14.93/2.47  --preprocessed_out                      false
% 14.93/2.47  --preprocessed_stats                    false
% 14.93/2.47  
% 14.93/2.47  ------ Abstraction refinement Options
% 14.93/2.47  
% 14.93/2.47  --abstr_ref                             []
% 14.93/2.47  --abstr_ref_prep                        false
% 14.93/2.47  --abstr_ref_until_sat                   false
% 14.93/2.47  --abstr_ref_sig_restrict                funpre
% 14.93/2.47  --abstr_ref_af_restrict_to_split_sk     false
% 14.93/2.47  --abstr_ref_under                       []
% 14.93/2.47  
% 14.93/2.47  ------ SAT Options
% 14.93/2.47  
% 14.93/2.47  --sat_mode                              false
% 14.93/2.47  --sat_fm_restart_options                ""
% 14.93/2.47  --sat_gr_def                            false
% 14.93/2.47  --sat_epr_types                         true
% 14.93/2.47  --sat_non_cyclic_types                  false
% 14.93/2.47  --sat_finite_models                     false
% 14.93/2.47  --sat_fm_lemmas                         false
% 14.93/2.47  --sat_fm_prep                           false
% 14.93/2.47  --sat_fm_uc_incr                        true
% 14.93/2.47  --sat_out_model                         small
% 14.93/2.47  --sat_out_clauses                       false
% 14.93/2.47  
% 14.93/2.47  ------ QBF Options
% 14.93/2.47  
% 14.93/2.47  --qbf_mode                              false
% 14.93/2.47  --qbf_elim_univ                         false
% 14.93/2.47  --qbf_dom_inst                          none
% 14.93/2.47  --qbf_dom_pre_inst                      false
% 14.93/2.47  --qbf_sk_in                             false
% 14.93/2.47  --qbf_pred_elim                         true
% 14.93/2.47  --qbf_split                             512
% 14.93/2.47  
% 14.93/2.47  ------ BMC1 Options
% 14.93/2.47  
% 14.93/2.47  --bmc1_incremental                      false
% 14.93/2.47  --bmc1_axioms                           reachable_all
% 14.93/2.47  --bmc1_min_bound                        0
% 14.93/2.47  --bmc1_max_bound                        -1
% 14.93/2.47  --bmc1_max_bound_default                -1
% 14.93/2.47  --bmc1_symbol_reachability              true
% 14.93/2.47  --bmc1_property_lemmas                  false
% 14.93/2.47  --bmc1_k_induction                      false
% 14.93/2.47  --bmc1_non_equiv_states                 false
% 14.93/2.47  --bmc1_deadlock                         false
% 14.93/2.47  --bmc1_ucm                              false
% 14.93/2.47  --bmc1_add_unsat_core                   none
% 14.93/2.47  --bmc1_unsat_core_children              false
% 14.93/2.47  --bmc1_unsat_core_extrapolate_axioms    false
% 14.93/2.47  --bmc1_out_stat                         full
% 14.93/2.47  --bmc1_ground_init                      false
% 14.93/2.47  --bmc1_pre_inst_next_state              false
% 14.93/2.47  --bmc1_pre_inst_state                   false
% 14.93/2.47  --bmc1_pre_inst_reach_state             false
% 14.93/2.47  --bmc1_out_unsat_core                   false
% 14.93/2.47  --bmc1_aig_witness_out                  false
% 14.93/2.47  --bmc1_verbose                          false
% 14.93/2.47  --bmc1_dump_clauses_tptp                false
% 14.93/2.47  --bmc1_dump_unsat_core_tptp             false
% 14.93/2.47  --bmc1_dump_file                        -
% 14.93/2.47  --bmc1_ucm_expand_uc_limit              128
% 14.93/2.47  --bmc1_ucm_n_expand_iterations          6
% 14.93/2.47  --bmc1_ucm_extend_mode                  1
% 14.93/2.47  --bmc1_ucm_init_mode                    2
% 14.93/2.47  --bmc1_ucm_cone_mode                    none
% 14.93/2.47  --bmc1_ucm_reduced_relation_type        0
% 14.93/2.47  --bmc1_ucm_relax_model                  4
% 14.93/2.47  --bmc1_ucm_full_tr_after_sat            true
% 14.93/2.47  --bmc1_ucm_expand_neg_assumptions       false
% 14.93/2.47  --bmc1_ucm_layered_model                none
% 14.93/2.47  --bmc1_ucm_max_lemma_size               10
% 14.93/2.47  
% 14.93/2.47  ------ AIG Options
% 14.93/2.47  
% 14.93/2.47  --aig_mode                              false
% 14.93/2.47  
% 14.93/2.47  ------ Instantiation Options
% 14.93/2.47  
% 14.93/2.47  --instantiation_flag                    false
% 14.93/2.47  --inst_sos_flag                         false
% 14.93/2.47  --inst_sos_phase                        true
% 14.93/2.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 14.93/2.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 14.93/2.47  --inst_lit_sel_side                     num_symb
% 14.93/2.47  --inst_solver_per_active                1400
% 14.93/2.47  --inst_solver_calls_frac                1.
% 14.93/2.47  --inst_passive_queue_type               priority_queues
% 14.93/2.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 14.93/2.47  --inst_passive_queues_freq              [25;2]
% 14.93/2.47  --inst_dismatching                      true
% 14.93/2.47  --inst_eager_unprocessed_to_passive     true
% 14.93/2.47  --inst_prop_sim_given                   true
% 14.93/2.47  --inst_prop_sim_new                     false
% 14.93/2.47  --inst_subs_new                         false
% 14.93/2.47  --inst_eq_res_simp                      false
% 14.93/2.47  --inst_subs_given                       false
% 14.93/2.47  --inst_orphan_elimination               true
% 14.93/2.47  --inst_learning_loop_flag               true
% 14.93/2.47  --inst_learning_start                   3000
% 14.93/2.47  --inst_learning_factor                  2
% 14.93/2.47  --inst_start_prop_sim_after_learn       3
% 14.93/2.47  --inst_sel_renew                        solver
% 14.93/2.47  --inst_lit_activity_flag                true
% 14.93/2.47  --inst_restr_to_given                   false
% 14.93/2.47  --inst_activity_threshold               500
% 14.93/2.47  --inst_out_proof                        true
% 14.93/2.47  
% 14.93/2.47  ------ Resolution Options
% 14.93/2.47  
% 14.93/2.47  --resolution_flag                       false
% 14.93/2.47  --res_lit_sel                           adaptive
% 14.93/2.47  --res_lit_sel_side                      none
% 14.93/2.47  --res_ordering                          kbo
% 14.93/2.47  --res_to_prop_solver                    active
% 14.93/2.47  --res_prop_simpl_new                    false
% 14.93/2.47  --res_prop_simpl_given                  true
% 14.93/2.47  --res_passive_queue_type                priority_queues
% 14.93/2.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 14.93/2.47  --res_passive_queues_freq               [15;5]
% 14.93/2.47  --res_forward_subs                      full
% 14.93/2.47  --res_backward_subs                     full
% 14.93/2.47  --res_forward_subs_resolution           true
% 14.93/2.47  --res_backward_subs_resolution          true
% 14.93/2.47  --res_orphan_elimination                true
% 14.93/2.47  --res_time_limit                        2.
% 14.93/2.47  --res_out_proof                         true
% 14.93/2.47  
% 14.93/2.47  ------ Superposition Options
% 14.93/2.47  
% 14.93/2.47  --superposition_flag                    true
% 14.93/2.47  --sup_passive_queue_type                priority_queues
% 14.93/2.47  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 14.93/2.47  --sup_passive_queues_freq               [8;1;4]
% 14.93/2.47  --demod_completeness_check              fast
% 14.93/2.47  --demod_use_ground                      true
% 14.93/2.47  --sup_to_prop_solver                    active
% 14.93/2.47  --sup_prop_simpl_new                    false
% 14.93/2.47  --sup_prop_simpl_given                  false
% 14.93/2.47  --sup_fun_splitting                     true
% 14.93/2.47  --sup_smt_interval                      10000
% 14.93/2.47  
% 14.93/2.47  ------ Superposition Simplification Setup
% 14.93/2.47  
% 14.93/2.47  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 14.93/2.47  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 14.93/2.47  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 14.93/2.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.93/2.47  --sup_full_triv                         [TrivRules]
% 14.93/2.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 14.93/2.47  --sup_full_bw                           [BwDemod;BwSubsumption]
% 14.93/2.47  --sup_immed_triv                        [TrivRules]
% 14.93/2.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 14.93/2.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 14.93/2.47  --sup_immed_bw_main                     []
% 14.93/2.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 14.93/2.47  --sup_input_triv                        [Unflattening;TrivRules]
% 14.93/2.47  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 14.93/2.47  --sup_input_bw                          [BwDemod;BwSubsumption]
% 14.93/2.47  
% 14.93/2.47  ------ Combination Options
% 14.93/2.47  
% 14.93/2.47  --comb_res_mult                         1
% 14.93/2.47  --comb_sup_mult                         1
% 14.93/2.47  --comb_inst_mult                        1000000
% 14.93/2.47  
% 14.93/2.47  ------ Debug Options
% 14.93/2.47  
% 14.93/2.47  --dbg_backtrace                         false
% 14.93/2.47  --dbg_dump_prop_clauses                 false
% 14.93/2.47  --dbg_dump_prop_clauses_file            -
% 14.93/2.47  --dbg_out_stat                          false
% 14.93/2.47  
% 14.93/2.47  
% 14.93/2.47  
% 14.93/2.47  
% 14.93/2.47  ------ Proving...
% 14.93/2.47  
% 14.93/2.47  
% 14.93/2.47  % SZS status Theorem for theBenchmark.p
% 14.93/2.47  
% 14.93/2.47   Resolution empty clause
% 14.93/2.47  
% 14.93/2.47  % SZS output start CNFRefutation for theBenchmark.p
% 14.93/2.47  
% 14.93/2.47  fof(f4,axiom,(
% 14.93/2.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 14.93/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/2.47  
% 14.93/2.47  fof(f15,plain,(
% 14.93/2.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 14.93/2.47    inference(cnf_transformation,[],[f4])).
% 14.93/2.47  
% 14.93/2.47  fof(f5,axiom,(
% 14.93/2.47    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 14.93/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/2.47  
% 14.93/2.47  fof(f16,plain,(
% 14.93/2.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 14.93/2.47    inference(cnf_transformation,[],[f5])).
% 14.93/2.47  
% 14.93/2.47  fof(f19,plain,(
% 14.93/2.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 14.93/2.47    inference(definition_unfolding,[],[f15,f16])).
% 14.93/2.47  
% 14.93/2.47  fof(f3,axiom,(
% 14.93/2.47    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 14.93/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/2.47  
% 14.93/2.47  fof(f14,plain,(
% 14.93/2.47    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 14.93/2.47    inference(cnf_transformation,[],[f3])).
% 14.93/2.47  
% 14.93/2.47  fof(f6,axiom,(
% 14.93/2.47    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 14.93/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/2.47  
% 14.93/2.47  fof(f17,plain,(
% 14.93/2.47    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 14.93/2.47    inference(cnf_transformation,[],[f6])).
% 14.93/2.47  
% 14.93/2.47  fof(f20,plain,(
% 14.93/2.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 14.93/2.47    inference(definition_unfolding,[],[f17,f16])).
% 14.93/2.47  
% 14.93/2.47  fof(f2,axiom,(
% 14.93/2.47    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 14.93/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/2.47  
% 14.93/2.47  fof(f13,plain,(
% 14.93/2.47    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 14.93/2.47    inference(cnf_transformation,[],[f2])).
% 14.93/2.47  
% 14.93/2.47  fof(f1,axiom,(
% 14.93/2.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 14.93/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/2.47  
% 14.93/2.47  fof(f12,plain,(
% 14.93/2.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 14.93/2.47    inference(cnf_transformation,[],[f1])).
% 14.93/2.47  
% 14.93/2.47  fof(f7,conjecture,(
% 14.93/2.47    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 14.93/2.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.93/2.47  
% 14.93/2.47  fof(f8,negated_conjecture,(
% 14.93/2.47    ~! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 14.93/2.47    inference(negated_conjecture,[],[f7])).
% 14.93/2.47  
% 14.93/2.47  fof(f9,plain,(
% 14.93/2.47    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 14.93/2.47    inference(ennf_transformation,[],[f8])).
% 14.93/2.47  
% 14.93/2.47  fof(f10,plain,(
% 14.93/2.47    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 14.93/2.47    introduced(choice_axiom,[])).
% 14.93/2.47  
% 14.93/2.47  fof(f11,plain,(
% 14.93/2.47    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 14.93/2.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f10])).
% 14.93/2.47  
% 14.93/2.47  fof(f18,plain,(
% 14.93/2.47    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 14.93/2.47    inference(cnf_transformation,[],[f11])).
% 14.93/2.47  
% 14.93/2.47  fof(f21,plain,(
% 14.93/2.47    k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 14.93/2.47    inference(definition_unfolding,[],[f18,f16])).
% 14.93/2.47  
% 14.93/2.47  cnf(c_3,plain,
% 14.93/2.47      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 14.93/2.47      inference(cnf_transformation,[],[f19]) ).
% 14.93/2.47  
% 14.93/2.47  cnf(c_2,plain,
% 14.93/2.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 14.93/2.47      inference(cnf_transformation,[],[f14]) ).
% 14.93/2.47  
% 14.93/2.47  cnf(c_81,plain,
% 14.93/2.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k4_xboole_0(k2_xboole_0(X0,X2),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 14.93/2.47      inference(superposition,[status(thm)],[c_3,c_2]) ).
% 14.93/2.47  
% 14.93/2.47  cnf(c_4,plain,
% 14.93/2.47      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 14.93/2.47      inference(cnf_transformation,[],[f20]) ).
% 14.93/2.47  
% 14.93/2.47  cnf(c_1,plain,
% 14.93/2.47      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 14.93/2.47      inference(cnf_transformation,[],[f13]) ).
% 14.93/2.47  
% 14.93/2.47  cnf(c_0,plain,
% 14.93/2.47      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 14.93/2.47      inference(cnf_transformation,[],[f12]) ).
% 14.93/2.47  
% 14.93/2.47  cnf(c_23,plain,
% 14.93/2.47      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 14.93/2.47      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 14.93/2.47  
% 14.93/2.47  cnf(c_70,plain,
% 14.93/2.47      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
% 14.93/2.47      inference(superposition,[status(thm)],[c_4,c_23]) ).
% 14.93/2.47  
% 14.93/2.47  cnf(c_87,plain,
% 14.93/2.47      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X0)) ),
% 14.93/2.47      inference(light_normalisation,[status(thm)],[c_81,c_70]) ).
% 14.93/2.47  
% 14.93/2.47  cnf(c_5,negated_conjecture,
% 14.93/2.47      ( k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
% 14.93/2.47      inference(cnf_transformation,[],[f21]) ).
% 14.93/2.47  
% 14.93/2.47  cnf(c_39147,plain,
% 14.93/2.47      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
% 14.93/2.47      inference(demodulation,[status(thm)],[c_87,c_5]) ).
% 14.93/2.47  
% 14.93/2.47  cnf(c_41544,plain,
% 14.93/2.47      ( $false ),
% 14.93/2.47      inference(equality_resolution_simp,[status(thm)],[c_39147]) ).
% 14.93/2.47  
% 14.93/2.47  
% 14.93/2.47  % SZS output end CNFRefutation for theBenchmark.p
% 14.93/2.47  
% 14.93/2.47  ------                               Statistics
% 14.93/2.47  
% 14.93/2.47  ------ General
% 14.93/2.47  
% 14.93/2.47  abstr_ref_over_cycles:                  0
% 14.93/2.47  abstr_ref_under_cycles:                 0
% 14.93/2.47  gc_basic_clause_elim:                   0
% 14.93/2.47  forced_gc_time:                         0
% 14.93/2.47  parsing_time:                           0.009
% 14.93/2.47  unif_index_cands_time:                  0.
% 14.93/2.47  unif_index_add_time:                    0.
% 14.93/2.47  orderings_time:                         0.
% 14.93/2.47  out_proof_time:                         0.005
% 14.93/2.47  total_time:                             1.509
% 14.93/2.47  num_of_symbols:                         35
% 14.93/2.47  num_of_terms:                           78095
% 14.93/2.47  
% 14.93/2.47  ------ Preprocessing
% 14.93/2.47  
% 14.93/2.47  num_of_splits:                          0
% 14.93/2.47  num_of_split_atoms:                     0
% 14.93/2.47  num_of_reused_defs:                     0
% 14.93/2.47  num_eq_ax_congr_red:                    0
% 14.93/2.47  num_of_sem_filtered_clauses:            0
% 14.93/2.47  num_of_subtypes:                        0
% 14.93/2.47  monotx_restored_types:                  0
% 14.93/2.47  sat_num_of_epr_types:                   0
% 14.93/2.47  sat_num_of_non_cyclic_types:            0
% 14.93/2.47  sat_guarded_non_collapsed_types:        0
% 14.93/2.47  num_pure_diseq_elim:                    0
% 14.93/2.47  simp_replaced_by:                       0
% 14.93/2.47  res_preprocessed:                       16
% 14.93/2.47  prep_upred:                             0
% 14.93/2.47  prep_unflattend:                        0
% 14.93/2.47  smt_new_axioms:                         0
% 14.93/2.47  pred_elim_cands:                        0
% 14.93/2.47  pred_elim:                              0
% 14.93/2.47  pred_elim_cl:                           0
% 14.93/2.47  pred_elim_cycles:                       0
% 14.93/2.47  merged_defs:                            0
% 14.93/2.47  merged_defs_ncl:                        0
% 14.93/2.47  bin_hyper_res:                          0
% 14.93/2.47  prep_cycles:                            2
% 14.93/2.47  pred_elim_time:                         0.
% 14.93/2.47  splitting_time:                         0.
% 14.93/2.47  sem_filter_time:                        0.
% 14.93/2.47  monotx_time:                            0.
% 14.93/2.47  subtype_inf_time:                       0.
% 14.93/2.47  
% 14.93/2.47  ------ Problem properties
% 14.93/2.47  
% 14.93/2.47  clauses:                                6
% 14.93/2.47  conjectures:                            1
% 14.93/2.47  epr:                                    0
% 14.93/2.47  horn:                                   6
% 14.93/2.47  ground:                                 1
% 14.93/2.47  unary:                                  6
% 14.93/2.47  binary:                                 0
% 14.93/2.47  lits:                                   6
% 14.93/2.47  lits_eq:                                6
% 14.93/2.47  fd_pure:                                0
% 14.93/2.47  fd_pseudo:                              0
% 14.93/2.47  fd_cond:                                0
% 14.93/2.47  fd_pseudo_cond:                         0
% 14.93/2.47  ac_symbols:                             0
% 14.93/2.47  
% 14.93/2.47  ------ Propositional Solver
% 14.93/2.47  
% 14.93/2.47  prop_solver_calls:                      13
% 14.93/2.47  prop_fast_solver_calls:                 44
% 14.93/2.47  smt_solver_calls:                       0
% 14.93/2.47  smt_fast_solver_calls:                  0
% 14.93/2.47  prop_num_of_clauses:                    271
% 14.93/2.47  prop_preprocess_simplified:             283
% 14.93/2.47  prop_fo_subsumed:                       0
% 14.93/2.47  prop_solver_time:                       0.
% 14.93/2.47  smt_solver_time:                        0.
% 14.93/2.47  smt_fast_solver_time:                   0.
% 14.93/2.47  prop_fast_solver_time:                  0.
% 14.93/2.47  prop_unsat_core_time:                   0.
% 14.93/2.47  
% 14.93/2.47  ------ QBF
% 14.93/2.47  
% 14.93/2.47  qbf_q_res:                              0
% 14.93/2.47  qbf_num_tautologies:                    0
% 14.93/2.47  qbf_prep_cycles:                        0
% 14.93/2.47  
% 14.93/2.47  ------ BMC1
% 14.93/2.47  
% 14.93/2.47  bmc1_current_bound:                     -1
% 14.93/2.47  bmc1_last_solved_bound:                 -1
% 14.93/2.47  bmc1_unsat_core_size:                   -1
% 14.93/2.47  bmc1_unsat_core_parents_size:           -1
% 14.93/2.47  bmc1_merge_next_fun:                    0
% 14.93/2.47  bmc1_unsat_core_clauses_time:           0.
% 14.93/2.47  
% 14.93/2.47  ------ Instantiation
% 14.93/2.47  
% 14.93/2.47  inst_num_of_clauses:                    0
% 14.93/2.47  inst_num_in_passive:                    0
% 14.93/2.47  inst_num_in_active:                     0
% 14.93/2.47  inst_num_in_unprocessed:                0
% 14.93/2.47  inst_num_of_loops:                      0
% 14.93/2.47  inst_num_of_learning_restarts:          0
% 14.93/2.47  inst_num_moves_active_passive:          0
% 14.93/2.47  inst_lit_activity:                      0
% 14.93/2.47  inst_lit_activity_moves:                0
% 14.93/2.47  inst_num_tautologies:                   0
% 14.93/2.47  inst_num_prop_implied:                  0
% 14.93/2.47  inst_num_existing_simplified:           0
% 14.93/2.47  inst_num_eq_res_simplified:             0
% 14.93/2.47  inst_num_child_elim:                    0
% 14.93/2.47  inst_num_of_dismatching_blockings:      0
% 14.93/2.47  inst_num_of_non_proper_insts:           0
% 14.93/2.47  inst_num_of_duplicates:                 0
% 14.93/2.47  inst_inst_num_from_inst_to_res:         0
% 14.93/2.47  inst_dismatching_checking_time:         0.
% 14.93/2.47  
% 14.93/2.47  ------ Resolution
% 14.93/2.47  
% 14.93/2.47  res_num_of_clauses:                     0
% 14.93/2.47  res_num_in_passive:                     0
% 14.93/2.47  res_num_in_active:                      0
% 14.93/2.47  res_num_of_loops:                       18
% 14.93/2.47  res_forward_subset_subsumed:            0
% 14.93/2.47  res_backward_subset_subsumed:           0
% 14.93/2.47  res_forward_subsumed:                   0
% 14.93/2.47  res_backward_subsumed:                  0
% 14.93/2.47  res_forward_subsumption_resolution:     0
% 14.93/2.47  res_backward_subsumption_resolution:    0
% 14.93/2.47  res_clause_to_clause_subsumption:       201170
% 14.93/2.47  res_orphan_elimination:                 0
% 14.93/2.47  res_tautology_del:                      0
% 14.93/2.47  res_num_eq_res_simplified:              0
% 14.93/2.47  res_num_sel_changes:                    0
% 14.93/2.47  res_moves_from_active_to_pass:          0
% 14.93/2.47  
% 14.93/2.47  ------ Superposition
% 14.93/2.47  
% 14.93/2.47  sup_time_total:                         0.
% 14.93/2.47  sup_time_generating:                    0.
% 14.93/2.47  sup_time_sim_full:                      0.
% 14.93/2.47  sup_time_sim_immed:                     0.
% 14.93/2.47  
% 14.93/2.47  sup_num_of_clauses:                     5889
% 14.93/2.47  sup_num_in_active:                      145
% 14.93/2.47  sup_num_in_passive:                     5744
% 14.93/2.47  sup_num_of_loops:                       167
% 14.93/2.47  sup_fw_superposition:                   12768
% 14.93/2.47  sup_bw_superposition:                   12256
% 14.93/2.47  sup_immediate_simplified:               15509
% 14.93/2.47  sup_given_eliminated:                   3
% 14.93/2.47  comparisons_done:                       0
% 14.93/2.47  comparisons_avoided:                    0
% 14.93/2.47  
% 14.93/2.47  ------ Simplifications
% 14.93/2.47  
% 14.93/2.47  
% 14.93/2.47  sim_fw_subset_subsumed:                 0
% 14.93/2.47  sim_bw_subset_subsumed:                 0
% 14.93/2.47  sim_fw_subsumed:                        2410
% 14.93/2.47  sim_bw_subsumed:                        113
% 14.93/2.47  sim_fw_subsumption_res:                 0
% 14.93/2.47  sim_bw_subsumption_res:                 0
% 14.93/2.47  sim_tautology_del:                      0
% 14.93/2.47  sim_eq_tautology_del:                   4024
% 14.93/2.47  sim_eq_res_simp:                        0
% 14.93/2.47  sim_fw_demodulated:                     10899
% 14.93/2.47  sim_bw_demodulated:                     142
% 14.93/2.47  sim_light_normalised:                   5365
% 14.93/2.47  sim_joinable_taut:                      0
% 14.93/2.47  sim_joinable_simp:                      0
% 14.93/2.47  sim_ac_normalised:                      0
% 14.93/2.47  sim_smt_subsumption:                    0
% 14.93/2.47  
%------------------------------------------------------------------------------
