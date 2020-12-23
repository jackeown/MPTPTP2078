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
% DateTime   : Thu Dec  3 11:26:25 EST 2020

% Result     : Theorem 1.04s
% Output     : CNFRefutation 1.04s
% Verified   : 
% Statistics : Number of formulae       :   25 (  43 expanded)
%              Number of clauses        :    5 (   7 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   26 (  44 expanded)
%              Number of equality atoms :   25 (  43 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) != k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) != k4_enumset1(X0,X1,X2,X3,X4,X5)
   => k2_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) != k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    k2_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) != k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f15,f25])).

fof(f47,plain,(
    k2_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) != k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k2_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(X4)),k1_tarski(X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f43,f48,f48])).

fof(f59,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) ),
    inference(definition_unfolding,[],[f47,f50,f44,f49])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_16,negated_conjecture,
    ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1172,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) ),
    inference(demodulation,[status(thm)],[c_2,c_16])).

cnf(c_1194,plain,
    ( k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) ),
    inference(superposition,[status(thm)],[c_2,c_1172])).

cnf(c_1263,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2,c_1194])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:01:42 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running in FOF mode
% 1.04/1.06  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.04/1.06  
% 1.04/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.04/1.06  
% 1.04/1.06  ------  iProver source info
% 1.04/1.06  
% 1.04/1.06  git: date: 2020-06-30 10:37:57 +0100
% 1.04/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.04/1.06  git: non_committed_changes: false
% 1.04/1.06  git: last_make_outside_of_git: false
% 1.04/1.06  
% 1.04/1.06  ------ 
% 1.04/1.06  
% 1.04/1.06  ------ Input Options
% 1.04/1.06  
% 1.04/1.06  --out_options                           all
% 1.04/1.06  --tptp_safe_out                         true
% 1.04/1.06  --problem_path                          ""
% 1.04/1.06  --include_path                          ""
% 1.04/1.06  --clausifier                            res/vclausify_rel
% 1.04/1.06  --clausifier_options                    --mode clausify
% 1.04/1.06  --stdin                                 false
% 1.04/1.06  --stats_out                             all
% 1.04/1.06  
% 1.04/1.06  ------ General Options
% 1.04/1.06  
% 1.04/1.06  --fof                                   false
% 1.04/1.06  --time_out_real                         305.
% 1.04/1.06  --time_out_virtual                      -1.
% 1.04/1.06  --symbol_type_check                     false
% 1.04/1.06  --clausify_out                          false
% 1.04/1.06  --sig_cnt_out                           false
% 1.04/1.06  --trig_cnt_out                          false
% 1.04/1.06  --trig_cnt_out_tolerance                1.
% 1.04/1.06  --trig_cnt_out_sk_spl                   false
% 1.04/1.06  --abstr_cl_out                          false
% 1.04/1.06  
% 1.04/1.06  ------ Global Options
% 1.04/1.06  
% 1.04/1.06  --schedule                              default
% 1.04/1.06  --add_important_lit                     false
% 1.04/1.06  --prop_solver_per_cl                    1000
% 1.04/1.06  --min_unsat_core                        false
% 1.04/1.06  --soft_assumptions                      false
% 1.04/1.06  --soft_lemma_size                       3
% 1.04/1.06  --prop_impl_unit_size                   0
% 1.04/1.06  --prop_impl_unit                        []
% 1.04/1.06  --share_sel_clauses                     true
% 1.04/1.06  --reset_solvers                         false
% 1.04/1.06  --bc_imp_inh                            [conj_cone]
% 1.04/1.06  --conj_cone_tolerance                   3.
% 1.04/1.06  --extra_neg_conj                        none
% 1.04/1.06  --large_theory_mode                     true
% 1.04/1.06  --prolific_symb_bound                   200
% 1.04/1.06  --lt_threshold                          2000
% 1.04/1.06  --clause_weak_htbl                      true
% 1.04/1.06  --gc_record_bc_elim                     false
% 1.04/1.06  
% 1.04/1.06  ------ Preprocessing Options
% 1.04/1.06  
% 1.04/1.06  --preprocessing_flag                    true
% 1.04/1.06  --time_out_prep_mult                    0.1
% 1.04/1.06  --splitting_mode                        input
% 1.04/1.06  --splitting_grd                         true
% 1.04/1.06  --splitting_cvd                         false
% 1.04/1.06  --splitting_cvd_svl                     false
% 1.04/1.06  --splitting_nvd                         32
% 1.04/1.06  --sub_typing                            true
% 1.04/1.06  --prep_gs_sim                           true
% 1.04/1.06  --prep_unflatten                        true
% 1.04/1.06  --prep_res_sim                          true
% 1.04/1.06  --prep_upred                            true
% 1.04/1.06  --prep_sem_filter                       exhaustive
% 1.04/1.06  --prep_sem_filter_out                   false
% 1.04/1.06  --pred_elim                             true
% 1.04/1.06  --res_sim_input                         true
% 1.04/1.06  --eq_ax_congr_red                       true
% 1.04/1.06  --pure_diseq_elim                       true
% 1.04/1.06  --brand_transform                       false
% 1.04/1.06  --non_eq_to_eq                          false
% 1.04/1.06  --prep_def_merge                        true
% 1.04/1.06  --prep_def_merge_prop_impl              false
% 1.04/1.06  --prep_def_merge_mbd                    true
% 1.04/1.06  --prep_def_merge_tr_red                 false
% 1.04/1.06  --prep_def_merge_tr_cl                  false
% 1.04/1.06  --smt_preprocessing                     true
% 1.04/1.06  --smt_ac_axioms                         fast
% 1.04/1.06  --preprocessed_out                      false
% 1.04/1.06  --preprocessed_stats                    false
% 1.04/1.06  
% 1.04/1.06  ------ Abstraction refinement Options
% 1.04/1.06  
% 1.04/1.06  --abstr_ref                             []
% 1.04/1.06  --abstr_ref_prep                        false
% 1.04/1.06  --abstr_ref_until_sat                   false
% 1.04/1.06  --abstr_ref_sig_restrict                funpre
% 1.04/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 1.04/1.06  --abstr_ref_under                       []
% 1.04/1.06  
% 1.04/1.06  ------ SAT Options
% 1.04/1.06  
% 1.04/1.06  --sat_mode                              false
% 1.04/1.06  --sat_fm_restart_options                ""
% 1.04/1.06  --sat_gr_def                            false
% 1.04/1.06  --sat_epr_types                         true
% 1.04/1.06  --sat_non_cyclic_types                  false
% 1.04/1.06  --sat_finite_models                     false
% 1.04/1.06  --sat_fm_lemmas                         false
% 1.04/1.06  --sat_fm_prep                           false
% 1.04/1.06  --sat_fm_uc_incr                        true
% 1.04/1.06  --sat_out_model                         small
% 1.04/1.06  --sat_out_clauses                       false
% 1.04/1.06  
% 1.04/1.06  ------ QBF Options
% 1.04/1.06  
% 1.04/1.06  --qbf_mode                              false
% 1.04/1.06  --qbf_elim_univ                         false
% 1.04/1.06  --qbf_dom_inst                          none
% 1.04/1.06  --qbf_dom_pre_inst                      false
% 1.04/1.06  --qbf_sk_in                             false
% 1.04/1.06  --qbf_pred_elim                         true
% 1.04/1.06  --qbf_split                             512
% 1.04/1.06  
% 1.04/1.06  ------ BMC1 Options
% 1.04/1.06  
% 1.04/1.06  --bmc1_incremental                      false
% 1.04/1.06  --bmc1_axioms                           reachable_all
% 1.04/1.06  --bmc1_min_bound                        0
% 1.04/1.06  --bmc1_max_bound                        -1
% 1.04/1.06  --bmc1_max_bound_default                -1
% 1.04/1.06  --bmc1_symbol_reachability              true
% 1.04/1.06  --bmc1_property_lemmas                  false
% 1.04/1.06  --bmc1_k_induction                      false
% 1.04/1.06  --bmc1_non_equiv_states                 false
% 1.04/1.06  --bmc1_deadlock                         false
% 1.04/1.06  --bmc1_ucm                              false
% 1.04/1.06  --bmc1_add_unsat_core                   none
% 1.04/1.06  --bmc1_unsat_core_children              false
% 1.04/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 1.04/1.06  --bmc1_out_stat                         full
% 1.04/1.06  --bmc1_ground_init                      false
% 1.04/1.06  --bmc1_pre_inst_next_state              false
% 1.04/1.06  --bmc1_pre_inst_state                   false
% 1.04/1.06  --bmc1_pre_inst_reach_state             false
% 1.04/1.06  --bmc1_out_unsat_core                   false
% 1.04/1.06  --bmc1_aig_witness_out                  false
% 1.04/1.06  --bmc1_verbose                          false
% 1.04/1.06  --bmc1_dump_clauses_tptp                false
% 1.04/1.06  --bmc1_dump_unsat_core_tptp             false
% 1.04/1.06  --bmc1_dump_file                        -
% 1.04/1.06  --bmc1_ucm_expand_uc_limit              128
% 1.04/1.06  --bmc1_ucm_n_expand_iterations          6
% 1.04/1.06  --bmc1_ucm_extend_mode                  1
% 1.04/1.06  --bmc1_ucm_init_mode                    2
% 1.04/1.06  --bmc1_ucm_cone_mode                    none
% 1.04/1.06  --bmc1_ucm_reduced_relation_type        0
% 1.04/1.06  --bmc1_ucm_relax_model                  4
% 1.04/1.06  --bmc1_ucm_full_tr_after_sat            true
% 1.04/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 1.04/1.06  --bmc1_ucm_layered_model                none
% 1.04/1.06  --bmc1_ucm_max_lemma_size               10
% 1.04/1.06  
% 1.04/1.06  ------ AIG Options
% 1.04/1.06  
% 1.04/1.06  --aig_mode                              false
% 1.04/1.06  
% 1.04/1.06  ------ Instantiation Options
% 1.04/1.06  
% 1.04/1.06  --instantiation_flag                    true
% 1.04/1.06  --inst_sos_flag                         false
% 1.04/1.06  --inst_sos_phase                        true
% 1.04/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.04/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.04/1.06  --inst_lit_sel_side                     num_symb
% 1.04/1.06  --inst_solver_per_active                1400
% 1.04/1.06  --inst_solver_calls_frac                1.
% 1.04/1.06  --inst_passive_queue_type               priority_queues
% 1.04/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.04/1.06  --inst_passive_queues_freq              [25;2]
% 1.04/1.06  --inst_dismatching                      true
% 1.04/1.06  --inst_eager_unprocessed_to_passive     true
% 1.04/1.06  --inst_prop_sim_given                   true
% 1.04/1.06  --inst_prop_sim_new                     false
% 1.04/1.06  --inst_subs_new                         false
% 1.04/1.06  --inst_eq_res_simp                      false
% 1.04/1.06  --inst_subs_given                       false
% 1.04/1.06  --inst_orphan_elimination               true
% 1.04/1.06  --inst_learning_loop_flag               true
% 1.04/1.06  --inst_learning_start                   3000
% 1.04/1.06  --inst_learning_factor                  2
% 1.04/1.06  --inst_start_prop_sim_after_learn       3
% 1.04/1.06  --inst_sel_renew                        solver
% 1.04/1.06  --inst_lit_activity_flag                true
% 1.04/1.06  --inst_restr_to_given                   false
% 1.04/1.06  --inst_activity_threshold               500
% 1.04/1.06  --inst_out_proof                        true
% 1.04/1.06  
% 1.04/1.06  ------ Resolution Options
% 1.04/1.06  
% 1.04/1.06  --resolution_flag                       true
% 1.04/1.06  --res_lit_sel                           adaptive
% 1.04/1.06  --res_lit_sel_side                      none
% 1.04/1.06  --res_ordering                          kbo
% 1.04/1.06  --res_to_prop_solver                    active
% 1.04/1.06  --res_prop_simpl_new                    false
% 1.04/1.06  --res_prop_simpl_given                  true
% 1.04/1.06  --res_passive_queue_type                priority_queues
% 1.04/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.04/1.06  --res_passive_queues_freq               [15;5]
% 1.04/1.06  --res_forward_subs                      full
% 1.04/1.06  --res_backward_subs                     full
% 1.04/1.06  --res_forward_subs_resolution           true
% 1.04/1.06  --res_backward_subs_resolution          true
% 1.04/1.06  --res_orphan_elimination                true
% 1.04/1.06  --res_time_limit                        2.
% 1.04/1.06  --res_out_proof                         true
% 1.04/1.06  
% 1.04/1.06  ------ Superposition Options
% 1.04/1.06  
% 1.04/1.06  --superposition_flag                    true
% 1.04/1.06  --sup_passive_queue_type                priority_queues
% 1.04/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.04/1.06  --sup_passive_queues_freq               [8;1;4]
% 1.04/1.06  --demod_completeness_check              fast
% 1.04/1.06  --demod_use_ground                      true
% 1.04/1.06  --sup_to_prop_solver                    passive
% 1.04/1.06  --sup_prop_simpl_new                    true
% 1.04/1.06  --sup_prop_simpl_given                  true
% 1.04/1.06  --sup_fun_splitting                     false
% 1.04/1.06  --sup_smt_interval                      50000
% 1.04/1.06  
% 1.04/1.06  ------ Superposition Simplification Setup
% 1.04/1.06  
% 1.04/1.06  --sup_indices_passive                   []
% 1.04/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.04/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.04/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.04/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 1.04/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.04/1.06  --sup_full_bw                           [BwDemod]
% 1.04/1.06  --sup_immed_triv                        [TrivRules]
% 1.04/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.04/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.04/1.06  --sup_immed_bw_main                     []
% 1.04/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.04/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 1.04/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.04/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.04/1.06  
% 1.04/1.06  ------ Combination Options
% 1.04/1.06  
% 1.04/1.06  --comb_res_mult                         3
% 1.04/1.06  --comb_sup_mult                         2
% 1.04/1.06  --comb_inst_mult                        10
% 1.04/1.06  
% 1.04/1.06  ------ Debug Options
% 1.04/1.06  
% 1.04/1.06  --dbg_backtrace                         false
% 1.04/1.06  --dbg_dump_prop_clauses                 false
% 1.04/1.06  --dbg_dump_prop_clauses_file            -
% 1.04/1.06  --dbg_out_stat                          false
% 1.04/1.06  ------ Parsing...
% 1.04/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.04/1.06  
% 1.04/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.04/1.06  
% 1.04/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.04/1.06  
% 1.04/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.04/1.06  ------ Proving...
% 1.04/1.06  ------ Problem Properties 
% 1.04/1.06  
% 1.04/1.06  
% 1.04/1.06  clauses                                 17
% 1.04/1.06  conjectures                             1
% 1.04/1.06  EPR                                     0
% 1.04/1.06  Horn                                    14
% 1.04/1.06  unary                                   9
% 1.04/1.06  binary                                  1
% 1.04/1.06  lits                                    35
% 1.04/1.06  lits eq                                 23
% 1.04/1.06  fd_pure                                 0
% 1.04/1.06  fd_pseudo                               0
% 1.04/1.06  fd_cond                                 0
% 1.04/1.06  fd_pseudo_cond                          6
% 1.04/1.06  AC symbols                              0
% 1.04/1.06  
% 1.04/1.06  ------ Schedule dynamic 5 is on 
% 1.04/1.06  
% 1.04/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.04/1.06  
% 1.04/1.06  
% 1.04/1.06  ------ 
% 1.04/1.06  Current options:
% 1.04/1.06  ------ 
% 1.04/1.06  
% 1.04/1.06  ------ Input Options
% 1.04/1.06  
% 1.04/1.06  --out_options                           all
% 1.04/1.06  --tptp_safe_out                         true
% 1.04/1.06  --problem_path                          ""
% 1.04/1.06  --include_path                          ""
% 1.04/1.06  --clausifier                            res/vclausify_rel
% 1.04/1.06  --clausifier_options                    --mode clausify
% 1.04/1.06  --stdin                                 false
% 1.04/1.06  --stats_out                             all
% 1.04/1.06  
% 1.04/1.06  ------ General Options
% 1.04/1.06  
% 1.04/1.06  --fof                                   false
% 1.04/1.06  --time_out_real                         305.
% 1.04/1.06  --time_out_virtual                      -1.
% 1.04/1.06  --symbol_type_check                     false
% 1.04/1.06  --clausify_out                          false
% 1.04/1.06  --sig_cnt_out                           false
% 1.04/1.06  --trig_cnt_out                          false
% 1.04/1.06  --trig_cnt_out_tolerance                1.
% 1.04/1.06  --trig_cnt_out_sk_spl                   false
% 1.04/1.06  --abstr_cl_out                          false
% 1.04/1.06  
% 1.04/1.06  ------ Global Options
% 1.04/1.06  
% 1.04/1.06  --schedule                              default
% 1.04/1.06  --add_important_lit                     false
% 1.04/1.06  --prop_solver_per_cl                    1000
% 1.04/1.06  --min_unsat_core                        false
% 1.04/1.06  --soft_assumptions                      false
% 1.04/1.06  --soft_lemma_size                       3
% 1.04/1.06  --prop_impl_unit_size                   0
% 1.04/1.06  --prop_impl_unit                        []
% 1.04/1.06  --share_sel_clauses                     true
% 1.04/1.06  --reset_solvers                         false
% 1.04/1.06  --bc_imp_inh                            [conj_cone]
% 1.04/1.06  --conj_cone_tolerance                   3.
% 1.04/1.06  --extra_neg_conj                        none
% 1.04/1.06  --large_theory_mode                     true
% 1.04/1.06  --prolific_symb_bound                   200
% 1.04/1.06  --lt_threshold                          2000
% 1.04/1.06  --clause_weak_htbl                      true
% 1.04/1.06  --gc_record_bc_elim                     false
% 1.04/1.06  
% 1.04/1.06  ------ Preprocessing Options
% 1.04/1.06  
% 1.04/1.06  --preprocessing_flag                    true
% 1.04/1.06  --time_out_prep_mult                    0.1
% 1.04/1.06  --splitting_mode                        input
% 1.04/1.06  --splitting_grd                         true
% 1.04/1.06  --splitting_cvd                         false
% 1.04/1.06  --splitting_cvd_svl                     false
% 1.04/1.06  --splitting_nvd                         32
% 1.04/1.06  --sub_typing                            true
% 1.04/1.06  --prep_gs_sim                           true
% 1.04/1.06  --prep_unflatten                        true
% 1.04/1.06  --prep_res_sim                          true
% 1.04/1.06  --prep_upred                            true
% 1.04/1.06  --prep_sem_filter                       exhaustive
% 1.04/1.06  --prep_sem_filter_out                   false
% 1.04/1.06  --pred_elim                             true
% 1.04/1.06  --res_sim_input                         true
% 1.04/1.06  --eq_ax_congr_red                       true
% 1.04/1.06  --pure_diseq_elim                       true
% 1.04/1.06  --brand_transform                       false
% 1.04/1.06  --non_eq_to_eq                          false
% 1.04/1.06  --prep_def_merge                        true
% 1.04/1.06  --prep_def_merge_prop_impl              false
% 1.04/1.06  --prep_def_merge_mbd                    true
% 1.04/1.06  --prep_def_merge_tr_red                 false
% 1.04/1.06  --prep_def_merge_tr_cl                  false
% 1.04/1.06  --smt_preprocessing                     true
% 1.04/1.06  --smt_ac_axioms                         fast
% 1.04/1.06  --preprocessed_out                      false
% 1.04/1.06  --preprocessed_stats                    false
% 1.04/1.06  
% 1.04/1.06  ------ Abstraction refinement Options
% 1.04/1.06  
% 1.04/1.06  --abstr_ref                             []
% 1.04/1.06  --abstr_ref_prep                        false
% 1.04/1.06  --abstr_ref_until_sat                   false
% 1.04/1.06  --abstr_ref_sig_restrict                funpre
% 1.04/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 1.04/1.06  --abstr_ref_under                       []
% 1.04/1.06  
% 1.04/1.06  ------ SAT Options
% 1.04/1.06  
% 1.04/1.06  --sat_mode                              false
% 1.04/1.06  --sat_fm_restart_options                ""
% 1.04/1.06  --sat_gr_def                            false
% 1.04/1.06  --sat_epr_types                         true
% 1.04/1.06  --sat_non_cyclic_types                  false
% 1.04/1.06  --sat_finite_models                     false
% 1.04/1.06  --sat_fm_lemmas                         false
% 1.04/1.06  --sat_fm_prep                           false
% 1.04/1.06  --sat_fm_uc_incr                        true
% 1.04/1.06  --sat_out_model                         small
% 1.04/1.06  --sat_out_clauses                       false
% 1.04/1.06  
% 1.04/1.06  ------ QBF Options
% 1.04/1.06  
% 1.04/1.06  --qbf_mode                              false
% 1.04/1.06  --qbf_elim_univ                         false
% 1.04/1.06  --qbf_dom_inst                          none
% 1.04/1.06  --qbf_dom_pre_inst                      false
% 1.04/1.06  --qbf_sk_in                             false
% 1.04/1.06  --qbf_pred_elim                         true
% 1.04/1.06  --qbf_split                             512
% 1.04/1.06  
% 1.04/1.06  ------ BMC1 Options
% 1.04/1.06  
% 1.04/1.06  --bmc1_incremental                      false
% 1.04/1.06  --bmc1_axioms                           reachable_all
% 1.04/1.06  --bmc1_min_bound                        0
% 1.04/1.06  --bmc1_max_bound                        -1
% 1.04/1.06  --bmc1_max_bound_default                -1
% 1.04/1.06  --bmc1_symbol_reachability              true
% 1.04/1.06  --bmc1_property_lemmas                  false
% 1.04/1.06  --bmc1_k_induction                      false
% 1.04/1.06  --bmc1_non_equiv_states                 false
% 1.04/1.06  --bmc1_deadlock                         false
% 1.04/1.06  --bmc1_ucm                              false
% 1.04/1.06  --bmc1_add_unsat_core                   none
% 1.04/1.06  --bmc1_unsat_core_children              false
% 1.04/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 1.04/1.06  --bmc1_out_stat                         full
% 1.04/1.06  --bmc1_ground_init                      false
% 1.04/1.06  --bmc1_pre_inst_next_state              false
% 1.04/1.06  --bmc1_pre_inst_state                   false
% 1.04/1.06  --bmc1_pre_inst_reach_state             false
% 1.04/1.06  --bmc1_out_unsat_core                   false
% 1.04/1.06  --bmc1_aig_witness_out                  false
% 1.04/1.06  --bmc1_verbose                          false
% 1.04/1.06  --bmc1_dump_clauses_tptp                false
% 1.04/1.06  --bmc1_dump_unsat_core_tptp             false
% 1.04/1.06  --bmc1_dump_file                        -
% 1.04/1.06  --bmc1_ucm_expand_uc_limit              128
% 1.04/1.06  --bmc1_ucm_n_expand_iterations          6
% 1.04/1.06  --bmc1_ucm_extend_mode                  1
% 1.04/1.06  --bmc1_ucm_init_mode                    2
% 1.04/1.06  --bmc1_ucm_cone_mode                    none
% 1.04/1.06  --bmc1_ucm_reduced_relation_type        0
% 1.04/1.06  --bmc1_ucm_relax_model                  4
% 1.04/1.06  --bmc1_ucm_full_tr_after_sat            true
% 1.04/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 1.04/1.06  --bmc1_ucm_layered_model                none
% 1.04/1.06  --bmc1_ucm_max_lemma_size               10
% 1.04/1.06  
% 1.04/1.06  ------ AIG Options
% 1.04/1.06  
% 1.04/1.06  --aig_mode                              false
% 1.04/1.06  
% 1.04/1.06  ------ Instantiation Options
% 1.04/1.06  
% 1.04/1.06  --instantiation_flag                    true
% 1.04/1.06  --inst_sos_flag                         false
% 1.04/1.06  --inst_sos_phase                        true
% 1.04/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.04/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.04/1.06  --inst_lit_sel_side                     none
% 1.04/1.06  --inst_solver_per_active                1400
% 1.04/1.06  --inst_solver_calls_frac                1.
% 1.04/1.06  --inst_passive_queue_type               priority_queues
% 1.04/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.04/1.06  --inst_passive_queues_freq              [25;2]
% 1.04/1.06  --inst_dismatching                      true
% 1.04/1.06  --inst_eager_unprocessed_to_passive     true
% 1.04/1.06  --inst_prop_sim_given                   true
% 1.04/1.06  --inst_prop_sim_new                     false
% 1.04/1.06  --inst_subs_new                         false
% 1.04/1.06  --inst_eq_res_simp                      false
% 1.04/1.06  --inst_subs_given                       false
% 1.04/1.06  --inst_orphan_elimination               true
% 1.04/1.06  --inst_learning_loop_flag               true
% 1.04/1.06  --inst_learning_start                   3000
% 1.04/1.06  --inst_learning_factor                  2
% 1.04/1.06  --inst_start_prop_sim_after_learn       3
% 1.04/1.06  --inst_sel_renew                        solver
% 1.04/1.06  --inst_lit_activity_flag                true
% 1.04/1.06  --inst_restr_to_given                   false
% 1.04/1.06  --inst_activity_threshold               500
% 1.04/1.06  --inst_out_proof                        true
% 1.04/1.06  
% 1.04/1.06  ------ Resolution Options
% 1.04/1.06  
% 1.04/1.06  --resolution_flag                       false
% 1.04/1.06  --res_lit_sel                           adaptive
% 1.04/1.06  --res_lit_sel_side                      none
% 1.04/1.06  --res_ordering                          kbo
% 1.04/1.06  --res_to_prop_solver                    active
% 1.04/1.06  --res_prop_simpl_new                    false
% 1.04/1.06  --res_prop_simpl_given                  true
% 1.04/1.06  --res_passive_queue_type                priority_queues
% 1.04/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.04/1.06  --res_passive_queues_freq               [15;5]
% 1.04/1.06  --res_forward_subs                      full
% 1.04/1.06  --res_backward_subs                     full
% 1.04/1.06  --res_forward_subs_resolution           true
% 1.04/1.06  --res_backward_subs_resolution          true
% 1.04/1.06  --res_orphan_elimination                true
% 1.04/1.06  --res_time_limit                        2.
% 1.04/1.06  --res_out_proof                         true
% 1.04/1.06  
% 1.04/1.06  ------ Superposition Options
% 1.04/1.06  
% 1.04/1.06  --superposition_flag                    true
% 1.04/1.06  --sup_passive_queue_type                priority_queues
% 1.04/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.04/1.06  --sup_passive_queues_freq               [8;1;4]
% 1.04/1.06  --demod_completeness_check              fast
% 1.04/1.06  --demod_use_ground                      true
% 1.04/1.06  --sup_to_prop_solver                    passive
% 1.04/1.06  --sup_prop_simpl_new                    true
% 1.04/1.06  --sup_prop_simpl_given                  true
% 1.04/1.06  --sup_fun_splitting                     false
% 1.04/1.06  --sup_smt_interval                      50000
% 1.04/1.06  
% 1.04/1.06  ------ Superposition Simplification Setup
% 1.04/1.06  
% 1.04/1.06  --sup_indices_passive                   []
% 1.04/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.04/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.04/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.04/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 1.04/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.04/1.06  --sup_full_bw                           [BwDemod]
% 1.04/1.06  --sup_immed_triv                        [TrivRules]
% 1.04/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.04/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.04/1.06  --sup_immed_bw_main                     []
% 1.04/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.04/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 1.04/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.04/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.04/1.06  
% 1.04/1.06  ------ Combination Options
% 1.04/1.06  
% 1.04/1.06  --comb_res_mult                         3
% 1.04/1.06  --comb_sup_mult                         2
% 1.04/1.06  --comb_inst_mult                        10
% 1.04/1.06  
% 1.04/1.06  ------ Debug Options
% 1.04/1.06  
% 1.04/1.06  --dbg_backtrace                         false
% 1.04/1.06  --dbg_dump_prop_clauses                 false
% 1.04/1.06  --dbg_dump_prop_clauses_file            -
% 1.04/1.06  --dbg_out_stat                          false
% 1.04/1.06  
% 1.04/1.06  
% 1.04/1.06  
% 1.04/1.06  
% 1.04/1.06  ------ Proving...
% 1.04/1.06  
% 1.04/1.06  
% 1.04/1.06  % SZS status Theorem for theBenchmark.p
% 1.04/1.06  
% 1.04/1.06   Resolution empty clause
% 1.04/1.06  
% 1.04/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 1.04/1.06  
% 1.04/1.06  fof(f3,axiom,(
% 1.04/1.06    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 1.04/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.04/1.06  
% 1.04/1.06  fof(f29,plain,(
% 1.04/1.06    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 1.04/1.06    inference(cnf_transformation,[],[f3])).
% 1.04/1.06  
% 1.04/1.06  fof(f11,conjecture,(
% 1.04/1.06    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.04/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.04/1.06  
% 1.04/1.06  fof(f12,negated_conjecture,(
% 1.04/1.06    ~! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.04/1.06    inference(negated_conjecture,[],[f11])).
% 1.04/1.06  
% 1.04/1.06  fof(f15,plain,(
% 1.04/1.06    ? [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) != k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.04/1.06    inference(ennf_transformation,[],[f12])).
% 1.04/1.06  
% 1.04/1.06  fof(f25,plain,(
% 1.04/1.06    ? [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) != k4_enumset1(X0,X1,X2,X3,X4,X5) => k2_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) != k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)),
% 1.04/1.06    introduced(choice_axiom,[])).
% 1.04/1.06  
% 1.04/1.06  fof(f26,plain,(
% 1.04/1.06    k2_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) != k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)),
% 1.04/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7])],[f15,f25])).
% 1.04/1.06  
% 1.04/1.06  fof(f47,plain,(
% 1.04/1.06    k2_xboole_0(k2_enumset1(sK2,sK3,sK4,sK5),k2_tarski(sK6,sK7)) != k4_enumset1(sK2,sK3,sK4,sK5,sK6,sK7)),
% 1.04/1.06    inference(cnf_transformation,[],[f26])).
% 1.04/1.06  
% 1.04/1.06  fof(f10,axiom,(
% 1.04/1.06    ! [X0,X1,X2,X3] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)),
% 1.04/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.04/1.06  
% 1.04/1.06  fof(f46,plain,(
% 1.04/1.06    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.04/1.06    inference(cnf_transformation,[],[f10])).
% 1.04/1.06  
% 1.04/1.06  fof(f50,plain,(
% 1.04/1.06    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k1_tarski(X3)) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.04/1.06    inference(definition_unfolding,[],[f46,f48])).
% 1.04/1.06  
% 1.04/1.06  fof(f7,axiom,(
% 1.04/1.06    ! [X0,X1,X2,X3,X4,X5] : k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.04/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.04/1.06  
% 1.04/1.06  fof(f43,plain,(
% 1.04/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.04/1.06    inference(cnf_transformation,[],[f7])).
% 1.04/1.06  
% 1.04/1.06  fof(f9,axiom,(
% 1.04/1.06    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)),
% 1.04/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.04/1.06  
% 1.04/1.06  fof(f45,plain,(
% 1.04/1.06    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)) )),
% 1.04/1.06    inference(cnf_transformation,[],[f9])).
% 1.04/1.06  
% 1.04/1.06  fof(f8,axiom,(
% 1.04/1.06    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 1.04/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.04/1.06  
% 1.04/1.06  fof(f44,plain,(
% 1.04/1.06    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 1.04/1.06    inference(cnf_transformation,[],[f8])).
% 1.04/1.06  
% 1.04/1.06  fof(f48,plain,(
% 1.04/1.06    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) = k1_enumset1(X0,X1,X2)) )),
% 1.04/1.06    inference(definition_unfolding,[],[f45,f44])).
% 1.04/1.06  
% 1.04/1.06  fof(f49,plain,(
% 1.04/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k2_xboole_0(k2_xboole_0(k1_tarski(X3),k1_tarski(X4)),k1_tarski(X5))) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.04/1.06    inference(definition_unfolding,[],[f43,f48,f48])).
% 1.04/1.06  
% 1.04/1.06  fof(f59,plain,(
% 1.04/1.06    k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7)))),
% 1.04/1.06    inference(definition_unfolding,[],[f47,f50,f44,f49])).
% 1.04/1.06  
% 1.04/1.06  cnf(c_2,plain,
% 1.04/1.06      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 1.04/1.06      inference(cnf_transformation,[],[f29]) ).
% 1.04/1.06  
% 1.04/1.06  cnf(c_16,negated_conjecture,
% 1.04/1.06      ( k2_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k1_tarski(sK4)),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) ),
% 1.04/1.06      inference(cnf_transformation,[],[f59]) ).
% 1.04/1.06  
% 1.04/1.06  cnf(c_1172,plain,
% 1.04/1.06      ( k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) != k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k1_tarski(sK5)),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7))) ),
% 1.04/1.06      inference(demodulation,[status(thm)],[c_2,c_16]) ).
% 1.04/1.06  
% 1.04/1.06  cnf(c_1194,plain,
% 1.04/1.06      ( k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k1_tarski(sK5),k2_xboole_0(k1_tarski(sK6),k1_tarski(sK7)))) != k2_xboole_0(k2_xboole_0(k1_tarski(sK2),k2_xboole_0(k1_tarski(sK3),k1_tarski(sK4))),k2_xboole_0(k2_xboole_0(k1_tarski(sK5),k1_tarski(sK6)),k1_tarski(sK7))) ),
% 1.04/1.06      inference(superposition,[status(thm)],[c_2,c_1172]) ).
% 1.04/1.06  
% 1.04/1.06  cnf(c_1263,plain,
% 1.04/1.06      ( $false ),
% 1.04/1.06      inference(superposition,[status(thm)],[c_2,c_1194]) ).
% 1.04/1.06  
% 1.04/1.06  
% 1.04/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 1.04/1.06  
% 1.04/1.06  ------                               Statistics
% 1.04/1.06  
% 1.04/1.06  ------ General
% 1.04/1.06  
% 1.04/1.06  abstr_ref_over_cycles:                  0
% 1.04/1.06  abstr_ref_under_cycles:                 0
% 1.04/1.06  gc_basic_clause_elim:                   0
% 1.04/1.06  forced_gc_time:                         0
% 1.04/1.06  parsing_time:                           0.023
% 1.04/1.06  unif_index_cands_time:                  0.
% 1.04/1.06  unif_index_add_time:                    0.
% 1.04/1.06  orderings_time:                         0.
% 1.04/1.06  out_proof_time:                         0.008
% 1.04/1.06  total_time:                             0.124
% 1.04/1.06  num_of_symbols:                         42
% 1.04/1.06  num_of_terms:                           1436
% 1.04/1.06  
% 1.04/1.06  ------ Preprocessing
% 1.04/1.06  
% 1.04/1.06  num_of_splits:                          0
% 1.04/1.06  num_of_split_atoms:                     0
% 1.04/1.06  num_of_reused_defs:                     0
% 1.04/1.06  num_eq_ax_congr_red:                    12
% 1.04/1.06  num_of_sem_filtered_clauses:            1
% 1.04/1.06  num_of_subtypes:                        0
% 1.04/1.06  monotx_restored_types:                  0
% 1.04/1.06  sat_num_of_epr_types:                   0
% 1.04/1.06  sat_num_of_non_cyclic_types:            0
% 1.04/1.06  sat_guarded_non_collapsed_types:        0
% 1.04/1.06  num_pure_diseq_elim:                    0
% 1.04/1.06  simp_replaced_by:                       0
% 1.04/1.06  res_preprocessed:                       62
% 1.04/1.06  prep_upred:                             0
% 1.04/1.06  prep_unflattend:                        36
% 1.04/1.06  smt_new_axioms:                         0
% 1.04/1.06  pred_elim_cands:                        1
% 1.04/1.06  pred_elim:                              0
% 1.04/1.06  pred_elim_cl:                           0
% 1.04/1.06  pred_elim_cycles:                       1
% 1.04/1.06  merged_defs:                            0
% 1.04/1.06  merged_defs_ncl:                        0
% 1.04/1.06  bin_hyper_res:                          0
% 1.04/1.06  prep_cycles:                            3
% 1.04/1.06  pred_elim_time:                         0.023
% 1.04/1.06  splitting_time:                         0.
% 1.04/1.06  sem_filter_time:                        0.
% 1.04/1.06  monotx_time:                            0.
% 1.04/1.06  subtype_inf_time:                       0.
% 1.04/1.06  
% 1.04/1.06  ------ Problem properties
% 1.04/1.06  
% 1.04/1.06  clauses:                                17
% 1.04/1.06  conjectures:                            1
% 1.04/1.06  epr:                                    0
% 1.04/1.06  horn:                                   14
% 1.04/1.06  ground:                                 1
% 1.04/1.06  unary:                                  9
% 1.04/1.06  binary:                                 1
% 1.04/1.06  lits:                                   35
% 1.04/1.06  lits_eq:                                23
% 1.04/1.06  fd_pure:                                0
% 1.04/1.06  fd_pseudo:                              0
% 1.04/1.06  fd_cond:                                0
% 1.04/1.06  fd_pseudo_cond:                         6
% 1.04/1.06  ac_symbols:                             0
% 1.04/1.06  
% 1.04/1.06  ------ Propositional Solver
% 1.04/1.06  
% 1.04/1.06  prop_solver_calls:                      20
% 1.04/1.06  prop_fast_solver_calls:                 385
% 1.04/1.06  smt_solver_calls:                       0
% 1.04/1.06  smt_fast_solver_calls:                  0
% 1.04/1.06  prop_num_of_clauses:                    300
% 1.04/1.06  prop_preprocess_simplified:             1889
% 1.04/1.06  prop_fo_subsumed:                       0
% 1.04/1.06  prop_solver_time:                       0.
% 1.04/1.06  smt_solver_time:                        0.
% 1.04/1.06  smt_fast_solver_time:                   0.
% 1.04/1.06  prop_fast_solver_time:                  0.
% 1.04/1.06  prop_unsat_core_time:                   0.
% 1.04/1.06  
% 1.04/1.06  ------ QBF
% 1.04/1.06  
% 1.04/1.06  qbf_q_res:                              0
% 1.04/1.06  qbf_num_tautologies:                    0
% 1.04/1.06  qbf_prep_cycles:                        0
% 1.04/1.06  
% 1.04/1.06  ------ BMC1
% 1.04/1.06  
% 1.04/1.06  bmc1_current_bound:                     -1
% 1.04/1.06  bmc1_last_solved_bound:                 -1
% 1.04/1.06  bmc1_unsat_core_size:                   -1
% 1.04/1.06  bmc1_unsat_core_parents_size:           -1
% 1.04/1.06  bmc1_merge_next_fun:                    0
% 1.04/1.06  bmc1_unsat_core_clauses_time:           0.
% 1.04/1.06  
% 1.04/1.06  ------ Instantiation
% 1.04/1.06  
% 1.04/1.06  inst_num_of_clauses:                    94
% 1.04/1.06  inst_num_in_passive:                    18
% 1.04/1.06  inst_num_in_active:                     39
% 1.04/1.06  inst_num_in_unprocessed:                37
% 1.04/1.06  inst_num_of_loops:                      40
% 1.04/1.06  inst_num_of_learning_restarts:          0
% 1.04/1.06  inst_num_moves_active_passive:          0
% 1.04/1.06  inst_lit_activity:                      0
% 1.04/1.06  inst_lit_activity_moves:                0
% 1.04/1.06  inst_num_tautologies:                   0
% 1.04/1.06  inst_num_prop_implied:                  0
% 1.04/1.06  inst_num_existing_simplified:           0
% 1.04/1.06  inst_num_eq_res_simplified:             0
% 1.04/1.06  inst_num_child_elim:                    0
% 1.04/1.06  inst_num_of_dismatching_blockings:      4
% 1.04/1.06  inst_num_of_non_proper_insts:           36
% 1.04/1.06  inst_num_of_duplicates:                 0
% 1.04/1.06  inst_inst_num_from_inst_to_res:         0
% 1.04/1.06  inst_dismatching_checking_time:         0.
% 1.04/1.06  
% 1.04/1.06  ------ Resolution
% 1.04/1.06  
% 1.04/1.06  res_num_of_clauses:                     0
% 1.04/1.06  res_num_in_passive:                     0
% 1.04/1.06  res_num_in_active:                      0
% 1.04/1.06  res_num_of_loops:                       65
% 1.04/1.06  res_forward_subset_subsumed:            5
% 1.04/1.06  res_backward_subset_subsumed:           0
% 1.04/1.06  res_forward_subsumed:                   0
% 1.04/1.06  res_backward_subsumed:                  0
% 1.04/1.06  res_forward_subsumption_resolution:     0
% 1.04/1.06  res_backward_subsumption_resolution:    0
% 1.04/1.06  res_clause_to_clause_subsumption:       311
% 1.04/1.06  res_orphan_elimination:                 0
% 1.04/1.06  res_tautology_del:                      4
% 1.04/1.06  res_num_eq_res_simplified:              0
% 1.04/1.06  res_num_sel_changes:                    0
% 1.04/1.06  res_moves_from_active_to_pass:          0
% 1.04/1.06  
% 1.04/1.06  ------ Superposition
% 1.04/1.06  
% 1.04/1.06  sup_time_total:                         0.
% 1.04/1.06  sup_time_generating:                    0.
% 1.04/1.06  sup_time_sim_full:                      0.
% 1.04/1.06  sup_time_sim_immed:                     0.
% 1.04/1.06  
% 1.04/1.06  sup_num_of_clauses:                     22
% 1.04/1.06  sup_num_in_active:                      6
% 1.04/1.06  sup_num_in_passive:                     16
% 1.04/1.06  sup_num_of_loops:                       6
% 1.04/1.06  sup_fw_superposition:                   7
% 1.04/1.06  sup_bw_superposition:                   3
% 1.04/1.06  sup_immediate_simplified:               4
% 1.04/1.06  sup_given_eliminated:                   0
% 1.04/1.06  comparisons_done:                       0
% 1.04/1.06  comparisons_avoided:                    0
% 1.04/1.06  
% 1.04/1.06  ------ Simplifications
% 1.04/1.06  
% 1.04/1.06  
% 1.04/1.06  sim_fw_subset_subsumed:                 0
% 1.04/1.06  sim_bw_subset_subsumed:                 0
% 1.04/1.06  sim_fw_subsumed:                        1
% 1.04/1.06  sim_bw_subsumed:                        0
% 1.04/1.06  sim_fw_subsumption_res:                 0
% 1.04/1.06  sim_bw_subsumption_res:                 0
% 1.04/1.06  sim_tautology_del:                      0
% 1.04/1.06  sim_eq_tautology_del:                   0
% 1.04/1.06  sim_eq_res_simp:                        0
% 1.04/1.06  sim_fw_demodulated:                     0
% 1.04/1.06  sim_bw_demodulated:                     1
% 1.04/1.06  sim_light_normalised:                   4
% 1.04/1.06  sim_joinable_taut:                      0
% 1.04/1.06  sim_joinable_simp:                      0
% 1.04/1.06  sim_ac_normalised:                      0
% 1.04/1.06  sim_smt_subsumption:                    0
% 1.04/1.06  
%------------------------------------------------------------------------------
