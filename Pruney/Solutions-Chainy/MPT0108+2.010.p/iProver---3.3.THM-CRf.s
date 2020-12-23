%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:30 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   45 (  68 expanded)
%              Number of clauses        :   17 (  21 expanded)
%              Number of leaves         :   11 (  20 expanded)
%              Depth                    :   13
%              Number of atoms          :   46 (  69 expanded)
%              Number of equality atoms :   45 (  68 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,conjecture,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1)
   => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f26,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f25,f18])).

fof(f31,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f26,f18,f27])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f21,f18,f18])).

fof(f5,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(definition_unfolding,[],[f19,f27])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_8,negated_conjecture,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_27,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1,c_8])).

cnf(c_32,plain,
    ( k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) != k5_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1,c_27])).

cnf(c_68,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_6,c_32])).

cnf(c_132,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_6,c_68])).

cnf(c_4,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_97,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_133,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_132,c_97])).

cnf(c_3,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_53,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_2])).

cnf(c_134,plain,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_133,c_3,c_5,c_7,c_53])).

cnf(c_135,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_134])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.15/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.00  
% 2.15/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.15/1.00  
% 2.15/1.00  ------  iProver source info
% 2.15/1.00  
% 2.15/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.15/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.15/1.00  git: non_committed_changes: false
% 2.15/1.00  git: last_make_outside_of_git: false
% 2.15/1.00  
% 2.15/1.00  ------ 
% 2.15/1.00  
% 2.15/1.00  ------ Input Options
% 2.15/1.00  
% 2.15/1.00  --out_options                           all
% 2.15/1.00  --tptp_safe_out                         true
% 2.15/1.00  --problem_path                          ""
% 2.15/1.00  --include_path                          ""
% 2.15/1.00  --clausifier                            res/vclausify_rel
% 2.15/1.00  --clausifier_options                    --mode clausify
% 2.15/1.00  --stdin                                 false
% 2.15/1.00  --stats_out                             all
% 2.15/1.00  
% 2.15/1.00  ------ General Options
% 2.15/1.00  
% 2.15/1.00  --fof                                   false
% 2.15/1.00  --time_out_real                         305.
% 2.15/1.00  --time_out_virtual                      -1.
% 2.15/1.00  --symbol_type_check                     false
% 2.15/1.00  --clausify_out                          false
% 2.15/1.00  --sig_cnt_out                           false
% 2.15/1.00  --trig_cnt_out                          false
% 2.15/1.00  --trig_cnt_out_tolerance                1.
% 2.15/1.00  --trig_cnt_out_sk_spl                   false
% 2.15/1.00  --abstr_cl_out                          false
% 2.15/1.00  
% 2.15/1.00  ------ Global Options
% 2.15/1.00  
% 2.15/1.00  --schedule                              default
% 2.15/1.00  --add_important_lit                     false
% 2.15/1.00  --prop_solver_per_cl                    1000
% 2.15/1.00  --min_unsat_core                        false
% 2.15/1.00  --soft_assumptions                      false
% 2.15/1.00  --soft_lemma_size                       3
% 2.15/1.00  --prop_impl_unit_size                   0
% 2.15/1.00  --prop_impl_unit                        []
% 2.15/1.00  --share_sel_clauses                     true
% 2.15/1.00  --reset_solvers                         false
% 2.15/1.00  --bc_imp_inh                            [conj_cone]
% 2.15/1.00  --conj_cone_tolerance                   3.
% 2.15/1.00  --extra_neg_conj                        none
% 2.15/1.00  --large_theory_mode                     true
% 2.15/1.00  --prolific_symb_bound                   200
% 2.15/1.00  --lt_threshold                          2000
% 2.15/1.00  --clause_weak_htbl                      true
% 2.15/1.00  --gc_record_bc_elim                     false
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing Options
% 2.15/1.00  
% 2.15/1.00  --preprocessing_flag                    true
% 2.15/1.00  --time_out_prep_mult                    0.1
% 2.15/1.00  --splitting_mode                        input
% 2.15/1.00  --splitting_grd                         true
% 2.15/1.00  --splitting_cvd                         false
% 2.15/1.00  --splitting_cvd_svl                     false
% 2.15/1.00  --splitting_nvd                         32
% 2.15/1.00  --sub_typing                            true
% 2.15/1.00  --prep_gs_sim                           true
% 2.15/1.00  --prep_unflatten                        true
% 2.15/1.00  --prep_res_sim                          true
% 2.15/1.00  --prep_upred                            true
% 2.15/1.00  --prep_sem_filter                       exhaustive
% 2.15/1.00  --prep_sem_filter_out                   false
% 2.15/1.00  --pred_elim                             true
% 2.15/1.00  --res_sim_input                         true
% 2.15/1.00  --eq_ax_congr_red                       true
% 2.15/1.00  --pure_diseq_elim                       true
% 2.15/1.00  --brand_transform                       false
% 2.15/1.00  --non_eq_to_eq                          false
% 2.15/1.00  --prep_def_merge                        true
% 2.15/1.00  --prep_def_merge_prop_impl              false
% 2.15/1.00  --prep_def_merge_mbd                    true
% 2.15/1.00  --prep_def_merge_tr_red                 false
% 2.15/1.00  --prep_def_merge_tr_cl                  false
% 2.15/1.00  --smt_preprocessing                     true
% 2.15/1.00  --smt_ac_axioms                         fast
% 2.15/1.00  --preprocessed_out                      false
% 2.15/1.00  --preprocessed_stats                    false
% 2.15/1.00  
% 2.15/1.00  ------ Abstraction refinement Options
% 2.15/1.00  
% 2.15/1.00  --abstr_ref                             []
% 2.15/1.00  --abstr_ref_prep                        false
% 2.15/1.00  --abstr_ref_until_sat                   false
% 2.15/1.00  --abstr_ref_sig_restrict                funpre
% 2.15/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.15/1.00  --abstr_ref_under                       []
% 2.15/1.00  
% 2.15/1.00  ------ SAT Options
% 2.15/1.00  
% 2.15/1.00  --sat_mode                              false
% 2.15/1.00  --sat_fm_restart_options                ""
% 2.15/1.00  --sat_gr_def                            false
% 2.15/1.00  --sat_epr_types                         true
% 2.15/1.00  --sat_non_cyclic_types                  false
% 2.15/1.00  --sat_finite_models                     false
% 2.15/1.00  --sat_fm_lemmas                         false
% 2.15/1.00  --sat_fm_prep                           false
% 2.15/1.00  --sat_fm_uc_incr                        true
% 2.15/1.00  --sat_out_model                         small
% 2.15/1.00  --sat_out_clauses                       false
% 2.15/1.00  
% 2.15/1.00  ------ QBF Options
% 2.15/1.00  
% 2.15/1.00  --qbf_mode                              false
% 2.15/1.00  --qbf_elim_univ                         false
% 2.15/1.00  --qbf_dom_inst                          none
% 2.15/1.00  --qbf_dom_pre_inst                      false
% 2.15/1.00  --qbf_sk_in                             false
% 2.15/1.00  --qbf_pred_elim                         true
% 2.15/1.00  --qbf_split                             512
% 2.15/1.00  
% 2.15/1.00  ------ BMC1 Options
% 2.15/1.00  
% 2.15/1.00  --bmc1_incremental                      false
% 2.15/1.00  --bmc1_axioms                           reachable_all
% 2.15/1.00  --bmc1_min_bound                        0
% 2.15/1.00  --bmc1_max_bound                        -1
% 2.15/1.00  --bmc1_max_bound_default                -1
% 2.15/1.00  --bmc1_symbol_reachability              true
% 2.15/1.00  --bmc1_property_lemmas                  false
% 2.15/1.00  --bmc1_k_induction                      false
% 2.15/1.00  --bmc1_non_equiv_states                 false
% 2.15/1.00  --bmc1_deadlock                         false
% 2.15/1.00  --bmc1_ucm                              false
% 2.15/1.00  --bmc1_add_unsat_core                   none
% 2.15/1.00  --bmc1_unsat_core_children              false
% 2.15/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.15/1.00  --bmc1_out_stat                         full
% 2.15/1.00  --bmc1_ground_init                      false
% 2.15/1.00  --bmc1_pre_inst_next_state              false
% 2.15/1.00  --bmc1_pre_inst_state                   false
% 2.15/1.00  --bmc1_pre_inst_reach_state             false
% 2.15/1.00  --bmc1_out_unsat_core                   false
% 2.15/1.00  --bmc1_aig_witness_out                  false
% 2.15/1.00  --bmc1_verbose                          false
% 2.15/1.00  --bmc1_dump_clauses_tptp                false
% 2.15/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.15/1.00  --bmc1_dump_file                        -
% 2.15/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.15/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.15/1.00  --bmc1_ucm_extend_mode                  1
% 2.15/1.00  --bmc1_ucm_init_mode                    2
% 2.15/1.00  --bmc1_ucm_cone_mode                    none
% 2.15/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.15/1.00  --bmc1_ucm_relax_model                  4
% 2.15/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.15/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.15/1.00  --bmc1_ucm_layered_model                none
% 2.15/1.00  --bmc1_ucm_max_lemma_size               10
% 2.15/1.00  
% 2.15/1.00  ------ AIG Options
% 2.15/1.00  
% 2.15/1.00  --aig_mode                              false
% 2.15/1.00  
% 2.15/1.00  ------ Instantiation Options
% 2.15/1.00  
% 2.15/1.00  --instantiation_flag                    true
% 2.15/1.00  --inst_sos_flag                         false
% 2.15/1.00  --inst_sos_phase                        true
% 2.15/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.15/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.15/1.00  --inst_lit_sel_side                     num_symb
% 2.15/1.00  --inst_solver_per_active                1400
% 2.15/1.00  --inst_solver_calls_frac                1.
% 2.15/1.00  --inst_passive_queue_type               priority_queues
% 2.15/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.15/1.00  --inst_passive_queues_freq              [25;2]
% 2.15/1.00  --inst_dismatching                      true
% 2.15/1.00  --inst_eager_unprocessed_to_passive     true
% 2.15/1.00  --inst_prop_sim_given                   true
% 2.15/1.00  --inst_prop_sim_new                     false
% 2.15/1.00  --inst_subs_new                         false
% 2.15/1.00  --inst_eq_res_simp                      false
% 2.15/1.00  --inst_subs_given                       false
% 2.15/1.00  --inst_orphan_elimination               true
% 2.15/1.00  --inst_learning_loop_flag               true
% 2.15/1.00  --inst_learning_start                   3000
% 2.15/1.00  --inst_learning_factor                  2
% 2.15/1.00  --inst_start_prop_sim_after_learn       3
% 2.15/1.00  --inst_sel_renew                        solver
% 2.15/1.00  --inst_lit_activity_flag                true
% 2.15/1.00  --inst_restr_to_given                   false
% 2.15/1.00  --inst_activity_threshold               500
% 2.15/1.00  --inst_out_proof                        true
% 2.15/1.00  
% 2.15/1.00  ------ Resolution Options
% 2.15/1.00  
% 2.15/1.00  --resolution_flag                       true
% 2.15/1.00  --res_lit_sel                           adaptive
% 2.15/1.00  --res_lit_sel_side                      none
% 2.15/1.00  --res_ordering                          kbo
% 2.15/1.00  --res_to_prop_solver                    active
% 2.15/1.00  --res_prop_simpl_new                    false
% 2.15/1.00  --res_prop_simpl_given                  true
% 2.15/1.00  --res_passive_queue_type                priority_queues
% 2.15/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.15/1.00  --res_passive_queues_freq               [15;5]
% 2.15/1.00  --res_forward_subs                      full
% 2.15/1.00  --res_backward_subs                     full
% 2.15/1.00  --res_forward_subs_resolution           true
% 2.15/1.00  --res_backward_subs_resolution          true
% 2.15/1.00  --res_orphan_elimination                true
% 2.15/1.00  --res_time_limit                        2.
% 2.15/1.00  --res_out_proof                         true
% 2.15/1.00  
% 2.15/1.00  ------ Superposition Options
% 2.15/1.00  
% 2.15/1.00  --superposition_flag                    true
% 2.15/1.00  --sup_passive_queue_type                priority_queues
% 2.15/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.15/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.15/1.00  --demod_completeness_check              fast
% 2.15/1.00  --demod_use_ground                      true
% 2.15/1.00  --sup_to_prop_solver                    passive
% 2.15/1.00  --sup_prop_simpl_new                    true
% 2.15/1.00  --sup_prop_simpl_given                  true
% 2.15/1.00  --sup_fun_splitting                     false
% 2.15/1.00  --sup_smt_interval                      50000
% 2.15/1.00  
% 2.15/1.00  ------ Superposition Simplification Setup
% 2.15/1.00  
% 2.15/1.00  --sup_indices_passive                   []
% 2.15/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.15/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_full_bw                           [BwDemod]
% 2.15/1.00  --sup_immed_triv                        [TrivRules]
% 2.15/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_immed_bw_main                     []
% 2.15/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.15/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.15/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.15/1.00  
% 2.15/1.00  ------ Combination Options
% 2.15/1.00  
% 2.15/1.00  --comb_res_mult                         3
% 2.15/1.00  --comb_sup_mult                         2
% 2.15/1.00  --comb_inst_mult                        10
% 2.15/1.00  
% 2.15/1.00  ------ Debug Options
% 2.15/1.00  
% 2.15/1.00  --dbg_backtrace                         false
% 2.15/1.00  --dbg_dump_prop_clauses                 false
% 2.15/1.00  --dbg_dump_prop_clauses_file            -
% 2.15/1.00  --dbg_out_stat                          false
% 2.15/1.00  ------ Parsing...
% 2.15/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.15/1.00  ------ Proving...
% 2.15/1.00  ------ Problem Properties 
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  clauses                                 9
% 2.15/1.00  conjectures                             1
% 2.15/1.00  EPR                                     0
% 2.15/1.00  Horn                                    9
% 2.15/1.00  unary                                   9
% 2.15/1.00  binary                                  0
% 2.15/1.00  lits                                    9
% 2.15/1.00  lits eq                                 9
% 2.15/1.00  fd_pure                                 0
% 2.15/1.00  fd_pseudo                               0
% 2.15/1.00  fd_cond                                 0
% 2.15/1.00  fd_pseudo_cond                          0
% 2.15/1.00  AC symbols                              0
% 2.15/1.00  
% 2.15/1.00  ------ Schedule UEQ
% 2.15/1.00  
% 2.15/1.00  ------ pure equality problem: resolution off 
% 2.15/1.00  
% 2.15/1.00  ------ Option_UEQ Time Limit: Unbounded
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  ------ 
% 2.15/1.00  Current options:
% 2.15/1.00  ------ 
% 2.15/1.00  
% 2.15/1.00  ------ Input Options
% 2.15/1.00  
% 2.15/1.00  --out_options                           all
% 2.15/1.00  --tptp_safe_out                         true
% 2.15/1.00  --problem_path                          ""
% 2.15/1.00  --include_path                          ""
% 2.15/1.00  --clausifier                            res/vclausify_rel
% 2.15/1.00  --clausifier_options                    --mode clausify
% 2.15/1.00  --stdin                                 false
% 2.15/1.00  --stats_out                             all
% 2.15/1.00  
% 2.15/1.00  ------ General Options
% 2.15/1.00  
% 2.15/1.00  --fof                                   false
% 2.15/1.00  --time_out_real                         305.
% 2.15/1.00  --time_out_virtual                      -1.
% 2.15/1.00  --symbol_type_check                     false
% 2.15/1.00  --clausify_out                          false
% 2.15/1.00  --sig_cnt_out                           false
% 2.15/1.00  --trig_cnt_out                          false
% 2.15/1.00  --trig_cnt_out_tolerance                1.
% 2.15/1.00  --trig_cnt_out_sk_spl                   false
% 2.15/1.00  --abstr_cl_out                          false
% 2.15/1.00  
% 2.15/1.00  ------ Global Options
% 2.15/1.00  
% 2.15/1.00  --schedule                              default
% 2.15/1.00  --add_important_lit                     false
% 2.15/1.00  --prop_solver_per_cl                    1000
% 2.15/1.00  --min_unsat_core                        false
% 2.15/1.00  --soft_assumptions                      false
% 2.15/1.00  --soft_lemma_size                       3
% 2.15/1.00  --prop_impl_unit_size                   0
% 2.15/1.00  --prop_impl_unit                        []
% 2.15/1.00  --share_sel_clauses                     true
% 2.15/1.00  --reset_solvers                         false
% 2.15/1.00  --bc_imp_inh                            [conj_cone]
% 2.15/1.00  --conj_cone_tolerance                   3.
% 2.15/1.00  --extra_neg_conj                        none
% 2.15/1.00  --large_theory_mode                     true
% 2.15/1.00  --prolific_symb_bound                   200
% 2.15/1.00  --lt_threshold                          2000
% 2.15/1.00  --clause_weak_htbl                      true
% 2.15/1.00  --gc_record_bc_elim                     false
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing Options
% 2.15/1.00  
% 2.15/1.00  --preprocessing_flag                    true
% 2.15/1.00  --time_out_prep_mult                    0.1
% 2.15/1.00  --splitting_mode                        input
% 2.15/1.00  --splitting_grd                         true
% 2.15/1.00  --splitting_cvd                         false
% 2.15/1.00  --splitting_cvd_svl                     false
% 2.15/1.00  --splitting_nvd                         32
% 2.15/1.00  --sub_typing                            true
% 2.15/1.00  --prep_gs_sim                           true
% 2.15/1.00  --prep_unflatten                        true
% 2.15/1.00  --prep_res_sim                          true
% 2.15/1.00  --prep_upred                            true
% 2.15/1.00  --prep_sem_filter                       exhaustive
% 2.15/1.00  --prep_sem_filter_out                   false
% 2.15/1.00  --pred_elim                             true
% 2.15/1.00  --res_sim_input                         true
% 2.15/1.00  --eq_ax_congr_red                       true
% 2.15/1.00  --pure_diseq_elim                       true
% 2.15/1.00  --brand_transform                       false
% 2.15/1.00  --non_eq_to_eq                          false
% 2.15/1.00  --prep_def_merge                        true
% 2.15/1.00  --prep_def_merge_prop_impl              false
% 2.15/1.00  --prep_def_merge_mbd                    true
% 2.15/1.00  --prep_def_merge_tr_red                 false
% 2.15/1.00  --prep_def_merge_tr_cl                  false
% 2.15/1.00  --smt_preprocessing                     true
% 2.15/1.00  --smt_ac_axioms                         fast
% 2.15/1.00  --preprocessed_out                      false
% 2.15/1.00  --preprocessed_stats                    false
% 2.15/1.00  
% 2.15/1.00  ------ Abstraction refinement Options
% 2.15/1.00  
% 2.15/1.00  --abstr_ref                             []
% 2.15/1.00  --abstr_ref_prep                        false
% 2.15/1.00  --abstr_ref_until_sat                   false
% 2.15/1.00  --abstr_ref_sig_restrict                funpre
% 2.15/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.15/1.00  --abstr_ref_under                       []
% 2.15/1.00  
% 2.15/1.00  ------ SAT Options
% 2.15/1.00  
% 2.15/1.00  --sat_mode                              false
% 2.15/1.00  --sat_fm_restart_options                ""
% 2.15/1.00  --sat_gr_def                            false
% 2.15/1.00  --sat_epr_types                         true
% 2.15/1.00  --sat_non_cyclic_types                  false
% 2.15/1.00  --sat_finite_models                     false
% 2.15/1.00  --sat_fm_lemmas                         false
% 2.15/1.00  --sat_fm_prep                           false
% 2.15/1.00  --sat_fm_uc_incr                        true
% 2.15/1.00  --sat_out_model                         small
% 2.15/1.00  --sat_out_clauses                       false
% 2.15/1.00  
% 2.15/1.00  ------ QBF Options
% 2.15/1.00  
% 2.15/1.00  --qbf_mode                              false
% 2.15/1.00  --qbf_elim_univ                         false
% 2.15/1.00  --qbf_dom_inst                          none
% 2.15/1.00  --qbf_dom_pre_inst                      false
% 2.15/1.00  --qbf_sk_in                             false
% 2.15/1.00  --qbf_pred_elim                         true
% 2.15/1.00  --qbf_split                             512
% 2.15/1.00  
% 2.15/1.00  ------ BMC1 Options
% 2.15/1.00  
% 2.15/1.00  --bmc1_incremental                      false
% 2.15/1.00  --bmc1_axioms                           reachable_all
% 2.15/1.00  --bmc1_min_bound                        0
% 2.15/1.00  --bmc1_max_bound                        -1
% 2.15/1.00  --bmc1_max_bound_default                -1
% 2.15/1.00  --bmc1_symbol_reachability              true
% 2.15/1.00  --bmc1_property_lemmas                  false
% 2.15/1.00  --bmc1_k_induction                      false
% 2.15/1.00  --bmc1_non_equiv_states                 false
% 2.15/1.00  --bmc1_deadlock                         false
% 2.15/1.00  --bmc1_ucm                              false
% 2.15/1.00  --bmc1_add_unsat_core                   none
% 2.15/1.00  --bmc1_unsat_core_children              false
% 2.15/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.15/1.00  --bmc1_out_stat                         full
% 2.15/1.00  --bmc1_ground_init                      false
% 2.15/1.00  --bmc1_pre_inst_next_state              false
% 2.15/1.00  --bmc1_pre_inst_state                   false
% 2.15/1.00  --bmc1_pre_inst_reach_state             false
% 2.15/1.00  --bmc1_out_unsat_core                   false
% 2.15/1.00  --bmc1_aig_witness_out                  false
% 2.15/1.00  --bmc1_verbose                          false
% 2.15/1.00  --bmc1_dump_clauses_tptp                false
% 2.15/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.15/1.00  --bmc1_dump_file                        -
% 2.15/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.15/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.15/1.00  --bmc1_ucm_extend_mode                  1
% 2.15/1.00  --bmc1_ucm_init_mode                    2
% 2.15/1.00  --bmc1_ucm_cone_mode                    none
% 2.15/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.15/1.00  --bmc1_ucm_relax_model                  4
% 2.15/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.15/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.15/1.00  --bmc1_ucm_layered_model                none
% 2.15/1.00  --bmc1_ucm_max_lemma_size               10
% 2.15/1.00  
% 2.15/1.00  ------ AIG Options
% 2.15/1.00  
% 2.15/1.00  --aig_mode                              false
% 2.15/1.00  
% 2.15/1.00  ------ Instantiation Options
% 2.15/1.00  
% 2.15/1.00  --instantiation_flag                    false
% 2.15/1.00  --inst_sos_flag                         false
% 2.15/1.00  --inst_sos_phase                        true
% 2.15/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.15/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.15/1.00  --inst_lit_sel_side                     num_symb
% 2.15/1.00  --inst_solver_per_active                1400
% 2.15/1.00  --inst_solver_calls_frac                1.
% 2.15/1.00  --inst_passive_queue_type               priority_queues
% 2.15/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.15/1.00  --inst_passive_queues_freq              [25;2]
% 2.15/1.00  --inst_dismatching                      true
% 2.15/1.00  --inst_eager_unprocessed_to_passive     true
% 2.15/1.00  --inst_prop_sim_given                   true
% 2.15/1.00  --inst_prop_sim_new                     false
% 2.15/1.00  --inst_subs_new                         false
% 2.15/1.00  --inst_eq_res_simp                      false
% 2.15/1.00  --inst_subs_given                       false
% 2.15/1.00  --inst_orphan_elimination               true
% 2.15/1.00  --inst_learning_loop_flag               true
% 2.15/1.00  --inst_learning_start                   3000
% 2.15/1.00  --inst_learning_factor                  2
% 2.15/1.00  --inst_start_prop_sim_after_learn       3
% 2.15/1.00  --inst_sel_renew                        solver
% 2.15/1.00  --inst_lit_activity_flag                true
% 2.15/1.00  --inst_restr_to_given                   false
% 2.15/1.00  --inst_activity_threshold               500
% 2.15/1.00  --inst_out_proof                        true
% 2.15/1.00  
% 2.15/1.00  ------ Resolution Options
% 2.15/1.00  
% 2.15/1.00  --resolution_flag                       false
% 2.15/1.00  --res_lit_sel                           adaptive
% 2.15/1.00  --res_lit_sel_side                      none
% 2.15/1.00  --res_ordering                          kbo
% 2.15/1.00  --res_to_prop_solver                    active
% 2.15/1.00  --res_prop_simpl_new                    false
% 2.15/1.00  --res_prop_simpl_given                  true
% 2.15/1.00  --res_passive_queue_type                priority_queues
% 2.15/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.15/1.00  --res_passive_queues_freq               [15;5]
% 2.15/1.00  --res_forward_subs                      full
% 2.15/1.00  --res_backward_subs                     full
% 2.15/1.00  --res_forward_subs_resolution           true
% 2.15/1.00  --res_backward_subs_resolution          true
% 2.15/1.00  --res_orphan_elimination                true
% 2.15/1.00  --res_time_limit                        2.
% 2.15/1.00  --res_out_proof                         true
% 2.15/1.00  
% 2.15/1.00  ------ Superposition Options
% 2.15/1.00  
% 2.15/1.00  --superposition_flag                    true
% 2.15/1.00  --sup_passive_queue_type                priority_queues
% 2.15/1.00  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.15/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.15/1.00  --demod_completeness_check              fast
% 2.15/1.00  --demod_use_ground                      true
% 2.15/1.00  --sup_to_prop_solver                    active
% 2.15/1.00  --sup_prop_simpl_new                    false
% 2.15/1.00  --sup_prop_simpl_given                  false
% 2.15/1.00  --sup_fun_splitting                     true
% 2.15/1.00  --sup_smt_interval                      10000
% 2.15/1.00  
% 2.15/1.00  ------ Superposition Simplification Setup
% 2.15/1.00  
% 2.15/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.15/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.15/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.15/1.00  --sup_full_triv                         [TrivRules]
% 2.15/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.15/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.15/1.00  --sup_immed_triv                        [TrivRules]
% 2.15/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/1.00  --sup_immed_bw_main                     []
% 2.15/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.15/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.15/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.15/1.00  --sup_input_bw                          [BwDemod;BwSubsumption]
% 2.15/1.00  
% 2.15/1.00  ------ Combination Options
% 2.15/1.00  
% 2.15/1.00  --comb_res_mult                         1
% 2.15/1.00  --comb_sup_mult                         1
% 2.15/1.00  --comb_inst_mult                        1000000
% 2.15/1.00  
% 2.15/1.00  ------ Debug Options
% 2.15/1.00  
% 2.15/1.00  --dbg_backtrace                         false
% 2.15/1.00  --dbg_dump_prop_clauses                 false
% 2.15/1.00  --dbg_dump_prop_clauses_file            -
% 2.15/1.00  --dbg_out_stat                          false
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  ------ Proving...
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  % SZS status Theorem for theBenchmark.p
% 2.15/1.00  
% 2.15/1.00   Resolution empty clause
% 2.15/1.00  
% 2.15/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.15/1.00  
% 2.15/1.00  fof(f8,axiom,(
% 2.15/1.00    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 2.15/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f23,plain,(
% 2.15/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f8])).
% 2.15/1.00  
% 2.15/1.00  fof(f2,axiom,(
% 2.15/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.15/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f17,plain,(
% 2.15/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f2])).
% 2.15/1.00  
% 2.15/1.00  fof(f11,conjecture,(
% 2.15/1.00    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 2.15/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f12,negated_conjecture,(
% 2.15/1.00    ~! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,X1)),
% 2.15/1.00    inference(negated_conjecture,[],[f11])).
% 2.15/1.00  
% 2.15/1.00  fof(f13,plain,(
% 2.15/1.00    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1)),
% 2.15/1.00    inference(ennf_transformation,[],[f12])).
% 2.15/1.00  
% 2.15/1.00  fof(f14,plain,(
% 2.15/1.00    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k5_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 2.15/1.00    introduced(choice_axiom,[])).
% 2.15/1.00  
% 2.15/1.00  fof(f15,plain,(
% 2.15/1.00    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 2.15/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 2.15/1.00  
% 2.15/1.00  fof(f26,plain,(
% 2.15/1.00    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k5_xboole_0(sK0,sK1)),
% 2.15/1.00    inference(cnf_transformation,[],[f15])).
% 2.15/1.00  
% 2.15/1.00  fof(f10,axiom,(
% 2.15/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.15/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f25,plain,(
% 2.15/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.15/1.00    inference(cnf_transformation,[],[f10])).
% 2.15/1.00  
% 2.15/1.00  fof(f3,axiom,(
% 2.15/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.15/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f18,plain,(
% 2.15/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.15/1.00    inference(cnf_transformation,[],[f3])).
% 2.15/1.00  
% 2.15/1.00  fof(f27,plain,(
% 2.15/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.15/1.00    inference(definition_unfolding,[],[f25,f18])).
% 2.15/1.00  
% 2.15/1.00  fof(f31,plain,(
% 2.15/1.00    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 2.15/1.00    inference(definition_unfolding,[],[f26,f18,f27])).
% 2.15/1.00  
% 2.15/1.00  fof(f6,axiom,(
% 2.15/1.00    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.15/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f21,plain,(
% 2.15/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.15/1.00    inference(cnf_transformation,[],[f6])).
% 2.15/1.00  
% 2.15/1.00  fof(f30,plain,(
% 2.15/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 2.15/1.00    inference(definition_unfolding,[],[f21,f18,f18])).
% 2.15/1.00  
% 2.15/1.00  fof(f5,axiom,(
% 2.15/1.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 2.15/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f20,plain,(
% 2.15/1.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.15/1.00    inference(cnf_transformation,[],[f5])).
% 2.15/1.00  
% 2.15/1.00  fof(f7,axiom,(
% 2.15/1.00    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.15/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f22,plain,(
% 2.15/1.00    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.15/1.00    inference(cnf_transformation,[],[f7])).
% 2.15/1.00  
% 2.15/1.00  fof(f9,axiom,(
% 2.15/1.00    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 2.15/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f24,plain,(
% 2.15/1.00    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 2.15/1.00    inference(cnf_transformation,[],[f9])).
% 2.15/1.00  
% 2.15/1.00  fof(f4,axiom,(
% 2.15/1.00    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 2.15/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.15/1.00  
% 2.15/1.00  fof(f19,plain,(
% 2.15/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 2.15/1.00    inference(cnf_transformation,[],[f4])).
% 2.15/1.00  
% 2.15/1.00  fof(f29,plain,(
% 2.15/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) )),
% 2.15/1.00    inference(definition_unfolding,[],[f19,f27])).
% 2.15/1.00  
% 2.15/1.00  cnf(c_6,plain,
% 2.15/1.00      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 2.15/1.00      inference(cnf_transformation,[],[f23]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_1,plain,
% 2.15/1.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.15/1.00      inference(cnf_transformation,[],[f17]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_8,negated_conjecture,
% 2.15/1.00      ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
% 2.15/1.00      inference(cnf_transformation,[],[f31]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_27,plain,
% 2.15/1.00      ( k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))) != k5_xboole_0(sK0,sK1) ),
% 2.15/1.00      inference(demodulation,[status(thm)],[c_1,c_8]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_32,plain,
% 2.15/1.00      ( k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) != k5_xboole_0(sK0,sK1) ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_1,c_27]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_68,plain,
% 2.15/1.00      ( k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) != k5_xboole_0(sK0,sK1) ),
% 2.15/1.00      inference(demodulation,[status(thm)],[c_6,c_32]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_132,plain,
% 2.15/1.00      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))) != k5_xboole_0(sK0,sK1) ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_6,c_68]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_4,plain,
% 2.15/1.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 2.15/1.00      inference(cnf_transformation,[],[f30]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_97,plain,
% 2.15/1.00      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_133,plain,
% 2.15/1.00      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) != k5_xboole_0(sK0,sK1) ),
% 2.15/1.00      inference(demodulation,[status(thm)],[c_132,c_97]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_3,plain,
% 2.15/1.00      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.15/1.00      inference(cnf_transformation,[],[f20]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_5,plain,
% 2.15/1.00      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.15/1.00      inference(cnf_transformation,[],[f22]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_7,plain,
% 2.15/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.15/1.00      inference(cnf_transformation,[],[f24]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_2,plain,
% 2.15/1.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 2.15/1.00      inference(cnf_transformation,[],[f29]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_53,plain,
% 2.15/1.00      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 2.15/1.00      inference(superposition,[status(thm)],[c_1,c_2]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_134,plain,
% 2.15/1.00      ( k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
% 2.15/1.00      inference(demodulation,[status(thm)],[c_133,c_3,c_5,c_7,c_53]) ).
% 2.15/1.00  
% 2.15/1.00  cnf(c_135,plain,
% 2.15/1.00      ( $false ),
% 2.15/1.00      inference(equality_resolution_simp,[status(thm)],[c_134]) ).
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.15/1.00  
% 2.15/1.00  ------                               Statistics
% 2.15/1.00  
% 2.15/1.00  ------ General
% 2.15/1.00  
% 2.15/1.00  abstr_ref_over_cycles:                  0
% 2.15/1.00  abstr_ref_under_cycles:                 0
% 2.15/1.00  gc_basic_clause_elim:                   0
% 2.15/1.00  forced_gc_time:                         0
% 2.15/1.00  parsing_time:                           0.01
% 2.15/1.00  unif_index_cands_time:                  0.
% 2.15/1.00  unif_index_add_time:                    0.
% 2.15/1.00  orderings_time:                         0.
% 2.15/1.00  out_proof_time:                         0.005
% 2.15/1.00  total_time:                             0.038
% 2.15/1.00  num_of_symbols:                         36
% 2.15/1.00  num_of_terms:                           394
% 2.15/1.00  
% 2.15/1.00  ------ Preprocessing
% 2.15/1.00  
% 2.15/1.00  num_of_splits:                          0
% 2.15/1.00  num_of_split_atoms:                     0
% 2.15/1.00  num_of_reused_defs:                     0
% 2.15/1.00  num_eq_ax_congr_red:                    0
% 2.15/1.00  num_of_sem_filtered_clauses:            0
% 2.15/1.00  num_of_subtypes:                        0
% 2.15/1.00  monotx_restored_types:                  0
% 2.15/1.00  sat_num_of_epr_types:                   0
% 2.15/1.00  sat_num_of_non_cyclic_types:            0
% 2.15/1.00  sat_guarded_non_collapsed_types:        0
% 2.15/1.00  num_pure_diseq_elim:                    0
% 2.15/1.00  simp_replaced_by:                       0
% 2.15/1.00  res_preprocessed:                       22
% 2.15/1.00  prep_upred:                             0
% 2.15/1.00  prep_unflattend:                        0
% 2.15/1.00  smt_new_axioms:                         0
% 2.15/1.00  pred_elim_cands:                        0
% 2.15/1.00  pred_elim:                              0
% 2.15/1.00  pred_elim_cl:                           0
% 2.15/1.00  pred_elim_cycles:                       0
% 2.15/1.00  merged_defs:                            0
% 2.15/1.00  merged_defs_ncl:                        0
% 2.15/1.00  bin_hyper_res:                          0
% 2.15/1.00  prep_cycles:                            2
% 2.15/1.00  pred_elim_time:                         0.
% 2.15/1.00  splitting_time:                         0.
% 2.15/1.00  sem_filter_time:                        0.
% 2.15/1.00  monotx_time:                            0.
% 2.15/1.00  subtype_inf_time:                       0.
% 2.15/1.00  
% 2.15/1.00  ------ Problem properties
% 2.15/1.00  
% 2.15/1.00  clauses:                                9
% 2.15/1.00  conjectures:                            1
% 2.15/1.00  epr:                                    0
% 2.15/1.00  horn:                                   9
% 2.15/1.00  ground:                                 1
% 2.15/1.00  unary:                                  9
% 2.15/1.00  binary:                                 0
% 2.15/1.00  lits:                                   9
% 2.15/1.00  lits_eq:                                9
% 2.15/1.00  fd_pure:                                0
% 2.15/1.00  fd_pseudo:                              0
% 2.15/1.00  fd_cond:                                0
% 2.15/1.00  fd_pseudo_cond:                         0
% 2.15/1.00  ac_symbols:                             0
% 2.15/1.00  
% 2.15/1.00  ------ Propositional Solver
% 2.15/1.00  
% 2.15/1.00  prop_solver_calls:                      13
% 2.15/1.00  prop_fast_solver_calls:                 56
% 2.15/1.00  smt_solver_calls:                       0
% 2.15/1.00  smt_fast_solver_calls:                  0
% 2.15/1.00  prop_num_of_clauses:                    31
% 2.15/1.00  prop_preprocess_simplified:             305
% 2.15/1.00  prop_fo_subsumed:                       0
% 2.15/1.00  prop_solver_time:                       0.
% 2.15/1.00  smt_solver_time:                        0.
% 2.15/1.00  smt_fast_solver_time:                   0.
% 2.15/1.00  prop_fast_solver_time:                  0.
% 2.15/1.00  prop_unsat_core_time:                   0.
% 2.15/1.00  
% 2.15/1.00  ------ QBF
% 2.15/1.00  
% 2.15/1.00  qbf_q_res:                              0
% 2.15/1.00  qbf_num_tautologies:                    0
% 2.15/1.00  qbf_prep_cycles:                        0
% 2.15/1.00  
% 2.15/1.00  ------ BMC1
% 2.15/1.00  
% 2.15/1.00  bmc1_current_bound:                     -1
% 2.15/1.00  bmc1_last_solved_bound:                 -1
% 2.15/1.00  bmc1_unsat_core_size:                   -1
% 2.15/1.00  bmc1_unsat_core_parents_size:           -1
% 2.15/1.00  bmc1_merge_next_fun:                    0
% 2.15/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.15/1.00  
% 2.15/1.00  ------ Instantiation
% 2.15/1.00  
% 2.15/1.00  inst_num_of_clauses:                    0
% 2.15/1.00  inst_num_in_passive:                    0
% 2.15/1.00  inst_num_in_active:                     0
% 2.15/1.00  inst_num_in_unprocessed:                0
% 2.15/1.00  inst_num_of_loops:                      0
% 2.15/1.00  inst_num_of_learning_restarts:          0
% 2.15/1.00  inst_num_moves_active_passive:          0
% 2.15/1.00  inst_lit_activity:                      0
% 2.15/1.00  inst_lit_activity_moves:                0
% 2.15/1.00  inst_num_tautologies:                   0
% 2.15/1.00  inst_num_prop_implied:                  0
% 2.15/1.00  inst_num_existing_simplified:           0
% 2.15/1.00  inst_num_eq_res_simplified:             0
% 2.15/1.00  inst_num_child_elim:                    0
% 2.15/1.00  inst_num_of_dismatching_blockings:      0
% 2.15/1.00  inst_num_of_non_proper_insts:           0
% 2.15/1.00  inst_num_of_duplicates:                 0
% 2.15/1.00  inst_inst_num_from_inst_to_res:         0
% 2.15/1.00  inst_dismatching_checking_time:         0.
% 2.15/1.00  
% 2.15/1.00  ------ Resolution
% 2.15/1.00  
% 2.15/1.00  res_num_of_clauses:                     0
% 2.15/1.00  res_num_in_passive:                     0
% 2.15/1.00  res_num_in_active:                      0
% 2.15/1.00  res_num_of_loops:                       24
% 2.15/1.00  res_forward_subset_subsumed:            0
% 2.15/1.00  res_backward_subset_subsumed:           0
% 2.15/1.00  res_forward_subsumed:                   0
% 2.15/1.00  res_backward_subsumed:                  0
% 2.15/1.00  res_forward_subsumption_resolution:     0
% 2.15/1.00  res_backward_subsumption_resolution:    0
% 2.15/1.00  res_clause_to_clause_subsumption:       113
% 2.15/1.00  res_orphan_elimination:                 0
% 2.15/1.00  res_tautology_del:                      0
% 2.15/1.00  res_num_eq_res_simplified:              0
% 2.15/1.00  res_num_sel_changes:                    0
% 2.15/1.00  res_moves_from_active_to_pass:          0
% 2.15/1.00  
% 2.15/1.00  ------ Superposition
% 2.15/1.00  
% 2.15/1.00  sup_time_total:                         0.
% 2.15/1.00  sup_time_generating:                    0.
% 2.15/1.00  sup_time_sim_full:                      0.
% 2.15/1.00  sup_time_sim_immed:                     0.
% 2.15/1.00  
% 2.15/1.00  sup_num_of_clauses:                     32
% 2.15/1.00  sup_num_in_active:                      12
% 2.15/1.00  sup_num_in_passive:                     20
% 2.15/1.00  sup_num_of_loops:                       14
% 2.15/1.00  sup_fw_superposition:                   49
% 2.15/1.00  sup_bw_superposition:                   26
% 2.15/1.00  sup_immediate_simplified:               24
% 2.15/1.00  sup_given_eliminated:                   0
% 2.15/1.00  comparisons_done:                       0
% 2.15/1.00  comparisons_avoided:                    0
% 2.15/1.00  
% 2.15/1.00  ------ Simplifications
% 2.15/1.00  
% 2.15/1.00  
% 2.15/1.00  sim_fw_subset_subsumed:                 0
% 2.15/1.00  sim_bw_subset_subsumed:                 0
% 2.15/1.00  sim_fw_subsumed:                        1
% 2.15/1.00  sim_bw_subsumed:                        1
% 2.15/1.00  sim_fw_subsumption_res:                 0
% 2.15/1.00  sim_bw_subsumption_res:                 0
% 2.15/1.00  sim_tautology_del:                      0
% 2.15/1.00  sim_eq_tautology_del:                   11
% 2.15/1.00  sim_eq_res_simp:                        0
% 2.15/1.00  sim_fw_demodulated:                     19
% 2.15/1.00  sim_bw_demodulated:                     3
% 2.15/1.00  sim_light_normalised:                   9
% 2.15/1.00  sim_joinable_taut:                      0
% 2.15/1.00  sim_joinable_simp:                      0
% 2.15/1.00  sim_ac_normalised:                      0
% 2.15/1.00  sim_smt_subsumption:                    0
% 2.15/1.00  
%------------------------------------------------------------------------------
