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
% DateTime   : Thu Dec  3 11:27:49 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 108 expanded)
%              Number of clauses        :   10 (  12 expanded)
%              Number of leaves         :   10 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :   40 ( 109 expanded)
%              Number of equality atoms :   39 ( 108 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f18,f19])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f17,f23])).

fof(f25,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f16,f24])).

fof(f28,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X0,X2) ),
    inference(definition_unfolding,[],[f21,f25,f25])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X6,X7),k5_enumset1(X0,X0,X0,X1,X2,X3,X4))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) ),
    inference(definition_unfolding,[],[f15,f14,f23,f25])).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k4_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X1,X2,X3))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(definition_unfolding,[],[f20,f26])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3) ),
    inference(ennf_transformation,[],[f10])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3)
   => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f12])).

fof(f22,plain,(
    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) ),
    inference(definition_unfolding,[],[f22,f24,f24])).

cnf(c_1,plain,
    ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X0,X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_11,plain,
    ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) = k5_enumset1(X1_36,X1_36,X1_36,X1_36,X1_36,X0_36,X2_36) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k4_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X1,X2,X3))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_12,plain,
    ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36),k4_xboole_0(k5_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36,X5_36,X6_36),k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36))) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36,X6_36) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_26,plain,
    ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36),k4_xboole_0(k5_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36,X5_36,X6_36),k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36))) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X5_36,X4_36,X6_36) ),
    inference(superposition,[status(thm)],[c_11,c_12])).

cnf(c_37,plain,
    ( k5_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36,X6_36) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X5_36,X4_36,X6_36) ),
    inference(superposition,[status(thm)],[c_26,c_12])).

cnf(c_2,negated_conjecture,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_10,negated_conjecture,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_38,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
    inference(demodulation,[status(thm)],[c_37,c_10])).

cnf(c_59,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.37/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.37/1.05  
% 0.37/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.37/1.05  
% 0.37/1.05  ------  iProver source info
% 0.37/1.05  
% 0.37/1.05  git: date: 2020-06-30 10:37:57 +0100
% 0.37/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.37/1.05  git: non_committed_changes: false
% 0.37/1.05  git: last_make_outside_of_git: false
% 0.37/1.05  
% 0.37/1.05  ------ 
% 0.37/1.05  
% 0.37/1.05  ------ Input Options
% 0.37/1.05  
% 0.37/1.05  --out_options                           all
% 0.37/1.05  --tptp_safe_out                         true
% 0.37/1.05  --problem_path                          ""
% 0.37/1.05  --include_path                          ""
% 0.37/1.05  --clausifier                            res/vclausify_rel
% 0.37/1.05  --clausifier_options                    --mode clausify
% 0.37/1.05  --stdin                                 false
% 0.37/1.05  --stats_out                             all
% 0.37/1.05  
% 0.37/1.05  ------ General Options
% 0.37/1.05  
% 0.37/1.05  --fof                                   false
% 0.37/1.05  --time_out_real                         305.
% 0.37/1.05  --time_out_virtual                      -1.
% 0.37/1.05  --symbol_type_check                     false
% 0.37/1.05  --clausify_out                          false
% 0.37/1.05  --sig_cnt_out                           false
% 0.37/1.05  --trig_cnt_out                          false
% 0.37/1.05  --trig_cnt_out_tolerance                1.
% 0.37/1.05  --trig_cnt_out_sk_spl                   false
% 0.37/1.05  --abstr_cl_out                          false
% 0.37/1.05  
% 0.37/1.05  ------ Global Options
% 0.37/1.05  
% 0.37/1.05  --schedule                              default
% 0.37/1.05  --add_important_lit                     false
% 0.37/1.05  --prop_solver_per_cl                    1000
% 0.37/1.05  --min_unsat_core                        false
% 0.37/1.05  --soft_assumptions                      false
% 0.37/1.05  --soft_lemma_size                       3
% 0.37/1.05  --prop_impl_unit_size                   0
% 0.37/1.05  --prop_impl_unit                        []
% 0.37/1.05  --share_sel_clauses                     true
% 0.37/1.05  --reset_solvers                         false
% 0.37/1.05  --bc_imp_inh                            [conj_cone]
% 0.37/1.05  --conj_cone_tolerance                   3.
% 0.37/1.05  --extra_neg_conj                        none
% 0.37/1.05  --large_theory_mode                     true
% 0.37/1.05  --prolific_symb_bound                   200
% 0.37/1.05  --lt_threshold                          2000
% 0.37/1.05  --clause_weak_htbl                      true
% 0.37/1.05  --gc_record_bc_elim                     false
% 0.37/1.05  
% 0.37/1.05  ------ Preprocessing Options
% 0.37/1.05  
% 0.37/1.05  --preprocessing_flag                    true
% 0.37/1.05  --time_out_prep_mult                    0.1
% 0.37/1.05  --splitting_mode                        input
% 0.37/1.05  --splitting_grd                         true
% 0.37/1.05  --splitting_cvd                         false
% 0.37/1.05  --splitting_cvd_svl                     false
% 0.37/1.05  --splitting_nvd                         32
% 0.37/1.05  --sub_typing                            true
% 0.37/1.05  --prep_gs_sim                           true
% 0.37/1.05  --prep_unflatten                        true
% 0.37/1.05  --prep_res_sim                          true
% 0.37/1.05  --prep_upred                            true
% 0.37/1.05  --prep_sem_filter                       exhaustive
% 0.37/1.05  --prep_sem_filter_out                   false
% 0.37/1.05  --pred_elim                             true
% 0.37/1.05  --res_sim_input                         true
% 0.37/1.05  --eq_ax_congr_red                       true
% 0.37/1.05  --pure_diseq_elim                       true
% 0.37/1.05  --brand_transform                       false
% 0.37/1.05  --non_eq_to_eq                          false
% 0.37/1.05  --prep_def_merge                        true
% 0.37/1.05  --prep_def_merge_prop_impl              false
% 0.37/1.05  --prep_def_merge_mbd                    true
% 0.37/1.05  --prep_def_merge_tr_red                 false
% 0.37/1.05  --prep_def_merge_tr_cl                  false
% 0.37/1.05  --smt_preprocessing                     true
% 0.37/1.05  --smt_ac_axioms                         fast
% 0.37/1.05  --preprocessed_out                      false
% 0.37/1.05  --preprocessed_stats                    false
% 0.37/1.05  
% 0.37/1.05  ------ Abstraction refinement Options
% 0.37/1.05  
% 0.37/1.05  --abstr_ref                             []
% 0.37/1.05  --abstr_ref_prep                        false
% 0.37/1.05  --abstr_ref_until_sat                   false
% 0.37/1.05  --abstr_ref_sig_restrict                funpre
% 0.37/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.37/1.05  --abstr_ref_under                       []
% 0.37/1.05  
% 0.37/1.05  ------ SAT Options
% 0.37/1.05  
% 0.37/1.05  --sat_mode                              false
% 0.37/1.05  --sat_fm_restart_options                ""
% 0.37/1.05  --sat_gr_def                            false
% 0.37/1.05  --sat_epr_types                         true
% 0.37/1.05  --sat_non_cyclic_types                  false
% 0.37/1.05  --sat_finite_models                     false
% 0.37/1.05  --sat_fm_lemmas                         false
% 0.37/1.05  --sat_fm_prep                           false
% 0.37/1.05  --sat_fm_uc_incr                        true
% 0.37/1.05  --sat_out_model                         small
% 0.37/1.05  --sat_out_clauses                       false
% 0.37/1.05  
% 0.37/1.05  ------ QBF Options
% 0.37/1.05  
% 0.37/1.05  --qbf_mode                              false
% 0.37/1.05  --qbf_elim_univ                         false
% 0.37/1.05  --qbf_dom_inst                          none
% 0.37/1.05  --qbf_dom_pre_inst                      false
% 0.37/1.05  --qbf_sk_in                             false
% 0.37/1.05  --qbf_pred_elim                         true
% 0.37/1.05  --qbf_split                             512
% 0.37/1.05  
% 0.37/1.05  ------ BMC1 Options
% 0.37/1.05  
% 0.37/1.05  --bmc1_incremental                      false
% 0.37/1.05  --bmc1_axioms                           reachable_all
% 0.37/1.05  --bmc1_min_bound                        0
% 0.37/1.05  --bmc1_max_bound                        -1
% 0.37/1.05  --bmc1_max_bound_default                -1
% 0.37/1.05  --bmc1_symbol_reachability              true
% 0.37/1.05  --bmc1_property_lemmas                  false
% 0.37/1.05  --bmc1_k_induction                      false
% 0.37/1.05  --bmc1_non_equiv_states                 false
% 0.37/1.05  --bmc1_deadlock                         false
% 0.37/1.05  --bmc1_ucm                              false
% 0.37/1.05  --bmc1_add_unsat_core                   none
% 0.37/1.05  --bmc1_unsat_core_children              false
% 0.37/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 0.37/1.05  --bmc1_out_stat                         full
% 0.37/1.05  --bmc1_ground_init                      false
% 0.37/1.05  --bmc1_pre_inst_next_state              false
% 0.37/1.05  --bmc1_pre_inst_state                   false
% 0.37/1.05  --bmc1_pre_inst_reach_state             false
% 0.37/1.05  --bmc1_out_unsat_core                   false
% 0.37/1.05  --bmc1_aig_witness_out                  false
% 0.37/1.05  --bmc1_verbose                          false
% 0.37/1.05  --bmc1_dump_clauses_tptp                false
% 0.37/1.05  --bmc1_dump_unsat_core_tptp             false
% 0.37/1.05  --bmc1_dump_file                        -
% 0.37/1.05  --bmc1_ucm_expand_uc_limit              128
% 0.37/1.05  --bmc1_ucm_n_expand_iterations          6
% 0.37/1.05  --bmc1_ucm_extend_mode                  1
% 0.37/1.05  --bmc1_ucm_init_mode                    2
% 0.37/1.05  --bmc1_ucm_cone_mode                    none
% 0.37/1.05  --bmc1_ucm_reduced_relation_type        0
% 0.37/1.05  --bmc1_ucm_relax_model                  4
% 0.37/1.05  --bmc1_ucm_full_tr_after_sat            true
% 0.37/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 0.37/1.05  --bmc1_ucm_layered_model                none
% 0.37/1.05  --bmc1_ucm_max_lemma_size               10
% 0.37/1.05  
% 0.37/1.05  ------ AIG Options
% 0.37/1.05  
% 0.37/1.05  --aig_mode                              false
% 0.37/1.05  
% 0.37/1.05  ------ Instantiation Options
% 0.37/1.05  
% 0.37/1.05  --instantiation_flag                    true
% 0.37/1.05  --inst_sos_flag                         false
% 0.37/1.05  --inst_sos_phase                        true
% 0.37/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.37/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.37/1.05  --inst_lit_sel_side                     num_symb
% 0.37/1.05  --inst_solver_per_active                1400
% 0.37/1.05  --inst_solver_calls_frac                1.
% 0.37/1.05  --inst_passive_queue_type               priority_queues
% 0.37/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.37/1.05  --inst_passive_queues_freq              [25;2]
% 0.37/1.05  --inst_dismatching                      true
% 0.37/1.05  --inst_eager_unprocessed_to_passive     true
% 0.37/1.05  --inst_prop_sim_given                   true
% 0.37/1.05  --inst_prop_sim_new                     false
% 0.37/1.05  --inst_subs_new                         false
% 0.37/1.05  --inst_eq_res_simp                      false
% 0.37/1.05  --inst_subs_given                       false
% 0.37/1.05  --inst_orphan_elimination               true
% 0.37/1.05  --inst_learning_loop_flag               true
% 0.37/1.05  --inst_learning_start                   3000
% 0.37/1.05  --inst_learning_factor                  2
% 0.37/1.05  --inst_start_prop_sim_after_learn       3
% 0.37/1.05  --inst_sel_renew                        solver
% 0.37/1.05  --inst_lit_activity_flag                true
% 0.37/1.05  --inst_restr_to_given                   false
% 0.37/1.05  --inst_activity_threshold               500
% 0.37/1.05  --inst_out_proof                        true
% 0.37/1.05  
% 0.37/1.05  ------ Resolution Options
% 0.37/1.05  
% 0.37/1.05  --resolution_flag                       true
% 0.37/1.05  --res_lit_sel                           adaptive
% 0.37/1.05  --res_lit_sel_side                      none
% 0.37/1.05  --res_ordering                          kbo
% 0.37/1.05  --res_to_prop_solver                    active
% 0.37/1.05  --res_prop_simpl_new                    false
% 0.37/1.05  --res_prop_simpl_given                  true
% 0.37/1.05  --res_passive_queue_type                priority_queues
% 0.37/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.37/1.05  --res_passive_queues_freq               [15;5]
% 0.37/1.05  --res_forward_subs                      full
% 0.37/1.05  --res_backward_subs                     full
% 0.37/1.05  --res_forward_subs_resolution           true
% 0.37/1.05  --res_backward_subs_resolution          true
% 0.37/1.05  --res_orphan_elimination                true
% 0.37/1.05  --res_time_limit                        2.
% 0.37/1.05  --res_out_proof                         true
% 0.37/1.05  
% 0.37/1.05  ------ Superposition Options
% 0.37/1.05  
% 0.37/1.05  --superposition_flag                    true
% 0.37/1.05  --sup_passive_queue_type                priority_queues
% 0.37/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.37/1.05  --sup_passive_queues_freq               [8;1;4]
% 0.37/1.05  --demod_completeness_check              fast
% 0.37/1.05  --demod_use_ground                      true
% 0.37/1.05  --sup_to_prop_solver                    passive
% 0.37/1.05  --sup_prop_simpl_new                    true
% 0.37/1.05  --sup_prop_simpl_given                  true
% 0.37/1.05  --sup_fun_splitting                     false
% 0.37/1.05  --sup_smt_interval                      50000
% 0.37/1.05  
% 0.37/1.05  ------ Superposition Simplification Setup
% 0.37/1.05  
% 0.37/1.05  --sup_indices_passive                   []
% 0.37/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 0.37/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.05  --sup_full_bw                           [BwDemod]
% 0.37/1.05  --sup_immed_triv                        [TrivRules]
% 0.37/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.37/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.05  --sup_immed_bw_main                     []
% 0.37/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.37/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 0.37/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.37/1.05  
% 0.37/1.05  ------ Combination Options
% 0.37/1.05  
% 0.37/1.05  --comb_res_mult                         3
% 0.37/1.05  --comb_sup_mult                         2
% 0.37/1.05  --comb_inst_mult                        10
% 0.37/1.05  
% 0.37/1.05  ------ Debug Options
% 0.37/1.05  
% 0.37/1.05  --dbg_backtrace                         false
% 0.37/1.05  --dbg_dump_prop_clauses                 false
% 0.37/1.05  --dbg_dump_prop_clauses_file            -
% 0.37/1.05  --dbg_out_stat                          false
% 0.37/1.05  ------ Parsing...
% 0.37/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.37/1.05  
% 0.37/1.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 0.37/1.05  
% 0.37/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.37/1.05  
% 0.37/1.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.37/1.05  ------ Proving...
% 0.37/1.05  ------ Problem Properties 
% 0.37/1.05  
% 0.37/1.05  
% 0.37/1.05  clauses                                 3
% 0.37/1.05  conjectures                             1
% 0.37/1.05  EPR                                     0
% 0.37/1.05  Horn                                    3
% 0.37/1.05  unary                                   3
% 0.37/1.05  binary                                  0
% 0.37/1.05  lits                                    3
% 0.37/1.05  lits eq                                 3
% 0.37/1.05  fd_pure                                 0
% 0.37/1.05  fd_pseudo                               0
% 0.37/1.05  fd_cond                                 0
% 0.37/1.05  fd_pseudo_cond                          0
% 0.37/1.05  AC symbols                              0
% 0.37/1.05  
% 0.37/1.05  ------ Schedule UEQ
% 0.37/1.05  
% 0.37/1.05  ------ pure equality problem: resolution off 
% 0.37/1.05  
% 0.37/1.05  ------ Option_UEQ Time Limit: Unbounded
% 0.37/1.05  
% 0.37/1.05  
% 0.37/1.05  ------ 
% 0.37/1.05  Current options:
% 0.37/1.05  ------ 
% 0.37/1.05  
% 0.37/1.05  ------ Input Options
% 0.37/1.05  
% 0.37/1.05  --out_options                           all
% 0.37/1.05  --tptp_safe_out                         true
% 0.37/1.05  --problem_path                          ""
% 0.37/1.05  --include_path                          ""
% 0.37/1.05  --clausifier                            res/vclausify_rel
% 0.37/1.05  --clausifier_options                    --mode clausify
% 0.37/1.05  --stdin                                 false
% 0.37/1.05  --stats_out                             all
% 0.37/1.05  
% 0.37/1.05  ------ General Options
% 0.37/1.05  
% 0.37/1.05  --fof                                   false
% 0.37/1.05  --time_out_real                         305.
% 0.37/1.05  --time_out_virtual                      -1.
% 0.37/1.05  --symbol_type_check                     false
% 0.37/1.05  --clausify_out                          false
% 0.37/1.05  --sig_cnt_out                           false
% 0.37/1.05  --trig_cnt_out                          false
% 0.37/1.05  --trig_cnt_out_tolerance                1.
% 0.37/1.05  --trig_cnt_out_sk_spl                   false
% 0.37/1.05  --abstr_cl_out                          false
% 0.37/1.05  
% 0.37/1.05  ------ Global Options
% 0.37/1.05  
% 0.37/1.05  --schedule                              default
% 0.37/1.05  --add_important_lit                     false
% 0.37/1.05  --prop_solver_per_cl                    1000
% 0.37/1.05  --min_unsat_core                        false
% 0.37/1.05  --soft_assumptions                      false
% 0.37/1.05  --soft_lemma_size                       3
% 0.37/1.05  --prop_impl_unit_size                   0
% 0.37/1.05  --prop_impl_unit                        []
% 0.37/1.05  --share_sel_clauses                     true
% 0.37/1.05  --reset_solvers                         false
% 0.37/1.05  --bc_imp_inh                            [conj_cone]
% 0.37/1.05  --conj_cone_tolerance                   3.
% 0.37/1.05  --extra_neg_conj                        none
% 0.37/1.05  --large_theory_mode                     true
% 0.37/1.05  --prolific_symb_bound                   200
% 0.37/1.05  --lt_threshold                          2000
% 0.37/1.05  --clause_weak_htbl                      true
% 0.37/1.05  --gc_record_bc_elim                     false
% 0.37/1.05  
% 0.37/1.05  ------ Preprocessing Options
% 0.37/1.05  
% 0.37/1.05  --preprocessing_flag                    true
% 0.37/1.05  --time_out_prep_mult                    0.1
% 0.37/1.05  --splitting_mode                        input
% 0.37/1.05  --splitting_grd                         true
% 0.37/1.05  --splitting_cvd                         false
% 0.37/1.05  --splitting_cvd_svl                     false
% 0.37/1.05  --splitting_nvd                         32
% 0.37/1.05  --sub_typing                            true
% 0.37/1.05  --prep_gs_sim                           true
% 0.37/1.05  --prep_unflatten                        true
% 0.37/1.05  --prep_res_sim                          true
% 0.37/1.05  --prep_upred                            true
% 0.37/1.05  --prep_sem_filter                       exhaustive
% 0.37/1.05  --prep_sem_filter_out                   false
% 0.37/1.05  --pred_elim                             true
% 0.37/1.05  --res_sim_input                         true
% 0.37/1.05  --eq_ax_congr_red                       true
% 0.37/1.05  --pure_diseq_elim                       true
% 0.37/1.05  --brand_transform                       false
% 0.37/1.05  --non_eq_to_eq                          false
% 0.37/1.05  --prep_def_merge                        true
% 0.37/1.05  --prep_def_merge_prop_impl              false
% 0.37/1.05  --prep_def_merge_mbd                    true
% 0.37/1.05  --prep_def_merge_tr_red                 false
% 0.37/1.05  --prep_def_merge_tr_cl                  false
% 0.37/1.05  --smt_preprocessing                     true
% 0.37/1.05  --smt_ac_axioms                         fast
% 0.37/1.05  --preprocessed_out                      false
% 0.37/1.05  --preprocessed_stats                    false
% 0.37/1.05  
% 0.37/1.05  ------ Abstraction refinement Options
% 0.37/1.05  
% 0.37/1.05  --abstr_ref                             []
% 0.37/1.05  --abstr_ref_prep                        false
% 0.37/1.05  --abstr_ref_until_sat                   false
% 0.37/1.05  --abstr_ref_sig_restrict                funpre
% 0.37/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 0.37/1.05  --abstr_ref_under                       []
% 0.37/1.05  
% 0.37/1.05  ------ SAT Options
% 0.37/1.05  
% 0.37/1.05  --sat_mode                              false
% 0.37/1.05  --sat_fm_restart_options                ""
% 0.37/1.05  --sat_gr_def                            false
% 0.37/1.05  --sat_epr_types                         true
% 0.37/1.05  --sat_non_cyclic_types                  false
% 0.37/1.05  --sat_finite_models                     false
% 0.37/1.05  --sat_fm_lemmas                         false
% 0.37/1.05  --sat_fm_prep                           false
% 0.37/1.05  --sat_fm_uc_incr                        true
% 0.37/1.05  --sat_out_model                         small
% 0.37/1.05  --sat_out_clauses                       false
% 0.37/1.05  
% 0.37/1.05  ------ QBF Options
% 0.37/1.05  
% 0.37/1.05  --qbf_mode                              false
% 0.37/1.05  --qbf_elim_univ                         false
% 0.37/1.05  --qbf_dom_inst                          none
% 0.37/1.05  --qbf_dom_pre_inst                      false
% 0.37/1.05  --qbf_sk_in                             false
% 0.37/1.05  --qbf_pred_elim                         true
% 0.37/1.05  --qbf_split                             512
% 0.37/1.05  
% 0.37/1.05  ------ BMC1 Options
% 0.37/1.05  
% 0.37/1.05  --bmc1_incremental                      false
% 0.37/1.05  --bmc1_axioms                           reachable_all
% 0.37/1.05  --bmc1_min_bound                        0
% 0.37/1.05  --bmc1_max_bound                        -1
% 0.37/1.05  --bmc1_max_bound_default                -1
% 0.37/1.05  --bmc1_symbol_reachability              true
% 0.37/1.05  --bmc1_property_lemmas                  false
% 0.37/1.05  --bmc1_k_induction                      false
% 0.37/1.05  --bmc1_non_equiv_states                 false
% 0.37/1.05  --bmc1_deadlock                         false
% 0.37/1.05  --bmc1_ucm                              false
% 0.37/1.05  --bmc1_add_unsat_core                   none
% 0.37/1.05  --bmc1_unsat_core_children              false
% 0.37/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 0.37/1.05  --bmc1_out_stat                         full
% 0.37/1.05  --bmc1_ground_init                      false
% 0.37/1.05  --bmc1_pre_inst_next_state              false
% 0.37/1.05  --bmc1_pre_inst_state                   false
% 0.37/1.05  --bmc1_pre_inst_reach_state             false
% 0.37/1.05  --bmc1_out_unsat_core                   false
% 0.37/1.05  --bmc1_aig_witness_out                  false
% 0.37/1.05  --bmc1_verbose                          false
% 0.37/1.05  --bmc1_dump_clauses_tptp                false
% 0.37/1.05  --bmc1_dump_unsat_core_tptp             false
% 0.37/1.05  --bmc1_dump_file                        -
% 0.37/1.05  --bmc1_ucm_expand_uc_limit              128
% 0.37/1.05  --bmc1_ucm_n_expand_iterations          6
% 0.37/1.05  --bmc1_ucm_extend_mode                  1
% 0.37/1.05  --bmc1_ucm_init_mode                    2
% 0.37/1.05  --bmc1_ucm_cone_mode                    none
% 0.37/1.05  --bmc1_ucm_reduced_relation_type        0
% 0.37/1.05  --bmc1_ucm_relax_model                  4
% 0.37/1.05  --bmc1_ucm_full_tr_after_sat            true
% 0.37/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 0.37/1.05  --bmc1_ucm_layered_model                none
% 0.37/1.05  --bmc1_ucm_max_lemma_size               10
% 0.37/1.05  
% 0.37/1.05  ------ AIG Options
% 0.37/1.05  
% 0.37/1.05  --aig_mode                              false
% 0.37/1.05  
% 0.37/1.05  ------ Instantiation Options
% 0.37/1.05  
% 0.37/1.05  --instantiation_flag                    false
% 0.37/1.05  --inst_sos_flag                         false
% 0.37/1.05  --inst_sos_phase                        true
% 0.37/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.37/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.37/1.05  --inst_lit_sel_side                     num_symb
% 0.37/1.05  --inst_solver_per_active                1400
% 0.37/1.05  --inst_solver_calls_frac                1.
% 0.37/1.05  --inst_passive_queue_type               priority_queues
% 0.37/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.37/1.05  --inst_passive_queues_freq              [25;2]
% 0.37/1.05  --inst_dismatching                      true
% 0.37/1.05  --inst_eager_unprocessed_to_passive     true
% 0.37/1.05  --inst_prop_sim_given                   true
% 0.37/1.05  --inst_prop_sim_new                     false
% 0.37/1.05  --inst_subs_new                         false
% 0.37/1.05  --inst_eq_res_simp                      false
% 0.37/1.05  --inst_subs_given                       false
% 0.37/1.05  --inst_orphan_elimination               true
% 0.37/1.05  --inst_learning_loop_flag               true
% 0.37/1.05  --inst_learning_start                   3000
% 0.37/1.05  --inst_learning_factor                  2
% 0.37/1.05  --inst_start_prop_sim_after_learn       3
% 0.37/1.05  --inst_sel_renew                        solver
% 0.37/1.05  --inst_lit_activity_flag                true
% 0.37/1.05  --inst_restr_to_given                   false
% 0.37/1.05  --inst_activity_threshold               500
% 0.37/1.05  --inst_out_proof                        true
% 0.37/1.05  
% 0.37/1.05  ------ Resolution Options
% 0.37/1.05  
% 0.37/1.05  --resolution_flag                       false
% 0.37/1.05  --res_lit_sel                           adaptive
% 0.37/1.05  --res_lit_sel_side                      none
% 0.37/1.05  --res_ordering                          kbo
% 0.37/1.05  --res_to_prop_solver                    active
% 0.37/1.05  --res_prop_simpl_new                    false
% 0.37/1.05  --res_prop_simpl_given                  true
% 0.37/1.05  --res_passive_queue_type                priority_queues
% 0.37/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.37/1.05  --res_passive_queues_freq               [15;5]
% 0.37/1.05  --res_forward_subs                      full
% 0.37/1.05  --res_backward_subs                     full
% 0.37/1.05  --res_forward_subs_resolution           true
% 0.37/1.05  --res_backward_subs_resolution          true
% 0.37/1.05  --res_orphan_elimination                true
% 0.37/1.05  --res_time_limit                        2.
% 0.37/1.05  --res_out_proof                         true
% 0.37/1.05  
% 0.37/1.05  ------ Superposition Options
% 0.37/1.05  
% 0.37/1.05  --superposition_flag                    true
% 0.37/1.05  --sup_passive_queue_type                priority_queues
% 0.37/1.05  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.37/1.05  --sup_passive_queues_freq               [8;1;4]
% 0.37/1.05  --demod_completeness_check              fast
% 0.37/1.05  --demod_use_ground                      true
% 0.37/1.05  --sup_to_prop_solver                    active
% 0.37/1.05  --sup_prop_simpl_new                    false
% 0.37/1.05  --sup_prop_simpl_given                  false
% 0.37/1.05  --sup_fun_splitting                     true
% 0.37/1.05  --sup_smt_interval                      10000
% 0.37/1.05  
% 0.37/1.05  ------ Superposition Simplification Setup
% 0.37/1.05  
% 0.37/1.05  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 0.37/1.05  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 0.37/1.05  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.05  --sup_full_triv                         [TrivRules]
% 0.37/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 0.37/1.05  --sup_full_bw                           [BwDemod;BwSubsumption]
% 0.37/1.05  --sup_immed_triv                        [TrivRules]
% 0.37/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.37/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 0.37/1.05  --sup_immed_bw_main                     []
% 0.37/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 0.37/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 0.37/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 0.37/1.05  --sup_input_bw                          [BwDemod;BwSubsumption]
% 0.37/1.05  
% 0.37/1.05  ------ Combination Options
% 0.37/1.05  
% 0.37/1.05  --comb_res_mult                         1
% 0.37/1.05  --comb_sup_mult                         1
% 0.37/1.05  --comb_inst_mult                        1000000
% 0.37/1.05  
% 0.37/1.05  ------ Debug Options
% 0.37/1.05  
% 0.37/1.05  --dbg_backtrace                         false
% 0.37/1.05  --dbg_dump_prop_clauses                 false
% 0.37/1.05  --dbg_dump_prop_clauses_file            -
% 0.37/1.05  --dbg_out_stat                          false
% 0.37/1.05  
% 0.37/1.05  
% 0.37/1.05  
% 0.37/1.05  
% 0.37/1.05  ------ Proving...
% 0.37/1.05  
% 0.37/1.05  
% 0.37/1.05  % SZS status Theorem for theBenchmark.p
% 0.37/1.05  
% 0.37/1.05   Resolution empty clause
% 0.37/1.05  
% 0.37/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 0.37/1.05  
% 0.37/1.05  fof(f8,axiom,(
% 0.37/1.05    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f21,plain,(
% 0.37/1.05    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X0,X2)) )),
% 0.37/1.05    inference(cnf_transformation,[],[f8])).
% 0.37/1.05  
% 0.37/1.05  fof(f3,axiom,(
% 0.37/1.05    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f16,plain,(
% 0.37/1.05    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.37/1.05    inference(cnf_transformation,[],[f3])).
% 0.37/1.05  
% 0.37/1.05  fof(f4,axiom,(
% 0.37/1.05    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f17,plain,(
% 0.37/1.05    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.37/1.05    inference(cnf_transformation,[],[f4])).
% 0.37/1.05  
% 0.37/1.05  fof(f5,axiom,(
% 0.37/1.05    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f18,plain,(
% 0.37/1.05    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.37/1.05    inference(cnf_transformation,[],[f5])).
% 0.37/1.05  
% 0.37/1.05  fof(f6,axiom,(
% 0.37/1.05    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f19,plain,(
% 0.37/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.37/1.05    inference(cnf_transformation,[],[f6])).
% 0.37/1.05  
% 0.37/1.05  fof(f23,plain,(
% 0.37/1.05    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.37/1.05    inference(definition_unfolding,[],[f18,f19])).
% 0.37/1.05  
% 0.37/1.05  fof(f24,plain,(
% 0.37/1.05    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.37/1.05    inference(definition_unfolding,[],[f17,f23])).
% 0.37/1.05  
% 0.37/1.05  fof(f25,plain,(
% 0.37/1.05    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.37/1.05    inference(definition_unfolding,[],[f16,f24])).
% 0.37/1.05  
% 0.37/1.05  fof(f28,plain,(
% 0.37/1.05    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X0,X2)) )),
% 0.37/1.05    inference(definition_unfolding,[],[f21,f25,f25])).
% 0.37/1.05  
% 0.37/1.05  fof(f7,axiom,(
% 0.37/1.05    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f20,plain,(
% 0.37/1.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.37/1.05    inference(cnf_transformation,[],[f7])).
% 0.37/1.05  
% 0.37/1.05  fof(f2,axiom,(
% 0.37/1.05    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f15,plain,(
% 0.37/1.05    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 0.37/1.05    inference(cnf_transformation,[],[f2])).
% 0.37/1.05  
% 0.37/1.05  fof(f1,axiom,(
% 0.37/1.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f14,plain,(
% 0.37/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.37/1.05    inference(cnf_transformation,[],[f1])).
% 0.37/1.05  
% 0.37/1.05  fof(f26,plain,(
% 0.37/1.05    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X1,X2,X3,X4),k4_xboole_0(k5_enumset1(X5,X5,X5,X5,X5,X6,X7),k5_enumset1(X0,X0,X0,X1,X2,X3,X4))) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) )),
% 0.37/1.05    inference(definition_unfolding,[],[f15,f14,f23,f25])).
% 0.37/1.05  
% 0.37/1.05  fof(f27,plain,(
% 0.37/1.05    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k4_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X1,X2,X3))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.37/1.05    inference(definition_unfolding,[],[f20,f26])).
% 0.37/1.05  
% 0.37/1.05  fof(f9,conjecture,(
% 0.37/1.05    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 0.37/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.05  
% 0.37/1.05  fof(f10,negated_conjecture,(
% 0.37/1.05    ~! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 0.37/1.05    inference(negated_conjecture,[],[f9])).
% 0.37/1.05  
% 0.37/1.05  fof(f11,plain,(
% 0.37/1.05    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3)),
% 0.37/1.05    inference(ennf_transformation,[],[f10])).
% 0.37/1.05  
% 0.37/1.05  fof(f12,plain,(
% 0.37/1.05    ? [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) != k2_enumset1(X0,X2,X1,X3) => k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.37/1.05    introduced(choice_axiom,[])).
% 0.37/1.05  
% 0.37/1.05  fof(f13,plain,(
% 0.37/1.05    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.37/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f11,f12])).
% 0.37/1.05  
% 0.37/1.05  fof(f22,plain,(
% 0.37/1.05    k2_enumset1(sK0,sK1,sK2,sK3) != k2_enumset1(sK0,sK2,sK1,sK3)),
% 0.37/1.05    inference(cnf_transformation,[],[f13])).
% 0.37/1.05  
% 0.37/1.05  fof(f29,plain,(
% 0.37/1.05    k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3)),
% 0.37/1.05    inference(definition_unfolding,[],[f22,f24,f24])).
% 0.37/1.05  
% 0.37/1.05  cnf(c_1,plain,
% 0.37/1.05      ( k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k5_enumset1(X1,X1,X1,X1,X1,X0,X2) ),
% 0.37/1.05      inference(cnf_transformation,[],[f28]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_11,plain,
% 0.37/1.05      ( k5_enumset1(X0_36,X0_36,X0_36,X0_36,X0_36,X1_36,X2_36) = k5_enumset1(X1_36,X1_36,X1_36,X1_36,X1_36,X0_36,X2_36) ),
% 0.37/1.05      inference(subtyping,[status(esa)],[c_1]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_0,plain,
% 0.37/1.05      ( k5_xboole_0(k5_enumset1(X0,X0,X0,X0,X1,X2,X3),k4_xboole_0(k5_enumset1(X4,X4,X4,X4,X4,X5,X6),k5_enumset1(X0,X0,X0,X0,X1,X2,X3))) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
% 0.37/1.05      inference(cnf_transformation,[],[f27]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_12,plain,
% 0.37/1.05      ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36),k4_xboole_0(k5_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36,X5_36,X6_36),k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36))) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36,X6_36) ),
% 0.37/1.05      inference(subtyping,[status(esa)],[c_0]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_26,plain,
% 0.37/1.05      ( k5_xboole_0(k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36),k4_xboole_0(k5_enumset1(X4_36,X4_36,X4_36,X4_36,X4_36,X5_36,X6_36),k5_enumset1(X0_36,X0_36,X0_36,X0_36,X1_36,X2_36,X3_36))) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X5_36,X4_36,X6_36) ),
% 0.37/1.05      inference(superposition,[status(thm)],[c_11,c_12]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_37,plain,
% 0.37/1.05      ( k5_enumset1(X0_36,X1_36,X2_36,X3_36,X4_36,X5_36,X6_36) = k5_enumset1(X0_36,X1_36,X2_36,X3_36,X5_36,X4_36,X6_36) ),
% 0.37/1.05      inference(superposition,[status(thm)],[c_26,c_12]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_2,negated_conjecture,
% 0.37/1.05      ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) ),
% 0.37/1.05      inference(cnf_transformation,[],[f29]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_10,negated_conjecture,
% 0.37/1.05      ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK2,sK1,sK3) ),
% 0.37/1.05      inference(subtyping,[status(esa)],[c_2]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_38,plain,
% 0.37/1.05      ( k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) != k5_enumset1(sK0,sK0,sK0,sK0,sK1,sK2,sK3) ),
% 0.37/1.05      inference(demodulation,[status(thm)],[c_37,c_10]) ).
% 0.37/1.05  
% 0.37/1.05  cnf(c_59,plain,
% 0.37/1.05      ( $false ),
% 0.37/1.05      inference(equality_resolution_simp,[status(thm)],[c_38]) ).
% 0.37/1.05  
% 0.37/1.05  
% 0.37/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 0.37/1.05  
% 0.37/1.05  ------                               Statistics
% 0.37/1.05  
% 0.37/1.05  ------ General
% 0.37/1.05  
% 0.37/1.05  abstr_ref_over_cycles:                  0
% 0.37/1.05  abstr_ref_under_cycles:                 0
% 0.37/1.05  gc_basic_clause_elim:                   0
% 0.37/1.05  forced_gc_time:                         0
% 0.37/1.05  parsing_time:                           0.021
% 0.37/1.05  unif_index_cands_time:                  0.
% 0.37/1.05  unif_index_add_time:                    0.
% 0.37/1.05  orderings_time:                         0.
% 0.37/1.05  out_proof_time:                         0.007
% 0.37/1.05  total_time:                             0.052
% 0.37/1.05  num_of_symbols:                         38
% 0.37/1.05  num_of_terms:                           203
% 0.37/1.05  
% 0.37/1.05  ------ Preprocessing
% 0.37/1.05  
% 0.37/1.05  num_of_splits:                          0
% 0.37/1.05  num_of_split_atoms:                     0
% 0.37/1.05  num_of_reused_defs:                     0
% 0.37/1.05  num_eq_ax_congr_red:                    7
% 0.37/1.05  num_of_sem_filtered_clauses:            0
% 0.37/1.05  num_of_subtypes:                        3
% 0.37/1.05  monotx_restored_types:                  0
% 0.37/1.05  sat_num_of_epr_types:                   0
% 0.37/1.05  sat_num_of_non_cyclic_types:            0
% 0.37/1.05  sat_guarded_non_collapsed_types:        0
% 0.37/1.05  num_pure_diseq_elim:                    0
% 0.37/1.05  simp_replaced_by:                       0
% 0.37/1.05  res_preprocessed:                       11
% 0.37/1.05  prep_upred:                             0
% 0.37/1.05  prep_unflattend:                        0
% 0.37/1.05  smt_new_axioms:                         0
% 0.37/1.05  pred_elim_cands:                        0
% 0.37/1.05  pred_elim:                              0
% 0.37/1.05  pred_elim_cl:                           0
% 0.37/1.05  pred_elim_cycles:                       0
% 0.37/1.05  merged_defs:                            0
% 0.37/1.05  merged_defs_ncl:                        0
% 0.37/1.05  bin_hyper_res:                          0
% 0.37/1.05  prep_cycles:                            2
% 0.37/1.05  pred_elim_time:                         0.
% 0.37/1.05  splitting_time:                         0.
% 0.37/1.05  sem_filter_time:                        0.
% 0.37/1.05  monotx_time:                            0.
% 0.37/1.05  subtype_inf_time:                       0.
% 0.37/1.05  
% 0.37/1.05  ------ Problem properties
% 0.37/1.05  
% 0.37/1.05  clauses:                                3
% 0.37/1.05  conjectures:                            1
% 0.37/1.05  epr:                                    0
% 0.37/1.05  horn:                                   3
% 0.37/1.05  ground:                                 1
% 0.37/1.05  unary:                                  3
% 0.37/1.05  binary:                                 0
% 0.37/1.05  lits:                                   3
% 0.37/1.05  lits_eq:                                3
% 0.37/1.05  fd_pure:                                0
% 0.37/1.05  fd_pseudo:                              0
% 0.37/1.05  fd_cond:                                0
% 0.37/1.05  fd_pseudo_cond:                         0
% 0.37/1.05  ac_symbols:                             0
% 0.37/1.05  
% 0.37/1.05  ------ Propositional Solver
% 0.37/1.05  
% 0.37/1.05  prop_solver_calls:                      13
% 0.37/1.05  prop_fast_solver_calls:                 34
% 0.37/1.05  smt_solver_calls:                       0
% 0.37/1.05  smt_fast_solver_calls:                  0
% 0.37/1.05  prop_num_of_clauses:                    21
% 0.37/1.05  prop_preprocess_simplified:             133
% 0.37/1.05  prop_fo_subsumed:                       0
% 0.37/1.05  prop_solver_time:                       0.
% 0.37/1.05  smt_solver_time:                        0.
% 0.37/1.05  smt_fast_solver_time:                   0.
% 0.37/1.05  prop_fast_solver_time:                  0.
% 0.37/1.05  prop_unsat_core_time:                   0.
% 0.37/1.05  
% 0.37/1.05  ------ QBF
% 0.37/1.05  
% 0.37/1.05  qbf_q_res:                              0
% 0.37/1.05  qbf_num_tautologies:                    0
% 0.37/1.05  qbf_prep_cycles:                        0
% 0.37/1.05  
% 0.37/1.05  ------ BMC1
% 0.37/1.05  
% 0.37/1.05  bmc1_current_bound:                     -1
% 0.37/1.05  bmc1_last_solved_bound:                 -1
% 0.37/1.05  bmc1_unsat_core_size:                   -1
% 0.37/1.05  bmc1_unsat_core_parents_size:           -1
% 0.37/1.05  bmc1_merge_next_fun:                    0
% 0.37/1.05  bmc1_unsat_core_clauses_time:           0.
% 0.37/1.05  
% 0.37/1.05  ------ Instantiation
% 0.37/1.05  
% 0.37/1.05  inst_num_of_clauses:                    0
% 0.37/1.05  inst_num_in_passive:                    0
% 0.37/1.05  inst_num_in_active:                     0
% 0.37/1.05  inst_num_in_unprocessed:                0
% 0.37/1.05  inst_num_of_loops:                      0
% 0.37/1.05  inst_num_of_learning_restarts:          0
% 0.37/1.05  inst_num_moves_active_passive:          0
% 0.37/1.05  inst_lit_activity:                      0
% 0.37/1.05  inst_lit_activity_moves:                0
% 0.37/1.05  inst_num_tautologies:                   0
% 0.37/1.05  inst_num_prop_implied:                  0
% 0.37/1.05  inst_num_existing_simplified:           0
% 0.37/1.05  inst_num_eq_res_simplified:             0
% 0.37/1.05  inst_num_child_elim:                    0
% 0.37/1.05  inst_num_of_dismatching_blockings:      0
% 0.37/1.05  inst_num_of_non_proper_insts:           0
% 0.37/1.05  inst_num_of_duplicates:                 0
% 0.37/1.05  inst_inst_num_from_inst_to_res:         0
% 0.37/1.05  inst_dismatching_checking_time:         0.
% 0.37/1.05  
% 0.37/1.05  ------ Resolution
% 0.37/1.05  
% 0.37/1.05  res_num_of_clauses:                     0
% 0.37/1.05  res_num_in_passive:                     0
% 0.37/1.05  res_num_in_active:                      0
% 0.37/1.05  res_num_of_loops:                       13
% 0.37/1.05  res_forward_subset_subsumed:            0
% 0.37/1.05  res_backward_subset_subsumed:           0
% 0.37/1.05  res_forward_subsumed:                   0
% 0.37/1.05  res_backward_subsumed:                  0
% 0.37/1.05  res_forward_subsumption_resolution:     0
% 0.37/1.05  res_backward_subsumption_resolution:    0
% 0.37/1.05  res_clause_to_clause_subsumption:       58
% 0.37/1.05  res_orphan_elimination:                 0
% 0.37/1.05  res_tautology_del:                      0
% 0.37/1.05  res_num_eq_res_simplified:              0
% 0.37/1.05  res_num_sel_changes:                    0
% 0.37/1.05  res_moves_from_active_to_pass:          0
% 0.37/1.05  
% 0.37/1.05  ------ Superposition
% 0.37/1.05  
% 0.37/1.05  sup_time_total:                         0.
% 0.37/1.05  sup_time_generating:                    0.
% 0.37/1.05  sup_time_sim_full:                      0.
% 0.37/1.05  sup_time_sim_immed:                     0.
% 0.37/1.05  
% 0.37/1.05  sup_num_of_clauses:                     12
% 0.37/1.05  sup_num_in_active:                      4
% 0.37/1.05  sup_num_in_passive:                     8
% 0.37/1.05  sup_num_of_loops:                       5
% 0.37/1.05  sup_fw_superposition:                   17
% 0.37/1.05  sup_bw_superposition:                   17
% 0.37/1.05  sup_immediate_simplified:               0
% 0.37/1.05  sup_given_eliminated:                   0
% 0.37/1.05  comparisons_done:                       0
% 0.37/1.05  comparisons_avoided:                    0
% 0.37/1.05  
% 0.37/1.05  ------ Simplifications
% 0.37/1.05  
% 0.37/1.05  
% 0.37/1.05  sim_fw_subset_subsumed:                 0
% 0.37/1.05  sim_bw_subset_subsumed:                 0
% 0.37/1.05  sim_fw_subsumed:                        0
% 0.37/1.05  sim_bw_subsumed:                        0
% 0.37/1.05  sim_fw_subsumption_res:                 0
% 0.37/1.05  sim_bw_subsumption_res:                 0
% 0.37/1.05  sim_tautology_del:                      0
% 0.37/1.05  sim_eq_tautology_del:                   0
% 0.37/1.05  sim_eq_res_simp:                        0
% 0.37/1.05  sim_fw_demodulated:                     0
% 0.37/1.05  sim_bw_demodulated:                     1
% 0.37/1.05  sim_light_normalised:                   0
% 0.37/1.05  sim_joinable_taut:                      0
% 0.37/1.05  sim_joinable_simp:                      0
% 0.37/1.05  sim_ac_normalised:                      0
% 0.37/1.05  sim_smt_subsumption:                    0
% 0.37/1.05  
%------------------------------------------------------------------------------
