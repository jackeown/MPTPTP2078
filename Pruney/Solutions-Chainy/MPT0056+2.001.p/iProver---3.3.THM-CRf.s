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
% DateTime   : Thu Dec  3 11:22:54 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :   43 (  81 expanded)
%              Number of clauses        :   25 (  34 expanded)
%              Number of leaves         :    9 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 (  90 expanded)
%              Number of equality atoms :   51 (  89 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f12,f15,f15])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(ennf_transformation,[],[f7])).

fof(f9,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2)
   => k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f16,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,plain,(
    k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2) != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f16,f15,f15])).

cnf(c_3,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_152,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_3,c_1])).

cnf(c_153,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(light_normalisation,[status(thm)],[c_152,c_3])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_151,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_3,c_2])).

cnf(c_253,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_151])).

cnf(c_1794,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_153,c_253])).

cnf(c_144,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[status(thm)],[c_1,c_3])).

cnf(c_423,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_0,c_144])).

cnf(c_1862,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_1794,c_423])).

cnf(c_1929,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_1862,c_3])).

cnf(c_4,negated_conjecture,
    ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2) != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_27,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(demodulation,[status(thm)],[c_4,c_3])).

cnf(c_41,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    inference(demodulation,[status(thm)],[c_0,c_27])).

cnf(c_15824,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) ),
    inference(demodulation,[status(thm)],[c_1929,c_41])).

cnf(c_2728,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_16,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_980,plain,
    ( X0 != k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | X1 != sK0
    | k4_xboole_0(X1,X0) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2727,plain,
    ( X0 != sK0
    | k4_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))
    | k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_980])).

cnf(c_2729,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))
    | k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2727])).

cnf(c_13,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_18,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15824,c_2728,c_2729,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:24:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.66/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.66/1.49  
% 7.66/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.66/1.49  
% 7.66/1.49  ------  iProver source info
% 7.66/1.49  
% 7.66/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.66/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.66/1.49  git: non_committed_changes: false
% 7.66/1.49  git: last_make_outside_of_git: false
% 7.66/1.49  
% 7.66/1.49  ------ 
% 7.66/1.49  
% 7.66/1.49  ------ Input Options
% 7.66/1.49  
% 7.66/1.49  --out_options                           all
% 7.66/1.49  --tptp_safe_out                         true
% 7.66/1.49  --problem_path                          ""
% 7.66/1.49  --include_path                          ""
% 7.66/1.49  --clausifier                            res/vclausify_rel
% 7.66/1.49  --clausifier_options                    --mode clausify
% 7.66/1.49  --stdin                                 false
% 7.66/1.49  --stats_out                             sel
% 7.66/1.49  
% 7.66/1.49  ------ General Options
% 7.66/1.49  
% 7.66/1.49  --fof                                   false
% 7.66/1.49  --time_out_real                         604.99
% 7.66/1.49  --time_out_virtual                      -1.
% 7.66/1.49  --symbol_type_check                     false
% 7.66/1.49  --clausify_out                          false
% 7.66/1.49  --sig_cnt_out                           false
% 7.66/1.49  --trig_cnt_out                          false
% 7.66/1.49  --trig_cnt_out_tolerance                1.
% 7.66/1.49  --trig_cnt_out_sk_spl                   false
% 7.66/1.49  --abstr_cl_out                          false
% 7.66/1.49  
% 7.66/1.49  ------ Global Options
% 7.66/1.49  
% 7.66/1.49  --schedule                              none
% 7.66/1.49  --add_important_lit                     false
% 7.66/1.49  --prop_solver_per_cl                    1000
% 7.66/1.49  --min_unsat_core                        false
% 7.66/1.49  --soft_assumptions                      false
% 7.66/1.49  --soft_lemma_size                       3
% 7.66/1.49  --prop_impl_unit_size                   0
% 7.66/1.49  --prop_impl_unit                        []
% 7.66/1.49  --share_sel_clauses                     true
% 7.66/1.49  --reset_solvers                         false
% 7.66/1.49  --bc_imp_inh                            [conj_cone]
% 7.66/1.49  --conj_cone_tolerance                   3.
% 7.66/1.49  --extra_neg_conj                        none
% 7.66/1.49  --large_theory_mode                     true
% 7.66/1.49  --prolific_symb_bound                   200
% 7.66/1.49  --lt_threshold                          2000
% 7.66/1.49  --clause_weak_htbl                      true
% 7.66/1.49  --gc_record_bc_elim                     false
% 7.66/1.49  
% 7.66/1.49  ------ Preprocessing Options
% 7.66/1.49  
% 7.66/1.49  --preprocessing_flag                    true
% 7.66/1.49  --time_out_prep_mult                    0.1
% 7.66/1.49  --splitting_mode                        input
% 7.66/1.49  --splitting_grd                         true
% 7.66/1.49  --splitting_cvd                         false
% 7.66/1.49  --splitting_cvd_svl                     false
% 7.66/1.49  --splitting_nvd                         32
% 7.66/1.49  --sub_typing                            true
% 7.66/1.49  --prep_gs_sim                           false
% 7.66/1.49  --prep_unflatten                        true
% 7.66/1.49  --prep_res_sim                          true
% 7.66/1.49  --prep_upred                            true
% 7.66/1.49  --prep_sem_filter                       exhaustive
% 7.66/1.49  --prep_sem_filter_out                   false
% 7.66/1.49  --pred_elim                             false
% 7.66/1.49  --res_sim_input                         true
% 7.66/1.49  --eq_ax_congr_red                       true
% 7.66/1.49  --pure_diseq_elim                       true
% 7.66/1.49  --brand_transform                       false
% 7.66/1.49  --non_eq_to_eq                          false
% 7.66/1.49  --prep_def_merge                        true
% 7.66/1.49  --prep_def_merge_prop_impl              false
% 7.66/1.49  --prep_def_merge_mbd                    true
% 7.66/1.49  --prep_def_merge_tr_red                 false
% 7.66/1.49  --prep_def_merge_tr_cl                  false
% 7.66/1.49  --smt_preprocessing                     true
% 7.66/1.49  --smt_ac_axioms                         fast
% 7.66/1.49  --preprocessed_out                      false
% 7.66/1.49  --preprocessed_stats                    false
% 7.66/1.49  
% 7.66/1.49  ------ Abstraction refinement Options
% 7.66/1.49  
% 7.66/1.49  --abstr_ref                             []
% 7.66/1.49  --abstr_ref_prep                        false
% 7.66/1.49  --abstr_ref_until_sat                   false
% 7.66/1.49  --abstr_ref_sig_restrict                funpre
% 7.66/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.66/1.49  --abstr_ref_under                       []
% 7.66/1.49  
% 7.66/1.49  ------ SAT Options
% 7.66/1.49  
% 7.66/1.49  --sat_mode                              false
% 7.66/1.49  --sat_fm_restart_options                ""
% 7.66/1.49  --sat_gr_def                            false
% 7.66/1.49  --sat_epr_types                         true
% 7.66/1.49  --sat_non_cyclic_types                  false
% 7.66/1.49  --sat_finite_models                     false
% 7.66/1.49  --sat_fm_lemmas                         false
% 7.66/1.49  --sat_fm_prep                           false
% 7.66/1.49  --sat_fm_uc_incr                        true
% 7.66/1.49  --sat_out_model                         small
% 7.66/1.49  --sat_out_clauses                       false
% 7.66/1.49  
% 7.66/1.49  ------ QBF Options
% 7.66/1.49  
% 7.66/1.49  --qbf_mode                              false
% 7.66/1.49  --qbf_elim_univ                         false
% 7.66/1.49  --qbf_dom_inst                          none
% 7.66/1.49  --qbf_dom_pre_inst                      false
% 7.66/1.49  --qbf_sk_in                             false
% 7.66/1.49  --qbf_pred_elim                         true
% 7.66/1.49  --qbf_split                             512
% 7.66/1.49  
% 7.66/1.49  ------ BMC1 Options
% 7.66/1.49  
% 7.66/1.49  --bmc1_incremental                      false
% 7.66/1.49  --bmc1_axioms                           reachable_all
% 7.66/1.49  --bmc1_min_bound                        0
% 7.66/1.49  --bmc1_max_bound                        -1
% 7.66/1.49  --bmc1_max_bound_default                -1
% 7.66/1.49  --bmc1_symbol_reachability              true
% 7.66/1.49  --bmc1_property_lemmas                  false
% 7.66/1.49  --bmc1_k_induction                      false
% 7.66/1.49  --bmc1_non_equiv_states                 false
% 7.66/1.49  --bmc1_deadlock                         false
% 7.66/1.49  --bmc1_ucm                              false
% 7.66/1.49  --bmc1_add_unsat_core                   none
% 7.66/1.49  --bmc1_unsat_core_children              false
% 7.66/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.66/1.49  --bmc1_out_stat                         full
% 7.66/1.49  --bmc1_ground_init                      false
% 7.66/1.49  --bmc1_pre_inst_next_state              false
% 7.66/1.49  --bmc1_pre_inst_state                   false
% 7.66/1.49  --bmc1_pre_inst_reach_state             false
% 7.66/1.49  --bmc1_out_unsat_core                   false
% 7.66/1.49  --bmc1_aig_witness_out                  false
% 7.66/1.49  --bmc1_verbose                          false
% 7.66/1.49  --bmc1_dump_clauses_tptp                false
% 7.66/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.66/1.49  --bmc1_dump_file                        -
% 7.66/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.66/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.66/1.49  --bmc1_ucm_extend_mode                  1
% 7.66/1.49  --bmc1_ucm_init_mode                    2
% 7.66/1.49  --bmc1_ucm_cone_mode                    none
% 7.66/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.66/1.49  --bmc1_ucm_relax_model                  4
% 7.66/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.66/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.66/1.49  --bmc1_ucm_layered_model                none
% 7.66/1.49  --bmc1_ucm_max_lemma_size               10
% 7.66/1.49  
% 7.66/1.49  ------ AIG Options
% 7.66/1.49  
% 7.66/1.49  --aig_mode                              false
% 7.66/1.49  
% 7.66/1.49  ------ Instantiation Options
% 7.66/1.49  
% 7.66/1.49  --instantiation_flag                    true
% 7.66/1.49  --inst_sos_flag                         false
% 7.66/1.49  --inst_sos_phase                        true
% 7.66/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.66/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.66/1.49  --inst_lit_sel_side                     num_symb
% 7.66/1.49  --inst_solver_per_active                1400
% 7.66/1.49  --inst_solver_calls_frac                1.
% 7.66/1.49  --inst_passive_queue_type               priority_queues
% 7.66/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.66/1.49  --inst_passive_queues_freq              [25;2]
% 7.66/1.49  --inst_dismatching                      true
% 7.66/1.49  --inst_eager_unprocessed_to_passive     true
% 7.66/1.49  --inst_prop_sim_given                   true
% 7.66/1.49  --inst_prop_sim_new                     false
% 7.66/1.49  --inst_subs_new                         false
% 7.66/1.49  --inst_eq_res_simp                      false
% 7.66/1.49  --inst_subs_given                       false
% 7.66/1.49  --inst_orphan_elimination               true
% 7.66/1.49  --inst_learning_loop_flag               true
% 7.66/1.49  --inst_learning_start                   3000
% 7.66/1.49  --inst_learning_factor                  2
% 7.66/1.49  --inst_start_prop_sim_after_learn       3
% 7.66/1.49  --inst_sel_renew                        solver
% 7.66/1.49  --inst_lit_activity_flag                true
% 7.66/1.49  --inst_restr_to_given                   false
% 7.66/1.49  --inst_activity_threshold               500
% 7.66/1.49  --inst_out_proof                        true
% 7.66/1.49  
% 7.66/1.49  ------ Resolution Options
% 7.66/1.49  
% 7.66/1.49  --resolution_flag                       true
% 7.66/1.49  --res_lit_sel                           adaptive
% 7.66/1.49  --res_lit_sel_side                      none
% 7.66/1.49  --res_ordering                          kbo
% 7.66/1.49  --res_to_prop_solver                    active
% 7.66/1.49  --res_prop_simpl_new                    false
% 7.66/1.49  --res_prop_simpl_given                  true
% 7.66/1.49  --res_passive_queue_type                priority_queues
% 7.66/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.66/1.49  --res_passive_queues_freq               [15;5]
% 7.66/1.49  --res_forward_subs                      full
% 7.66/1.49  --res_backward_subs                     full
% 7.66/1.49  --res_forward_subs_resolution           true
% 7.66/1.49  --res_backward_subs_resolution          true
% 7.66/1.49  --res_orphan_elimination                true
% 7.66/1.49  --res_time_limit                        2.
% 7.66/1.49  --res_out_proof                         true
% 7.66/1.49  
% 7.66/1.49  ------ Superposition Options
% 7.66/1.49  
% 7.66/1.49  --superposition_flag                    true
% 7.66/1.49  --sup_passive_queue_type                priority_queues
% 7.66/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.66/1.49  --sup_passive_queues_freq               [1;4]
% 7.66/1.49  --demod_completeness_check              fast
% 7.66/1.49  --demod_use_ground                      true
% 7.66/1.49  --sup_to_prop_solver                    passive
% 7.66/1.49  --sup_prop_simpl_new                    true
% 7.66/1.49  --sup_prop_simpl_given                  true
% 7.66/1.49  --sup_fun_splitting                     false
% 7.66/1.49  --sup_smt_interval                      50000
% 7.66/1.49  
% 7.66/1.49  ------ Superposition Simplification Setup
% 7.66/1.49  
% 7.66/1.49  --sup_indices_passive                   []
% 7.66/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.66/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.49  --sup_full_bw                           [BwDemod]
% 7.66/1.49  --sup_immed_triv                        [TrivRules]
% 7.66/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.49  --sup_immed_bw_main                     []
% 7.66/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.66/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.49  
% 7.66/1.49  ------ Combination Options
% 7.66/1.49  
% 7.66/1.49  --comb_res_mult                         3
% 7.66/1.49  --comb_sup_mult                         2
% 7.66/1.49  --comb_inst_mult                        10
% 7.66/1.49  
% 7.66/1.49  ------ Debug Options
% 7.66/1.49  
% 7.66/1.49  --dbg_backtrace                         false
% 7.66/1.49  --dbg_dump_prop_clauses                 false
% 7.66/1.49  --dbg_dump_prop_clauses_file            -
% 7.66/1.49  --dbg_out_stat                          false
% 7.66/1.49  ------ Parsing...
% 7.66/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.66/1.49  
% 7.66/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.66/1.49  
% 7.66/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.66/1.49  
% 7.66/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.66/1.49  ------ Proving...
% 7.66/1.49  ------ Problem Properties 
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  clauses                                 5
% 7.66/1.49  conjectures                             1
% 7.66/1.49  EPR                                     0
% 7.66/1.49  Horn                                    5
% 7.66/1.49  unary                                   5
% 7.66/1.49  binary                                  0
% 7.66/1.49  lits                                    5
% 7.66/1.49  lits eq                                 5
% 7.66/1.49  fd_pure                                 0
% 7.66/1.49  fd_pseudo                               0
% 7.66/1.49  fd_cond                                 0
% 7.66/1.49  fd_pseudo_cond                          0
% 7.66/1.49  AC symbols                              0
% 7.66/1.49  
% 7.66/1.49  ------ Input Options Time Limit: Unbounded
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  ------ 
% 7.66/1.49  Current options:
% 7.66/1.49  ------ 
% 7.66/1.49  
% 7.66/1.49  ------ Input Options
% 7.66/1.49  
% 7.66/1.49  --out_options                           all
% 7.66/1.49  --tptp_safe_out                         true
% 7.66/1.49  --problem_path                          ""
% 7.66/1.49  --include_path                          ""
% 7.66/1.49  --clausifier                            res/vclausify_rel
% 7.66/1.49  --clausifier_options                    --mode clausify
% 7.66/1.49  --stdin                                 false
% 7.66/1.49  --stats_out                             sel
% 7.66/1.49  
% 7.66/1.49  ------ General Options
% 7.66/1.49  
% 7.66/1.49  --fof                                   false
% 7.66/1.49  --time_out_real                         604.99
% 7.66/1.49  --time_out_virtual                      -1.
% 7.66/1.49  --symbol_type_check                     false
% 7.66/1.49  --clausify_out                          false
% 7.66/1.49  --sig_cnt_out                           false
% 7.66/1.49  --trig_cnt_out                          false
% 7.66/1.49  --trig_cnt_out_tolerance                1.
% 7.66/1.49  --trig_cnt_out_sk_spl                   false
% 7.66/1.49  --abstr_cl_out                          false
% 7.66/1.49  
% 7.66/1.49  ------ Global Options
% 7.66/1.49  
% 7.66/1.49  --schedule                              none
% 7.66/1.49  --add_important_lit                     false
% 7.66/1.49  --prop_solver_per_cl                    1000
% 7.66/1.49  --min_unsat_core                        false
% 7.66/1.49  --soft_assumptions                      false
% 7.66/1.49  --soft_lemma_size                       3
% 7.66/1.49  --prop_impl_unit_size                   0
% 7.66/1.49  --prop_impl_unit                        []
% 7.66/1.49  --share_sel_clauses                     true
% 7.66/1.49  --reset_solvers                         false
% 7.66/1.49  --bc_imp_inh                            [conj_cone]
% 7.66/1.49  --conj_cone_tolerance                   3.
% 7.66/1.49  --extra_neg_conj                        none
% 7.66/1.49  --large_theory_mode                     true
% 7.66/1.49  --prolific_symb_bound                   200
% 7.66/1.49  --lt_threshold                          2000
% 7.66/1.49  --clause_weak_htbl                      true
% 7.66/1.49  --gc_record_bc_elim                     false
% 7.66/1.49  
% 7.66/1.49  ------ Preprocessing Options
% 7.66/1.49  
% 7.66/1.49  --preprocessing_flag                    true
% 7.66/1.49  --time_out_prep_mult                    0.1
% 7.66/1.49  --splitting_mode                        input
% 7.66/1.49  --splitting_grd                         true
% 7.66/1.49  --splitting_cvd                         false
% 7.66/1.49  --splitting_cvd_svl                     false
% 7.66/1.49  --splitting_nvd                         32
% 7.66/1.49  --sub_typing                            true
% 7.66/1.49  --prep_gs_sim                           false
% 7.66/1.49  --prep_unflatten                        true
% 7.66/1.49  --prep_res_sim                          true
% 7.66/1.49  --prep_upred                            true
% 7.66/1.49  --prep_sem_filter                       exhaustive
% 7.66/1.49  --prep_sem_filter_out                   false
% 7.66/1.49  --pred_elim                             false
% 7.66/1.49  --res_sim_input                         true
% 7.66/1.49  --eq_ax_congr_red                       true
% 7.66/1.49  --pure_diseq_elim                       true
% 7.66/1.49  --brand_transform                       false
% 7.66/1.49  --non_eq_to_eq                          false
% 7.66/1.49  --prep_def_merge                        true
% 7.66/1.49  --prep_def_merge_prop_impl              false
% 7.66/1.49  --prep_def_merge_mbd                    true
% 7.66/1.49  --prep_def_merge_tr_red                 false
% 7.66/1.49  --prep_def_merge_tr_cl                  false
% 7.66/1.49  --smt_preprocessing                     true
% 7.66/1.49  --smt_ac_axioms                         fast
% 7.66/1.49  --preprocessed_out                      false
% 7.66/1.49  --preprocessed_stats                    false
% 7.66/1.49  
% 7.66/1.49  ------ Abstraction refinement Options
% 7.66/1.49  
% 7.66/1.49  --abstr_ref                             []
% 7.66/1.49  --abstr_ref_prep                        false
% 7.66/1.49  --abstr_ref_until_sat                   false
% 7.66/1.49  --abstr_ref_sig_restrict                funpre
% 7.66/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.66/1.49  --abstr_ref_under                       []
% 7.66/1.49  
% 7.66/1.49  ------ SAT Options
% 7.66/1.49  
% 7.66/1.49  --sat_mode                              false
% 7.66/1.49  --sat_fm_restart_options                ""
% 7.66/1.49  --sat_gr_def                            false
% 7.66/1.49  --sat_epr_types                         true
% 7.66/1.49  --sat_non_cyclic_types                  false
% 7.66/1.49  --sat_finite_models                     false
% 7.66/1.49  --sat_fm_lemmas                         false
% 7.66/1.49  --sat_fm_prep                           false
% 7.66/1.49  --sat_fm_uc_incr                        true
% 7.66/1.49  --sat_out_model                         small
% 7.66/1.49  --sat_out_clauses                       false
% 7.66/1.49  
% 7.66/1.49  ------ QBF Options
% 7.66/1.49  
% 7.66/1.49  --qbf_mode                              false
% 7.66/1.49  --qbf_elim_univ                         false
% 7.66/1.49  --qbf_dom_inst                          none
% 7.66/1.49  --qbf_dom_pre_inst                      false
% 7.66/1.49  --qbf_sk_in                             false
% 7.66/1.49  --qbf_pred_elim                         true
% 7.66/1.49  --qbf_split                             512
% 7.66/1.49  
% 7.66/1.49  ------ BMC1 Options
% 7.66/1.49  
% 7.66/1.49  --bmc1_incremental                      false
% 7.66/1.49  --bmc1_axioms                           reachable_all
% 7.66/1.49  --bmc1_min_bound                        0
% 7.66/1.49  --bmc1_max_bound                        -1
% 7.66/1.49  --bmc1_max_bound_default                -1
% 7.66/1.49  --bmc1_symbol_reachability              true
% 7.66/1.49  --bmc1_property_lemmas                  false
% 7.66/1.49  --bmc1_k_induction                      false
% 7.66/1.49  --bmc1_non_equiv_states                 false
% 7.66/1.49  --bmc1_deadlock                         false
% 7.66/1.49  --bmc1_ucm                              false
% 7.66/1.49  --bmc1_add_unsat_core                   none
% 7.66/1.49  --bmc1_unsat_core_children              false
% 7.66/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.66/1.49  --bmc1_out_stat                         full
% 7.66/1.49  --bmc1_ground_init                      false
% 7.66/1.49  --bmc1_pre_inst_next_state              false
% 7.66/1.49  --bmc1_pre_inst_state                   false
% 7.66/1.49  --bmc1_pre_inst_reach_state             false
% 7.66/1.49  --bmc1_out_unsat_core                   false
% 7.66/1.49  --bmc1_aig_witness_out                  false
% 7.66/1.49  --bmc1_verbose                          false
% 7.66/1.49  --bmc1_dump_clauses_tptp                false
% 7.66/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.66/1.49  --bmc1_dump_file                        -
% 7.66/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.66/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.66/1.49  --bmc1_ucm_extend_mode                  1
% 7.66/1.49  --bmc1_ucm_init_mode                    2
% 7.66/1.49  --bmc1_ucm_cone_mode                    none
% 7.66/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.66/1.49  --bmc1_ucm_relax_model                  4
% 7.66/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.66/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.66/1.49  --bmc1_ucm_layered_model                none
% 7.66/1.49  --bmc1_ucm_max_lemma_size               10
% 7.66/1.49  
% 7.66/1.49  ------ AIG Options
% 7.66/1.49  
% 7.66/1.49  --aig_mode                              false
% 7.66/1.49  
% 7.66/1.49  ------ Instantiation Options
% 7.66/1.49  
% 7.66/1.49  --instantiation_flag                    true
% 7.66/1.49  --inst_sos_flag                         false
% 7.66/1.49  --inst_sos_phase                        true
% 7.66/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.66/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.66/1.49  --inst_lit_sel_side                     num_symb
% 7.66/1.49  --inst_solver_per_active                1400
% 7.66/1.49  --inst_solver_calls_frac                1.
% 7.66/1.49  --inst_passive_queue_type               priority_queues
% 7.66/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.66/1.49  --inst_passive_queues_freq              [25;2]
% 7.66/1.49  --inst_dismatching                      true
% 7.66/1.49  --inst_eager_unprocessed_to_passive     true
% 7.66/1.49  --inst_prop_sim_given                   true
% 7.66/1.49  --inst_prop_sim_new                     false
% 7.66/1.49  --inst_subs_new                         false
% 7.66/1.49  --inst_eq_res_simp                      false
% 7.66/1.49  --inst_subs_given                       false
% 7.66/1.49  --inst_orphan_elimination               true
% 7.66/1.49  --inst_learning_loop_flag               true
% 7.66/1.49  --inst_learning_start                   3000
% 7.66/1.49  --inst_learning_factor                  2
% 7.66/1.49  --inst_start_prop_sim_after_learn       3
% 7.66/1.49  --inst_sel_renew                        solver
% 7.66/1.49  --inst_lit_activity_flag                true
% 7.66/1.49  --inst_restr_to_given                   false
% 7.66/1.49  --inst_activity_threshold               500
% 7.66/1.49  --inst_out_proof                        true
% 7.66/1.49  
% 7.66/1.49  ------ Resolution Options
% 7.66/1.49  
% 7.66/1.49  --resolution_flag                       true
% 7.66/1.49  --res_lit_sel                           adaptive
% 7.66/1.49  --res_lit_sel_side                      none
% 7.66/1.49  --res_ordering                          kbo
% 7.66/1.49  --res_to_prop_solver                    active
% 7.66/1.49  --res_prop_simpl_new                    false
% 7.66/1.49  --res_prop_simpl_given                  true
% 7.66/1.49  --res_passive_queue_type                priority_queues
% 7.66/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.66/1.49  --res_passive_queues_freq               [15;5]
% 7.66/1.49  --res_forward_subs                      full
% 7.66/1.49  --res_backward_subs                     full
% 7.66/1.49  --res_forward_subs_resolution           true
% 7.66/1.49  --res_backward_subs_resolution          true
% 7.66/1.49  --res_orphan_elimination                true
% 7.66/1.49  --res_time_limit                        2.
% 7.66/1.49  --res_out_proof                         true
% 7.66/1.49  
% 7.66/1.49  ------ Superposition Options
% 7.66/1.49  
% 7.66/1.49  --superposition_flag                    true
% 7.66/1.49  --sup_passive_queue_type                priority_queues
% 7.66/1.49  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.66/1.49  --sup_passive_queues_freq               [1;4]
% 7.66/1.49  --demod_completeness_check              fast
% 7.66/1.49  --demod_use_ground                      true
% 7.66/1.49  --sup_to_prop_solver                    passive
% 7.66/1.49  --sup_prop_simpl_new                    true
% 7.66/1.49  --sup_prop_simpl_given                  true
% 7.66/1.49  --sup_fun_splitting                     false
% 7.66/1.49  --sup_smt_interval                      50000
% 7.66/1.49  
% 7.66/1.49  ------ Superposition Simplification Setup
% 7.66/1.49  
% 7.66/1.49  --sup_indices_passive                   []
% 7.66/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.66/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.49  --sup_full_bw                           [BwDemod]
% 7.66/1.49  --sup_immed_triv                        [TrivRules]
% 7.66/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.49  --sup_immed_bw_main                     []
% 7.66/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.66/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.66/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.66/1.49  
% 7.66/1.49  ------ Combination Options
% 7.66/1.49  
% 7.66/1.49  --comb_res_mult                         3
% 7.66/1.49  --comb_sup_mult                         2
% 7.66/1.49  --comb_inst_mult                        10
% 7.66/1.49  
% 7.66/1.49  ------ Debug Options
% 7.66/1.49  
% 7.66/1.49  --dbg_backtrace                         false
% 7.66/1.49  --dbg_dump_prop_clauses                 false
% 7.66/1.49  --dbg_dump_prop_clauses_file            -
% 7.66/1.49  --dbg_out_stat                          false
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  ------ Proving...
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  % SZS status Theorem for theBenchmark.p
% 7.66/1.49  
% 7.66/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.66/1.49  
% 7.66/1.49  fof(f4,axiom,(
% 7.66/1.49    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f14,plain,(
% 7.66/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.66/1.49    inference(cnf_transformation,[],[f4])).
% 7.66/1.49  
% 7.66/1.49  fof(f2,axiom,(
% 7.66/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f12,plain,(
% 7.66/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.66/1.49    inference(cnf_transformation,[],[f2])).
% 7.66/1.49  
% 7.66/1.49  fof(f5,axiom,(
% 7.66/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f15,plain,(
% 7.66/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.66/1.49    inference(cnf_transformation,[],[f5])).
% 7.66/1.49  
% 7.66/1.49  fof(f17,plain,(
% 7.66/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.66/1.49    inference(definition_unfolding,[],[f12,f15,f15])).
% 7.66/1.49  
% 7.66/1.49  fof(f1,axiom,(
% 7.66/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f11,plain,(
% 7.66/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.66/1.49    inference(cnf_transformation,[],[f1])).
% 7.66/1.49  
% 7.66/1.49  fof(f3,axiom,(
% 7.66/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f13,plain,(
% 7.66/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.66/1.49    inference(cnf_transformation,[],[f3])).
% 7.66/1.49  
% 7.66/1.49  fof(f6,conjecture,(
% 7.66/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.66/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.66/1.49  
% 7.66/1.49  fof(f7,negated_conjecture,(
% 7.66/1.49    ~! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.66/1.49    inference(negated_conjecture,[],[f6])).
% 7.66/1.49  
% 7.66/1.49  fof(f8,plain,(
% 7.66/1.49    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.66/1.49    inference(ennf_transformation,[],[f7])).
% 7.66/1.49  
% 7.66/1.49  fof(f9,plain,(
% 7.66/1.49    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),X2) => k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 7.66/1.49    introduced(choice_axiom,[])).
% 7.66/1.49  
% 7.66/1.49  fof(f10,plain,(
% 7.66/1.49    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 7.66/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).
% 7.66/1.49  
% 7.66/1.49  fof(f16,plain,(
% 7.66/1.49    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)),
% 7.66/1.49    inference(cnf_transformation,[],[f10])).
% 7.66/1.49  
% 7.66/1.49  fof(f18,plain,(
% 7.66/1.49    k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2) != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 7.66/1.49    inference(definition_unfolding,[],[f16,f15,f15])).
% 7.66/1.49  
% 7.66/1.49  cnf(c_3,plain,
% 7.66/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.66/1.49      inference(cnf_transformation,[],[f14]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1,plain,
% 7.66/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.66/1.49      inference(cnf_transformation,[],[f17]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_152,plain,
% 7.66/1.49      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(k4_xboole_0(X0,X1),X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 7.66/1.49      inference(superposition,[status(thm)],[c_3,c_1]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_153,plain,
% 7.66/1.49      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 7.66/1.49      inference(light_normalisation,[status(thm)],[c_152,c_3]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_0,plain,
% 7.66/1.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.66/1.49      inference(cnf_transformation,[],[f11]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_2,plain,
% 7.66/1.49      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.66/1.49      inference(cnf_transformation,[],[f13]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_151,plain,
% 7.66/1.49      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.66/1.49      inference(superposition,[status(thm)],[c_3,c_2]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_253,plain,
% 7.66/1.49      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.66/1.49      inference(superposition,[status(thm)],[c_0,c_151]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1794,plain,
% 7.66/1.49      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X0,X1))) ),
% 7.66/1.49      inference(demodulation,[status(thm)],[c_153,c_253]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_144,plain,
% 7.66/1.49      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
% 7.66/1.49      inference(superposition,[status(thm)],[c_1,c_3]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_423,plain,
% 7.66/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X1,k2_xboole_0(X2,k4_xboole_0(X1,X0))) ),
% 7.66/1.49      inference(superposition,[status(thm)],[c_0,c_144]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1862,plain,
% 7.66/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.66/1.49      inference(superposition,[status(thm)],[c_1794,c_423]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_1929,plain,
% 7.66/1.49      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 7.66/1.49      inference(demodulation,[status(thm)],[c_1862,c_3]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_4,negated_conjecture,
% 7.66/1.49      ( k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2) != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
% 7.66/1.49      inference(cnf_transformation,[],[f18]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_27,plain,
% 7.66/1.49      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
% 7.66/1.49      inference(demodulation,[status(thm)],[c_4,c_3]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_41,plain,
% 7.66/1.49      ( k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
% 7.66/1.49      inference(demodulation,[status(thm)],[c_0,c_27]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_15824,plain,
% 7.66/1.49      ( k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) ),
% 7.66/1.49      inference(demodulation,[status(thm)],[c_1929,c_41]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_2728,plain,
% 7.66/1.49      ( k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_0]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_16,plain,
% 7.66/1.49      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 7.66/1.49      theory(equality) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_980,plain,
% 7.66/1.49      ( X0 != k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)
% 7.66/1.49      | X1 != sK0
% 7.66/1.49      | k4_xboole_0(X1,X0) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_2727,plain,
% 7.66/1.49      ( X0 != sK0
% 7.66/1.49      | k4_xboole_0(X0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))
% 7.66/1.49      | k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_980]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_2729,plain,
% 7.66/1.49      ( k4_xboole_0(sK0,k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK2))
% 7.66/1.49      | k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),sK2)
% 7.66/1.49      | sK0 != sK0 ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_2727]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_13,plain,( X0 = X0 ),theory(equality) ).
% 7.66/1.49  
% 7.66/1.49  cnf(c_18,plain,
% 7.66/1.49      ( sK0 = sK0 ),
% 7.66/1.49      inference(instantiation,[status(thm)],[c_13]) ).
% 7.66/1.49  
% 7.66/1.49  cnf(contradiction,plain,
% 7.66/1.49      ( $false ),
% 7.66/1.49      inference(minisat,[status(thm)],[c_15824,c_2728,c_2729,c_18]) ).
% 7.66/1.49  
% 7.66/1.49  
% 7.66/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.66/1.49  
% 7.66/1.49  ------                               Statistics
% 7.66/1.49  
% 7.66/1.49  ------ Selected
% 7.66/1.49  
% 7.66/1.49  total_time:                             0.563
% 7.66/1.49  
%------------------------------------------------------------------------------
