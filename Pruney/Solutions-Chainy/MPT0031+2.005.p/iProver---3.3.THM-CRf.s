%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:24 EST 2020

% Result     : Theorem 7.55s
% Output     : CNFRefutation 7.55s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 321 expanded)
%              Number of clauses        :   31 ( 157 expanded)
%              Number of leaves         :    7 (  81 expanded)
%              Depth                    :   18
%              Number of atoms          :   48 ( 322 expanded)
%              Number of equality atoms :   47 ( 321 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ? [X0,X1,X2] : k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) != k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f7])).

fof(f9,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) != k2_xboole_0(X0,k3_xboole_0(X1,X2))
   => k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).

fof(f16,plain,(
    k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f12])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_3,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_49,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X0)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_3])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_24,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_1])).

cnf(c_52,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_24,c_3])).

cnf(c_116,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_52])).

cnf(c_873,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,k3_xboole_0(X0,X1))) = k3_xboole_0(X1,k2_xboole_0(k3_xboole_0(X0,X1),X0)) ),
    inference(superposition,[status(thm)],[c_49,c_116])).

cnf(c_882,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,k3_xboole_0(X0,X1))) = k3_xboole_0(X1,k3_xboole_0(X0,k2_xboole_0(X1,X0))) ),
    inference(light_normalisation,[status(thm)],[c_873,c_52])).

cnf(c_21,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_2])).

cnf(c_279,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),X1)) ),
    inference(superposition,[status(thm)],[c_116,c_3])).

cnf(c_284,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k3_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_279,c_116])).

cnf(c_285,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,k2_xboole_0(X0,X1))) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_284,c_2])).

cnf(c_883,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(k3_xboole_0(X1,X0),X1) ),
    inference(demodulation,[status(thm)],[c_882,c_21,c_285])).

cnf(c_1347,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_883,c_0])).

cnf(c_1777,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X0)) = k3_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1,c_1347])).

cnf(c_1847,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_1777,c_1])).

cnf(c_2538,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),X2)) = k2_xboole_0(X0,k3_xboole_0(X2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_1847,c_49])).

cnf(c_1293,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_883,c_0])).

cnf(c_1627,plain,
    ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_1293,c_0])).

cnf(c_2577,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_1847,c_1627])).

cnf(c_2578,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2577,c_1])).

cnf(c_2594,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,k2_xboole_0(X0,X2))) = k3_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_2538,c_2578])).

cnf(c_4,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_70,plain,
    ( k2_xboole_0(X0,k2_xboole_0(k3_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,X2) ),
    inference(superposition,[status(thm)],[c_21,c_4])).

cnf(c_872,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k3_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_49,c_70])).

cnf(c_2595,plain,
    ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_2594,c_872])).

cnf(c_5,negated_conjecture,
    ( k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_22618,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_2595,c_5])).

cnf(c_23280,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_22618])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n002.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 19:54:51 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.55/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.55/1.49  
% 7.55/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.55/1.49  
% 7.55/1.49  ------  iProver source info
% 7.55/1.49  
% 7.55/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.55/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.55/1.49  git: non_committed_changes: false
% 7.55/1.49  git: last_make_outside_of_git: false
% 7.55/1.49  
% 7.55/1.49  ------ 
% 7.55/1.49  
% 7.55/1.49  ------ Input Options
% 7.55/1.49  
% 7.55/1.49  --out_options                           all
% 7.55/1.49  --tptp_safe_out                         true
% 7.55/1.49  --problem_path                          ""
% 7.55/1.49  --include_path                          ""
% 7.55/1.49  --clausifier                            res/vclausify_rel
% 7.55/1.49  --clausifier_options                    --mode clausify
% 7.55/1.49  --stdin                                 false
% 7.55/1.49  --stats_out                             all
% 7.55/1.49  
% 7.55/1.49  ------ General Options
% 7.55/1.49  
% 7.55/1.49  --fof                                   false
% 7.55/1.49  --time_out_real                         305.
% 7.55/1.49  --time_out_virtual                      -1.
% 7.55/1.49  --symbol_type_check                     false
% 7.55/1.49  --clausify_out                          false
% 7.55/1.49  --sig_cnt_out                           false
% 7.55/1.49  --trig_cnt_out                          false
% 7.55/1.49  --trig_cnt_out_tolerance                1.
% 7.55/1.49  --trig_cnt_out_sk_spl                   false
% 7.55/1.49  --abstr_cl_out                          false
% 7.55/1.49  
% 7.55/1.49  ------ Global Options
% 7.55/1.49  
% 7.55/1.49  --schedule                              default
% 7.55/1.49  --add_important_lit                     false
% 7.55/1.49  --prop_solver_per_cl                    1000
% 7.55/1.49  --min_unsat_core                        false
% 7.55/1.49  --soft_assumptions                      false
% 7.55/1.49  --soft_lemma_size                       3
% 7.55/1.49  --prop_impl_unit_size                   0
% 7.55/1.49  --prop_impl_unit                        []
% 7.55/1.49  --share_sel_clauses                     true
% 7.55/1.49  --reset_solvers                         false
% 7.55/1.49  --bc_imp_inh                            [conj_cone]
% 7.55/1.49  --conj_cone_tolerance                   3.
% 7.55/1.49  --extra_neg_conj                        none
% 7.55/1.49  --large_theory_mode                     true
% 7.55/1.49  --prolific_symb_bound                   200
% 7.55/1.49  --lt_threshold                          2000
% 7.55/1.49  --clause_weak_htbl                      true
% 7.55/1.49  --gc_record_bc_elim                     false
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing Options
% 7.55/1.49  
% 7.55/1.49  --preprocessing_flag                    true
% 7.55/1.49  --time_out_prep_mult                    0.1
% 7.55/1.49  --splitting_mode                        input
% 7.55/1.49  --splitting_grd                         true
% 7.55/1.49  --splitting_cvd                         false
% 7.55/1.49  --splitting_cvd_svl                     false
% 7.55/1.49  --splitting_nvd                         32
% 7.55/1.49  --sub_typing                            true
% 7.55/1.49  --prep_gs_sim                           true
% 7.55/1.49  --prep_unflatten                        true
% 7.55/1.49  --prep_res_sim                          true
% 7.55/1.49  --prep_upred                            true
% 7.55/1.49  --prep_sem_filter                       exhaustive
% 7.55/1.49  --prep_sem_filter_out                   false
% 7.55/1.49  --pred_elim                             true
% 7.55/1.49  --res_sim_input                         true
% 7.55/1.49  --eq_ax_congr_red                       true
% 7.55/1.49  --pure_diseq_elim                       true
% 7.55/1.49  --brand_transform                       false
% 7.55/1.49  --non_eq_to_eq                          false
% 7.55/1.49  --prep_def_merge                        true
% 7.55/1.49  --prep_def_merge_prop_impl              false
% 7.55/1.49  --prep_def_merge_mbd                    true
% 7.55/1.49  --prep_def_merge_tr_red                 false
% 7.55/1.49  --prep_def_merge_tr_cl                  false
% 7.55/1.49  --smt_preprocessing                     true
% 7.55/1.49  --smt_ac_axioms                         fast
% 7.55/1.49  --preprocessed_out                      false
% 7.55/1.49  --preprocessed_stats                    false
% 7.55/1.49  
% 7.55/1.49  ------ Abstraction refinement Options
% 7.55/1.49  
% 7.55/1.49  --abstr_ref                             []
% 7.55/1.49  --abstr_ref_prep                        false
% 7.55/1.49  --abstr_ref_until_sat                   false
% 7.55/1.49  --abstr_ref_sig_restrict                funpre
% 7.55/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.55/1.49  --abstr_ref_under                       []
% 7.55/1.49  
% 7.55/1.49  ------ SAT Options
% 7.55/1.49  
% 7.55/1.49  --sat_mode                              false
% 7.55/1.49  --sat_fm_restart_options                ""
% 7.55/1.49  --sat_gr_def                            false
% 7.55/1.49  --sat_epr_types                         true
% 7.55/1.49  --sat_non_cyclic_types                  false
% 7.55/1.49  --sat_finite_models                     false
% 7.55/1.49  --sat_fm_lemmas                         false
% 7.55/1.49  --sat_fm_prep                           false
% 7.55/1.49  --sat_fm_uc_incr                        true
% 7.55/1.49  --sat_out_model                         small
% 7.55/1.49  --sat_out_clauses                       false
% 7.55/1.49  
% 7.55/1.49  ------ QBF Options
% 7.55/1.49  
% 7.55/1.49  --qbf_mode                              false
% 7.55/1.49  --qbf_elim_univ                         false
% 7.55/1.49  --qbf_dom_inst                          none
% 7.55/1.49  --qbf_dom_pre_inst                      false
% 7.55/1.49  --qbf_sk_in                             false
% 7.55/1.49  --qbf_pred_elim                         true
% 7.55/1.49  --qbf_split                             512
% 7.55/1.49  
% 7.55/1.49  ------ BMC1 Options
% 7.55/1.49  
% 7.55/1.49  --bmc1_incremental                      false
% 7.55/1.49  --bmc1_axioms                           reachable_all
% 7.55/1.49  --bmc1_min_bound                        0
% 7.55/1.49  --bmc1_max_bound                        -1
% 7.55/1.49  --bmc1_max_bound_default                -1
% 7.55/1.49  --bmc1_symbol_reachability              true
% 7.55/1.49  --bmc1_property_lemmas                  false
% 7.55/1.49  --bmc1_k_induction                      false
% 7.55/1.49  --bmc1_non_equiv_states                 false
% 7.55/1.49  --bmc1_deadlock                         false
% 7.55/1.49  --bmc1_ucm                              false
% 7.55/1.49  --bmc1_add_unsat_core                   none
% 7.55/1.49  --bmc1_unsat_core_children              false
% 7.55/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.55/1.49  --bmc1_out_stat                         full
% 7.55/1.49  --bmc1_ground_init                      false
% 7.55/1.49  --bmc1_pre_inst_next_state              false
% 7.55/1.49  --bmc1_pre_inst_state                   false
% 7.55/1.49  --bmc1_pre_inst_reach_state             false
% 7.55/1.49  --bmc1_out_unsat_core                   false
% 7.55/1.49  --bmc1_aig_witness_out                  false
% 7.55/1.49  --bmc1_verbose                          false
% 7.55/1.49  --bmc1_dump_clauses_tptp                false
% 7.55/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.55/1.49  --bmc1_dump_file                        -
% 7.55/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.55/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.55/1.49  --bmc1_ucm_extend_mode                  1
% 7.55/1.49  --bmc1_ucm_init_mode                    2
% 7.55/1.49  --bmc1_ucm_cone_mode                    none
% 7.55/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.55/1.49  --bmc1_ucm_relax_model                  4
% 7.55/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.55/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.55/1.49  --bmc1_ucm_layered_model                none
% 7.55/1.49  --bmc1_ucm_max_lemma_size               10
% 7.55/1.49  
% 7.55/1.49  ------ AIG Options
% 7.55/1.49  
% 7.55/1.49  --aig_mode                              false
% 7.55/1.49  
% 7.55/1.49  ------ Instantiation Options
% 7.55/1.49  
% 7.55/1.49  --instantiation_flag                    true
% 7.55/1.49  --inst_sos_flag                         false
% 7.55/1.49  --inst_sos_phase                        true
% 7.55/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.55/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.55/1.49  --inst_lit_sel_side                     num_symb
% 7.55/1.49  --inst_solver_per_active                1400
% 7.55/1.49  --inst_solver_calls_frac                1.
% 7.55/1.49  --inst_passive_queue_type               priority_queues
% 7.55/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.55/1.49  --inst_passive_queues_freq              [25;2]
% 7.55/1.49  --inst_dismatching                      true
% 7.55/1.49  --inst_eager_unprocessed_to_passive     true
% 7.55/1.49  --inst_prop_sim_given                   true
% 7.55/1.49  --inst_prop_sim_new                     false
% 7.55/1.49  --inst_subs_new                         false
% 7.55/1.49  --inst_eq_res_simp                      false
% 7.55/1.49  --inst_subs_given                       false
% 7.55/1.49  --inst_orphan_elimination               true
% 7.55/1.49  --inst_learning_loop_flag               true
% 7.55/1.49  --inst_learning_start                   3000
% 7.55/1.49  --inst_learning_factor                  2
% 7.55/1.49  --inst_start_prop_sim_after_learn       3
% 7.55/1.49  --inst_sel_renew                        solver
% 7.55/1.49  --inst_lit_activity_flag                true
% 7.55/1.49  --inst_restr_to_given                   false
% 7.55/1.49  --inst_activity_threshold               500
% 7.55/1.49  --inst_out_proof                        true
% 7.55/1.49  
% 7.55/1.49  ------ Resolution Options
% 7.55/1.49  
% 7.55/1.49  --resolution_flag                       true
% 7.55/1.49  --res_lit_sel                           adaptive
% 7.55/1.49  --res_lit_sel_side                      none
% 7.55/1.49  --res_ordering                          kbo
% 7.55/1.49  --res_to_prop_solver                    active
% 7.55/1.49  --res_prop_simpl_new                    false
% 7.55/1.49  --res_prop_simpl_given                  true
% 7.55/1.49  --res_passive_queue_type                priority_queues
% 7.55/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.55/1.49  --res_passive_queues_freq               [15;5]
% 7.55/1.49  --res_forward_subs                      full
% 7.55/1.49  --res_backward_subs                     full
% 7.55/1.49  --res_forward_subs_resolution           true
% 7.55/1.49  --res_backward_subs_resolution          true
% 7.55/1.49  --res_orphan_elimination                true
% 7.55/1.49  --res_time_limit                        2.
% 7.55/1.49  --res_out_proof                         true
% 7.55/1.49  
% 7.55/1.49  ------ Superposition Options
% 7.55/1.49  
% 7.55/1.49  --superposition_flag                    true
% 7.55/1.49  --sup_passive_queue_type                priority_queues
% 7.55/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.55/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.55/1.49  --demod_completeness_check              fast
% 7.55/1.49  --demod_use_ground                      true
% 7.55/1.49  --sup_to_prop_solver                    passive
% 7.55/1.49  --sup_prop_simpl_new                    true
% 7.55/1.49  --sup_prop_simpl_given                  true
% 7.55/1.49  --sup_fun_splitting                     false
% 7.55/1.49  --sup_smt_interval                      50000
% 7.55/1.49  
% 7.55/1.49  ------ Superposition Simplification Setup
% 7.55/1.49  
% 7.55/1.49  --sup_indices_passive                   []
% 7.55/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.55/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.49  --sup_full_bw                           [BwDemod]
% 7.55/1.49  --sup_immed_triv                        [TrivRules]
% 7.55/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.55/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.49  --sup_immed_bw_main                     []
% 7.55/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.55/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.55/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.55/1.49  
% 7.55/1.49  ------ Combination Options
% 7.55/1.49  
% 7.55/1.49  --comb_res_mult                         3
% 7.55/1.49  --comb_sup_mult                         2
% 7.55/1.49  --comb_inst_mult                        10
% 7.55/1.49  
% 7.55/1.49  ------ Debug Options
% 7.55/1.49  
% 7.55/1.49  --dbg_backtrace                         false
% 7.55/1.49  --dbg_dump_prop_clauses                 false
% 7.55/1.49  --dbg_dump_prop_clauses_file            -
% 7.55/1.49  --dbg_out_stat                          false
% 7.55/1.49  ------ Parsing...
% 7.55/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.55/1.49  ------ Proving...
% 7.55/1.49  ------ Problem Properties 
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  clauses                                 6
% 7.55/1.49  conjectures                             1
% 7.55/1.49  EPR                                     0
% 7.55/1.49  Horn                                    6
% 7.55/1.49  unary                                   6
% 7.55/1.49  binary                                  0
% 7.55/1.49  lits                                    6
% 7.55/1.49  lits eq                                 6
% 7.55/1.49  fd_pure                                 0
% 7.55/1.49  fd_pseudo                               0
% 7.55/1.49  fd_cond                                 0
% 7.55/1.49  fd_pseudo_cond                          0
% 7.55/1.49  AC symbols                              0
% 7.55/1.49  
% 7.55/1.49  ------ Schedule UEQ
% 7.55/1.49  
% 7.55/1.49  ------ pure equality problem: resolution off 
% 7.55/1.49  
% 7.55/1.49  ------ Option_UEQ Time Limit: Unbounded
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  ------ 
% 7.55/1.49  Current options:
% 7.55/1.49  ------ 
% 7.55/1.49  
% 7.55/1.49  ------ Input Options
% 7.55/1.49  
% 7.55/1.49  --out_options                           all
% 7.55/1.49  --tptp_safe_out                         true
% 7.55/1.49  --problem_path                          ""
% 7.55/1.49  --include_path                          ""
% 7.55/1.49  --clausifier                            res/vclausify_rel
% 7.55/1.49  --clausifier_options                    --mode clausify
% 7.55/1.49  --stdin                                 false
% 7.55/1.49  --stats_out                             all
% 7.55/1.49  
% 7.55/1.49  ------ General Options
% 7.55/1.49  
% 7.55/1.49  --fof                                   false
% 7.55/1.49  --time_out_real                         305.
% 7.55/1.49  --time_out_virtual                      -1.
% 7.55/1.49  --symbol_type_check                     false
% 7.55/1.49  --clausify_out                          false
% 7.55/1.49  --sig_cnt_out                           false
% 7.55/1.49  --trig_cnt_out                          false
% 7.55/1.49  --trig_cnt_out_tolerance                1.
% 7.55/1.49  --trig_cnt_out_sk_spl                   false
% 7.55/1.49  --abstr_cl_out                          false
% 7.55/1.49  
% 7.55/1.49  ------ Global Options
% 7.55/1.49  
% 7.55/1.49  --schedule                              default
% 7.55/1.49  --add_important_lit                     false
% 7.55/1.49  --prop_solver_per_cl                    1000
% 7.55/1.49  --min_unsat_core                        false
% 7.55/1.49  --soft_assumptions                      false
% 7.55/1.49  --soft_lemma_size                       3
% 7.55/1.49  --prop_impl_unit_size                   0
% 7.55/1.49  --prop_impl_unit                        []
% 7.55/1.49  --share_sel_clauses                     true
% 7.55/1.49  --reset_solvers                         false
% 7.55/1.49  --bc_imp_inh                            [conj_cone]
% 7.55/1.49  --conj_cone_tolerance                   3.
% 7.55/1.49  --extra_neg_conj                        none
% 7.55/1.49  --large_theory_mode                     true
% 7.55/1.49  --prolific_symb_bound                   200
% 7.55/1.49  --lt_threshold                          2000
% 7.55/1.49  --clause_weak_htbl                      true
% 7.55/1.49  --gc_record_bc_elim                     false
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing Options
% 7.55/1.49  
% 7.55/1.49  --preprocessing_flag                    true
% 7.55/1.49  --time_out_prep_mult                    0.1
% 7.55/1.49  --splitting_mode                        input
% 7.55/1.49  --splitting_grd                         true
% 7.55/1.49  --splitting_cvd                         false
% 7.55/1.49  --splitting_cvd_svl                     false
% 7.55/1.49  --splitting_nvd                         32
% 7.55/1.49  --sub_typing                            true
% 7.55/1.49  --prep_gs_sim                           true
% 7.55/1.49  --prep_unflatten                        true
% 7.55/1.49  --prep_res_sim                          true
% 7.55/1.49  --prep_upred                            true
% 7.55/1.49  --prep_sem_filter                       exhaustive
% 7.55/1.49  --prep_sem_filter_out                   false
% 7.55/1.49  --pred_elim                             true
% 7.55/1.49  --res_sim_input                         true
% 7.55/1.49  --eq_ax_congr_red                       true
% 7.55/1.49  --pure_diseq_elim                       true
% 7.55/1.49  --brand_transform                       false
% 7.55/1.49  --non_eq_to_eq                          false
% 7.55/1.49  --prep_def_merge                        true
% 7.55/1.49  --prep_def_merge_prop_impl              false
% 7.55/1.49  --prep_def_merge_mbd                    true
% 7.55/1.49  --prep_def_merge_tr_red                 false
% 7.55/1.49  --prep_def_merge_tr_cl                  false
% 7.55/1.49  --smt_preprocessing                     true
% 7.55/1.49  --smt_ac_axioms                         fast
% 7.55/1.49  --preprocessed_out                      false
% 7.55/1.49  --preprocessed_stats                    false
% 7.55/1.49  
% 7.55/1.49  ------ Abstraction refinement Options
% 7.55/1.49  
% 7.55/1.49  --abstr_ref                             []
% 7.55/1.49  --abstr_ref_prep                        false
% 7.55/1.49  --abstr_ref_until_sat                   false
% 7.55/1.49  --abstr_ref_sig_restrict                funpre
% 7.55/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.55/1.49  --abstr_ref_under                       []
% 7.55/1.49  
% 7.55/1.49  ------ SAT Options
% 7.55/1.49  
% 7.55/1.49  --sat_mode                              false
% 7.55/1.49  --sat_fm_restart_options                ""
% 7.55/1.49  --sat_gr_def                            false
% 7.55/1.49  --sat_epr_types                         true
% 7.55/1.49  --sat_non_cyclic_types                  false
% 7.55/1.49  --sat_finite_models                     false
% 7.55/1.49  --sat_fm_lemmas                         false
% 7.55/1.49  --sat_fm_prep                           false
% 7.55/1.49  --sat_fm_uc_incr                        true
% 7.55/1.49  --sat_out_model                         small
% 7.55/1.49  --sat_out_clauses                       false
% 7.55/1.49  
% 7.55/1.49  ------ QBF Options
% 7.55/1.49  
% 7.55/1.49  --qbf_mode                              false
% 7.55/1.49  --qbf_elim_univ                         false
% 7.55/1.49  --qbf_dom_inst                          none
% 7.55/1.49  --qbf_dom_pre_inst                      false
% 7.55/1.49  --qbf_sk_in                             false
% 7.55/1.49  --qbf_pred_elim                         true
% 7.55/1.49  --qbf_split                             512
% 7.55/1.49  
% 7.55/1.49  ------ BMC1 Options
% 7.55/1.49  
% 7.55/1.49  --bmc1_incremental                      false
% 7.55/1.49  --bmc1_axioms                           reachable_all
% 7.55/1.49  --bmc1_min_bound                        0
% 7.55/1.49  --bmc1_max_bound                        -1
% 7.55/1.49  --bmc1_max_bound_default                -1
% 7.55/1.49  --bmc1_symbol_reachability              true
% 7.55/1.49  --bmc1_property_lemmas                  false
% 7.55/1.49  --bmc1_k_induction                      false
% 7.55/1.49  --bmc1_non_equiv_states                 false
% 7.55/1.49  --bmc1_deadlock                         false
% 7.55/1.49  --bmc1_ucm                              false
% 7.55/1.49  --bmc1_add_unsat_core                   none
% 7.55/1.49  --bmc1_unsat_core_children              false
% 7.55/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.55/1.49  --bmc1_out_stat                         full
% 7.55/1.49  --bmc1_ground_init                      false
% 7.55/1.49  --bmc1_pre_inst_next_state              false
% 7.55/1.49  --bmc1_pre_inst_state                   false
% 7.55/1.49  --bmc1_pre_inst_reach_state             false
% 7.55/1.49  --bmc1_out_unsat_core                   false
% 7.55/1.49  --bmc1_aig_witness_out                  false
% 7.55/1.49  --bmc1_verbose                          false
% 7.55/1.49  --bmc1_dump_clauses_tptp                false
% 7.55/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.55/1.49  --bmc1_dump_file                        -
% 7.55/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.55/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.55/1.49  --bmc1_ucm_extend_mode                  1
% 7.55/1.49  --bmc1_ucm_init_mode                    2
% 7.55/1.49  --bmc1_ucm_cone_mode                    none
% 7.55/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.55/1.49  --bmc1_ucm_relax_model                  4
% 7.55/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.55/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.55/1.49  --bmc1_ucm_layered_model                none
% 7.55/1.49  --bmc1_ucm_max_lemma_size               10
% 7.55/1.49  
% 7.55/1.49  ------ AIG Options
% 7.55/1.49  
% 7.55/1.49  --aig_mode                              false
% 7.55/1.49  
% 7.55/1.49  ------ Instantiation Options
% 7.55/1.49  
% 7.55/1.49  --instantiation_flag                    false
% 7.55/1.49  --inst_sos_flag                         false
% 7.55/1.49  --inst_sos_phase                        true
% 7.55/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.55/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.55/1.49  --inst_lit_sel_side                     num_symb
% 7.55/1.49  --inst_solver_per_active                1400
% 7.55/1.49  --inst_solver_calls_frac                1.
% 7.55/1.49  --inst_passive_queue_type               priority_queues
% 7.55/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.55/1.49  --inst_passive_queues_freq              [25;2]
% 7.55/1.49  --inst_dismatching                      true
% 7.55/1.49  --inst_eager_unprocessed_to_passive     true
% 7.55/1.49  --inst_prop_sim_given                   true
% 7.55/1.49  --inst_prop_sim_new                     false
% 7.55/1.49  --inst_subs_new                         false
% 7.55/1.49  --inst_eq_res_simp                      false
% 7.55/1.49  --inst_subs_given                       false
% 7.55/1.49  --inst_orphan_elimination               true
% 7.55/1.49  --inst_learning_loop_flag               true
% 7.55/1.49  --inst_learning_start                   3000
% 7.55/1.49  --inst_learning_factor                  2
% 7.55/1.49  --inst_start_prop_sim_after_learn       3
% 7.55/1.49  --inst_sel_renew                        solver
% 7.55/1.49  --inst_lit_activity_flag                true
% 7.55/1.49  --inst_restr_to_given                   false
% 7.55/1.49  --inst_activity_threshold               500
% 7.55/1.49  --inst_out_proof                        true
% 7.55/1.49  
% 7.55/1.49  ------ Resolution Options
% 7.55/1.49  
% 7.55/1.49  --resolution_flag                       false
% 7.55/1.49  --res_lit_sel                           adaptive
% 7.55/1.49  --res_lit_sel_side                      none
% 7.55/1.49  --res_ordering                          kbo
% 7.55/1.49  --res_to_prop_solver                    active
% 7.55/1.49  --res_prop_simpl_new                    false
% 7.55/1.49  --res_prop_simpl_given                  true
% 7.55/1.49  --res_passive_queue_type                priority_queues
% 7.55/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.55/1.49  --res_passive_queues_freq               [15;5]
% 7.55/1.49  --res_forward_subs                      full
% 7.55/1.49  --res_backward_subs                     full
% 7.55/1.49  --res_forward_subs_resolution           true
% 7.55/1.49  --res_backward_subs_resolution          true
% 7.55/1.49  --res_orphan_elimination                true
% 7.55/1.49  --res_time_limit                        2.
% 7.55/1.49  --res_out_proof                         true
% 7.55/1.49  
% 7.55/1.49  ------ Superposition Options
% 7.55/1.49  
% 7.55/1.49  --superposition_flag                    true
% 7.55/1.49  --sup_passive_queue_type                priority_queues
% 7.55/1.49  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.55/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.55/1.49  --demod_completeness_check              fast
% 7.55/1.49  --demod_use_ground                      true
% 7.55/1.49  --sup_to_prop_solver                    active
% 7.55/1.49  --sup_prop_simpl_new                    false
% 7.55/1.49  --sup_prop_simpl_given                  false
% 7.55/1.49  --sup_fun_splitting                     true
% 7.55/1.49  --sup_smt_interval                      10000
% 7.55/1.49  
% 7.55/1.49  ------ Superposition Simplification Setup
% 7.55/1.49  
% 7.55/1.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.55/1.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.55/1.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.55/1.49  --sup_full_triv                         [TrivRules]
% 7.55/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.55/1.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.55/1.49  --sup_immed_triv                        [TrivRules]
% 7.55/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.55/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.55/1.49  --sup_immed_bw_main                     []
% 7.55/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.55/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.55/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.55/1.49  --sup_input_bw                          [BwDemod;BwSubsumption]
% 7.55/1.49  
% 7.55/1.49  ------ Combination Options
% 7.55/1.49  
% 7.55/1.49  --comb_res_mult                         1
% 7.55/1.49  --comb_sup_mult                         1
% 7.55/1.49  --comb_inst_mult                        1000000
% 7.55/1.49  
% 7.55/1.49  ------ Debug Options
% 7.55/1.49  
% 7.55/1.49  --dbg_backtrace                         false
% 7.55/1.49  --dbg_dump_prop_clauses                 false
% 7.55/1.49  --dbg_dump_prop_clauses_file            -
% 7.55/1.49  --dbg_out_stat                          false
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  ------ Proving...
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  % SZS status Theorem for theBenchmark.p
% 7.55/1.49  
% 7.55/1.49   Resolution empty clause
% 7.55/1.49  
% 7.55/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.55/1.49  
% 7.55/1.49  fof(f2,axiom,(
% 7.55/1.49    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f12,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 7.55/1.49    inference(cnf_transformation,[],[f2])).
% 7.55/1.49  
% 7.55/1.49  fof(f1,axiom,(
% 7.55/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f11,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f1])).
% 7.55/1.49  
% 7.55/1.49  fof(f4,axiom,(
% 7.55/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f14,plain,(
% 7.55/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 7.55/1.49    inference(cnf_transformation,[],[f4])).
% 7.55/1.49  
% 7.55/1.49  fof(f3,axiom,(
% 7.55/1.49    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f13,plain,(
% 7.55/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 7.55/1.49    inference(cnf_transformation,[],[f3])).
% 7.55/1.49  
% 7.55/1.49  fof(f5,axiom,(
% 7.55/1.49    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f15,plain,(
% 7.55/1.49    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 7.55/1.49    inference(cnf_transformation,[],[f5])).
% 7.55/1.49  
% 7.55/1.49  fof(f6,conjecture,(
% 7.55/1.49    ! [X0,X1,X2] : k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2))),
% 7.55/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.55/1.49  
% 7.55/1.49  fof(f7,negated_conjecture,(
% 7.55/1.49    ~! [X0,X1,X2] : k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2))),
% 7.55/1.49    inference(negated_conjecture,[],[f6])).
% 7.55/1.49  
% 7.55/1.49  fof(f8,plain,(
% 7.55/1.49    ? [X0,X1,X2] : k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) != k2_xboole_0(X0,k3_xboole_0(X1,X2))),
% 7.55/1.49    inference(ennf_transformation,[],[f7])).
% 7.55/1.49  
% 7.55/1.49  fof(f9,plain,(
% 7.55/1.49    ? [X0,X1,X2] : k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) != k2_xboole_0(X0,k3_xboole_0(X1,X2)) => k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 7.55/1.49    introduced(choice_axiom,[])).
% 7.55/1.49  
% 7.55/1.49  fof(f10,plain,(
% 7.55/1.49    k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 7.55/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f9])).
% 7.55/1.49  
% 7.55/1.49  fof(f16,plain,(
% 7.55/1.49    k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 7.55/1.49    inference(cnf_transformation,[],[f10])).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1,plain,
% 7.55/1.49      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 7.55/1.49      inference(cnf_transformation,[],[f12]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_0,plain,
% 7.55/1.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.55/1.49      inference(cnf_transformation,[],[f11]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_3,plain,
% 7.55/1.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.55/1.49      inference(cnf_transformation,[],[f14]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_49,plain,
% 7.55/1.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X0)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_0,c_3]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2,plain,
% 7.55/1.49      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 7.55/1.49      inference(cnf_transformation,[],[f13]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_24,plain,
% 7.55/1.49      ( k3_xboole_0(X0,X0) = X0 ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_2,c_1]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_52,plain,
% 7.55/1.49      ( k2_xboole_0(k3_xboole_0(X0,X1),X0) = k3_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_24,c_3]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_116,plain,
% 7.55/1.49      ( k2_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(X1,k2_xboole_0(X0,X1)) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_0,c_52]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_873,plain,
% 7.55/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,k3_xboole_0(X0,X1))) = k3_xboole_0(X1,k2_xboole_0(k3_xboole_0(X0,X1),X0)) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_49,c_116]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_882,plain,
% 7.55/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X1,k3_xboole_0(X0,X1))) = k3_xboole_0(X1,k3_xboole_0(X0,k2_xboole_0(X1,X0))) ),
% 7.55/1.49      inference(light_normalisation,[status(thm)],[c_873,c_52]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_21,plain,
% 7.55/1.49      ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_0,c_2]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_279,plain,
% 7.55/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k2_xboole_0(k3_xboole_0(X0,X1),X1)) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_116,c_3]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_284,plain,
% 7.55/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),k2_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,k3_xboole_0(X1,k2_xboole_0(X0,X1))) ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_279,c_116]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_285,plain,
% 7.55/1.49      ( k3_xboole_0(X0,k3_xboole_0(X1,k2_xboole_0(X0,X1))) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 7.55/1.49      inference(light_normalisation,[status(thm)],[c_284,c_2]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_883,plain,
% 7.55/1.49      ( k3_xboole_0(k3_xboole_0(X0,X1),X1) = k3_xboole_0(k3_xboole_0(X1,X0),X1) ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_882,c_21,c_285]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1347,plain,
% 7.55/1.49      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(k3_xboole_0(X1,X0),X0) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_883,c_0]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1777,plain,
% 7.55/1.49      ( k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X0)) = k3_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1,c_1347]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1847,plain,
% 7.55/1.49      ( k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(k2_xboole_0(X0,X1),X0)) = X0 ),
% 7.55/1.49      inference(light_normalisation,[status(thm)],[c_1777,c_1]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2538,plain,
% 7.55/1.49      ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),X0),X2)) = k2_xboole_0(X0,k3_xboole_0(X2,k2_xboole_0(X0,X1))) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1847,c_49]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1293,plain,
% 7.55/1.49      ( k3_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_883,c_0]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_1627,plain,
% 7.55/1.49      ( k3_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X1,X0)) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1293,c_0]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2577,plain,
% 7.55/1.49      ( k3_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_1847,c_1627]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2578,plain,
% 7.55/1.49      ( k3_xboole_0(k2_xboole_0(X0,X1),X0) = X0 ),
% 7.55/1.49      inference(light_normalisation,[status(thm)],[c_2577,c_1]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2594,plain,
% 7.55/1.49      ( k2_xboole_0(X0,k3_xboole_0(X1,k2_xboole_0(X0,X2))) = k3_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X0,X1)) ),
% 7.55/1.49      inference(light_normalisation,[status(thm)],[c_2538,c_2578]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_4,plain,
% 7.55/1.49      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 7.55/1.49      inference(cnf_transformation,[],[f15]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_70,plain,
% 7.55/1.49      ( k2_xboole_0(X0,k2_xboole_0(k3_xboole_0(X1,X0),X2)) = k2_xboole_0(X0,X2) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_21,c_4]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_872,plain,
% 7.55/1.49      ( k2_xboole_0(X0,k3_xboole_0(X1,k2_xboole_0(X0,X2))) = k2_xboole_0(X0,k3_xboole_0(X2,X1)) ),
% 7.55/1.49      inference(superposition,[status(thm)],[c_49,c_70]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_2595,plain,
% 7.55/1.49      ( k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_2594,c_872]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_5,negated_conjecture,
% 7.55/1.49      ( k3_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
% 7.55/1.49      inference(cnf_transformation,[],[f16]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_22618,plain,
% 7.55/1.49      ( k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
% 7.55/1.49      inference(demodulation,[status(thm)],[c_2595,c_5]) ).
% 7.55/1.49  
% 7.55/1.49  cnf(c_23280,plain,
% 7.55/1.49      ( $false ),
% 7.55/1.49      inference(equality_resolution_simp,[status(thm)],[c_22618]) ).
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.55/1.49  
% 7.55/1.49  ------                               Statistics
% 7.55/1.49  
% 7.55/1.49  ------ General
% 7.55/1.49  
% 7.55/1.49  abstr_ref_over_cycles:                  0
% 7.55/1.49  abstr_ref_under_cycles:                 0
% 7.55/1.49  gc_basic_clause_elim:                   0
% 7.55/1.49  forced_gc_time:                         0
% 7.55/1.49  parsing_time:                           0.008
% 7.55/1.49  unif_index_cands_time:                  0.
% 7.55/1.49  unif_index_add_time:                    0.
% 7.55/1.49  orderings_time:                         0.
% 7.55/1.49  out_proof_time:                         0.005
% 7.55/1.49  total_time:                             0.708
% 7.55/1.49  num_of_symbols:                         36
% 7.55/1.49  num_of_terms:                           33353
% 7.55/1.49  
% 7.55/1.49  ------ Preprocessing
% 7.55/1.49  
% 7.55/1.49  num_of_splits:                          0
% 7.55/1.49  num_of_split_atoms:                     0
% 7.55/1.49  num_of_reused_defs:                     0
% 7.55/1.49  num_eq_ax_congr_red:                    0
% 7.55/1.49  num_of_sem_filtered_clauses:            0
% 7.55/1.49  num_of_subtypes:                        0
% 7.55/1.49  monotx_restored_types:                  0
% 7.55/1.49  sat_num_of_epr_types:                   0
% 7.55/1.49  sat_num_of_non_cyclic_types:            0
% 7.55/1.49  sat_guarded_non_collapsed_types:        0
% 7.55/1.49  num_pure_diseq_elim:                    0
% 7.55/1.49  simp_replaced_by:                       0
% 7.55/1.49  res_preprocessed:                       16
% 7.55/1.49  prep_upred:                             0
% 7.55/1.49  prep_unflattend:                        0
% 7.55/1.49  smt_new_axioms:                         0
% 7.55/1.49  pred_elim_cands:                        0
% 7.55/1.49  pred_elim:                              0
% 7.55/1.49  pred_elim_cl:                           0
% 7.55/1.49  pred_elim_cycles:                       0
% 7.55/1.49  merged_defs:                            0
% 7.55/1.49  merged_defs_ncl:                        0
% 7.55/1.49  bin_hyper_res:                          0
% 7.55/1.49  prep_cycles:                            2
% 7.55/1.49  pred_elim_time:                         0.
% 7.55/1.49  splitting_time:                         0.
% 7.55/1.49  sem_filter_time:                        0.
% 7.55/1.49  monotx_time:                            0.
% 7.55/1.49  subtype_inf_time:                       0.
% 7.55/1.49  
% 7.55/1.49  ------ Problem properties
% 7.55/1.49  
% 7.55/1.49  clauses:                                6
% 7.55/1.49  conjectures:                            1
% 7.55/1.49  epr:                                    0
% 7.55/1.49  horn:                                   6
% 7.55/1.49  ground:                                 1
% 7.55/1.49  unary:                                  6
% 7.55/1.49  binary:                                 0
% 7.55/1.49  lits:                                   6
% 7.55/1.49  lits_eq:                                6
% 7.55/1.49  fd_pure:                                0
% 7.55/1.49  fd_pseudo:                              0
% 7.55/1.49  fd_cond:                                0
% 7.55/1.49  fd_pseudo_cond:                         0
% 7.55/1.49  ac_symbols:                             0
% 7.55/1.49  
% 7.55/1.49  ------ Propositional Solver
% 7.55/1.49  
% 7.55/1.49  prop_solver_calls:                      13
% 7.55/1.49  prop_fast_solver_calls:                 44
% 7.55/1.49  smt_solver_calls:                       0
% 7.55/1.49  smt_fast_solver_calls:                  0
% 7.55/1.49  prop_num_of_clauses:                    221
% 7.55/1.49  prop_preprocess_simplified:             271
% 7.55/1.49  prop_fo_subsumed:                       0
% 7.55/1.49  prop_solver_time:                       0.
% 7.55/1.49  smt_solver_time:                        0.
% 7.55/1.49  smt_fast_solver_time:                   0.
% 7.55/1.49  prop_fast_solver_time:                  0.
% 7.55/1.49  prop_unsat_core_time:                   0.
% 7.55/1.49  
% 7.55/1.49  ------ QBF
% 7.55/1.49  
% 7.55/1.49  qbf_q_res:                              0
% 7.55/1.49  qbf_num_tautologies:                    0
% 7.55/1.49  qbf_prep_cycles:                        0
% 7.55/1.49  
% 7.55/1.49  ------ BMC1
% 7.55/1.49  
% 7.55/1.49  bmc1_current_bound:                     -1
% 7.55/1.49  bmc1_last_solved_bound:                 -1
% 7.55/1.49  bmc1_unsat_core_size:                   -1
% 7.55/1.49  bmc1_unsat_core_parents_size:           -1
% 7.55/1.49  bmc1_merge_next_fun:                    0
% 7.55/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.55/1.49  
% 7.55/1.49  ------ Instantiation
% 7.55/1.49  
% 7.55/1.49  inst_num_of_clauses:                    0
% 7.55/1.49  inst_num_in_passive:                    0
% 7.55/1.49  inst_num_in_active:                     0
% 7.55/1.49  inst_num_in_unprocessed:                0
% 7.55/1.49  inst_num_of_loops:                      0
% 7.55/1.49  inst_num_of_learning_restarts:          0
% 7.55/1.49  inst_num_moves_active_passive:          0
% 7.55/1.49  inst_lit_activity:                      0
% 7.55/1.49  inst_lit_activity_moves:                0
% 7.55/1.49  inst_num_tautologies:                   0
% 7.55/1.49  inst_num_prop_implied:                  0
% 7.55/1.49  inst_num_existing_simplified:           0
% 7.55/1.49  inst_num_eq_res_simplified:             0
% 7.55/1.49  inst_num_child_elim:                    0
% 7.55/1.49  inst_num_of_dismatching_blockings:      0
% 7.55/1.49  inst_num_of_non_proper_insts:           0
% 7.55/1.49  inst_num_of_duplicates:                 0
% 7.55/1.49  inst_inst_num_from_inst_to_res:         0
% 7.55/1.49  inst_dismatching_checking_time:         0.
% 7.55/1.49  
% 7.55/1.49  ------ Resolution
% 7.55/1.49  
% 7.55/1.49  res_num_of_clauses:                     0
% 7.55/1.49  res_num_in_passive:                     0
% 7.55/1.49  res_num_in_active:                      0
% 7.55/1.49  res_num_of_loops:                       18
% 7.55/1.49  res_forward_subset_subsumed:            0
% 7.55/1.49  res_backward_subset_subsumed:           0
% 7.55/1.49  res_forward_subsumed:                   0
% 7.55/1.49  res_backward_subsumed:                  0
% 7.55/1.49  res_forward_subsumption_resolution:     0
% 7.55/1.49  res_backward_subsumption_resolution:    0
% 7.55/1.49  res_clause_to_clause_subsumption:       100476
% 7.55/1.49  res_orphan_elimination:                 0
% 7.55/1.49  res_tautology_del:                      0
% 7.55/1.49  res_num_eq_res_simplified:              0
% 7.55/1.49  res_num_sel_changes:                    0
% 7.55/1.49  res_moves_from_active_to_pass:          0
% 7.55/1.49  
% 7.55/1.49  ------ Superposition
% 7.55/1.49  
% 7.55/1.49  sup_time_total:                         0.
% 7.55/1.49  sup_time_generating:                    0.
% 7.55/1.49  sup_time_sim_full:                      0.
% 7.55/1.49  sup_time_sim_immed:                     0.
% 7.55/1.49  
% 7.55/1.49  sup_num_of_clauses:                     2855
% 7.55/1.49  sup_num_in_active:                      126
% 7.55/1.49  sup_num_in_passive:                     2729
% 7.55/1.49  sup_num_of_loops:                       136
% 7.55/1.49  sup_fw_superposition:                   8521
% 7.55/1.49  sup_bw_superposition:                   7815
% 7.55/1.49  sup_immediate_simplified:               7604
% 7.55/1.49  sup_given_eliminated:                   2
% 7.55/1.49  comparisons_done:                       0
% 7.55/1.49  comparisons_avoided:                    0
% 7.55/1.49  
% 7.55/1.49  ------ Simplifications
% 7.55/1.49  
% 7.55/1.49  
% 7.55/1.49  sim_fw_subset_subsumed:                 0
% 7.55/1.49  sim_bw_subset_subsumed:                 0
% 7.55/1.49  sim_fw_subsumed:                        1902
% 7.55/1.49  sim_bw_subsumed:                        34
% 7.55/1.49  sim_fw_subsumption_res:                 0
% 7.55/1.49  sim_bw_subsumption_res:                 0
% 7.55/1.49  sim_tautology_del:                      0
% 7.55/1.49  sim_eq_tautology_del:                   1469
% 7.55/1.49  sim_eq_res_simp:                        0
% 7.55/1.49  sim_fw_demodulated:                     3995
% 7.55/1.49  sim_bw_demodulated:                     55
% 7.55/1.49  sim_light_normalised:                   2799
% 7.55/1.49  sim_joinable_taut:                      0
% 7.55/1.49  sim_joinable_simp:                      0
% 7.55/1.49  sim_ac_normalised:                      0
% 7.55/1.49  sim_smt_subsumption:                    0
% 7.55/1.49  
%------------------------------------------------------------------------------
