%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:54 EST 2020

% Result     : Theorem 27.88s
% Output     : CNFRefutation 27.88s
% Verified   : 
% Statistics : Number of formulae       :   46 (  82 expanded)
%              Number of clauses        :   26 (  38 expanded)
%              Number of leaves         :    9 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :   47 (  83 expanded)
%              Number of equality atoms :   46 (  82 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f13,conjecture,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f13])).

fof(f18,plain,(
    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,
    ( ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f33,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_4,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_5,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_684,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_4,c_5])).

cnf(c_10,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_716,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X0,k3_xboole_0(X0,X2)) ),
    inference(light_normalisation,[status(thm)],[c_684,c_10])).

cnf(c_717,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_716,c_4])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_210,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_4])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1042,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_210,c_8])).

cnf(c_2258,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_717,c_1042])).

cnf(c_9,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2279,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_2258,c_9])).

cnf(c_2,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_26130,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k3_xboole_0(X0,X1),X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(superposition,[status(thm)],[c_2279,c_2])).

cnf(c_26255,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X0)),k3_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(light_normalisation,[status(thm)],[c_26130,c_9])).

cnf(c_427,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X1,k3_xboole_0(k3_xboole_0(X0,X1),X2))) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_9,c_8])).

cnf(c_428,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X1,k3_xboole_0(k3_xboole_0(X0,X1),X2))) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_427,c_9])).

cnf(c_557,plain,
    ( k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X0,k4_xboole_0(X1,X3))) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    inference(superposition,[status(thm)],[c_9,c_2])).

cnf(c_577,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X2)),k3_xboole_0(X0,k4_xboole_0(X1,X3))) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    inference(light_normalisation,[status(thm)],[c_557,c_9])).

cnf(c_578,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X2)),k3_xboole_0(X0,k4_xboole_0(X1,X3))) = k3_xboole_0(X0,k4_xboole_0(X1,k3_xboole_0(X2,X3))) ),
    inference(demodulation,[status(thm)],[c_577,c_9])).

cnf(c_26256,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_26255,c_9,c_428,c_578])).

cnf(c_12,negated_conjecture,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_149,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK2))) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_12,c_9])).

cnf(c_74260,plain,
    ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_26256,c_149])).

cnf(c_74267,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_74260])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:17:44 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 27.88/3.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.88/3.99  
% 27.88/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.88/3.99  
% 27.88/3.99  ------  iProver source info
% 27.88/3.99  
% 27.88/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.88/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.88/3.99  git: non_committed_changes: false
% 27.88/3.99  git: last_make_outside_of_git: false
% 27.88/3.99  
% 27.88/3.99  ------ 
% 27.88/3.99  
% 27.88/3.99  ------ Input Options
% 27.88/3.99  
% 27.88/3.99  --out_options                           all
% 27.88/3.99  --tptp_safe_out                         true
% 27.88/3.99  --problem_path                          ""
% 27.88/3.99  --include_path                          ""
% 27.88/3.99  --clausifier                            res/vclausify_rel
% 27.88/3.99  --clausifier_options                    --mode clausify
% 27.88/3.99  --stdin                                 false
% 27.88/3.99  --stats_out                             sel
% 27.88/3.99  
% 27.88/3.99  ------ General Options
% 27.88/3.99  
% 27.88/3.99  --fof                                   false
% 27.88/3.99  --time_out_real                         604.99
% 27.88/3.99  --time_out_virtual                      -1.
% 27.88/3.99  --symbol_type_check                     false
% 27.88/3.99  --clausify_out                          false
% 27.88/3.99  --sig_cnt_out                           false
% 27.88/3.99  --trig_cnt_out                          false
% 27.88/3.99  --trig_cnt_out_tolerance                1.
% 27.88/3.99  --trig_cnt_out_sk_spl                   false
% 27.88/3.99  --abstr_cl_out                          false
% 27.88/3.99  
% 27.88/3.99  ------ Global Options
% 27.88/3.99  
% 27.88/3.99  --schedule                              none
% 27.88/3.99  --add_important_lit                     false
% 27.88/3.99  --prop_solver_per_cl                    1000
% 27.88/3.99  --min_unsat_core                        false
% 27.88/3.99  --soft_assumptions                      false
% 27.88/3.99  --soft_lemma_size                       3
% 27.88/3.99  --prop_impl_unit_size                   0
% 27.88/3.99  --prop_impl_unit                        []
% 27.88/3.99  --share_sel_clauses                     true
% 27.88/3.99  --reset_solvers                         false
% 27.88/3.99  --bc_imp_inh                            [conj_cone]
% 27.88/3.99  --conj_cone_tolerance                   3.
% 27.88/3.99  --extra_neg_conj                        none
% 27.88/3.99  --large_theory_mode                     true
% 27.88/3.99  --prolific_symb_bound                   200
% 27.88/3.99  --lt_threshold                          2000
% 27.88/3.99  --clause_weak_htbl                      true
% 27.88/3.99  --gc_record_bc_elim                     false
% 27.88/3.99  
% 27.88/3.99  ------ Preprocessing Options
% 27.88/3.99  
% 27.88/3.99  --preprocessing_flag                    true
% 27.88/3.99  --time_out_prep_mult                    0.1
% 27.88/3.99  --splitting_mode                        input
% 27.88/3.99  --splitting_grd                         true
% 27.88/3.99  --splitting_cvd                         false
% 27.88/3.99  --splitting_cvd_svl                     false
% 27.88/3.99  --splitting_nvd                         32
% 27.88/3.99  --sub_typing                            true
% 27.88/3.99  --prep_gs_sim                           false
% 27.88/3.99  --prep_unflatten                        true
% 27.88/3.99  --prep_res_sim                          true
% 27.88/3.99  --prep_upred                            true
% 27.88/3.99  --prep_sem_filter                       exhaustive
% 27.88/3.99  --prep_sem_filter_out                   false
% 27.88/3.99  --pred_elim                             false
% 27.88/3.99  --res_sim_input                         true
% 27.88/3.99  --eq_ax_congr_red                       true
% 27.88/3.99  --pure_diseq_elim                       true
% 27.88/3.99  --brand_transform                       false
% 27.88/3.99  --non_eq_to_eq                          false
% 27.88/3.99  --prep_def_merge                        true
% 27.88/3.99  --prep_def_merge_prop_impl              false
% 27.88/3.99  --prep_def_merge_mbd                    true
% 27.88/3.99  --prep_def_merge_tr_red                 false
% 27.88/3.99  --prep_def_merge_tr_cl                  false
% 27.88/3.99  --smt_preprocessing                     true
% 27.88/3.99  --smt_ac_axioms                         fast
% 27.88/3.99  --preprocessed_out                      false
% 27.88/3.99  --preprocessed_stats                    false
% 27.88/3.99  
% 27.88/3.99  ------ Abstraction refinement Options
% 27.88/3.99  
% 27.88/3.99  --abstr_ref                             []
% 27.88/3.99  --abstr_ref_prep                        false
% 27.88/3.99  --abstr_ref_until_sat                   false
% 27.88/3.99  --abstr_ref_sig_restrict                funpre
% 27.88/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.88/3.99  --abstr_ref_under                       []
% 27.88/3.99  
% 27.88/3.99  ------ SAT Options
% 27.88/3.99  
% 27.88/3.99  --sat_mode                              false
% 27.88/3.99  --sat_fm_restart_options                ""
% 27.88/3.99  --sat_gr_def                            false
% 27.88/3.99  --sat_epr_types                         true
% 27.88/3.99  --sat_non_cyclic_types                  false
% 27.88/3.99  --sat_finite_models                     false
% 27.88/3.99  --sat_fm_lemmas                         false
% 27.88/3.99  --sat_fm_prep                           false
% 27.88/3.99  --sat_fm_uc_incr                        true
% 27.88/3.99  --sat_out_model                         small
% 27.88/3.99  --sat_out_clauses                       false
% 27.88/3.99  
% 27.88/3.99  ------ QBF Options
% 27.88/3.99  
% 27.88/3.99  --qbf_mode                              false
% 27.88/3.99  --qbf_elim_univ                         false
% 27.88/3.99  --qbf_dom_inst                          none
% 27.88/3.99  --qbf_dom_pre_inst                      false
% 27.88/3.99  --qbf_sk_in                             false
% 27.88/3.99  --qbf_pred_elim                         true
% 27.88/3.99  --qbf_split                             512
% 27.88/3.99  
% 27.88/3.99  ------ BMC1 Options
% 27.88/3.99  
% 27.88/3.99  --bmc1_incremental                      false
% 27.88/3.99  --bmc1_axioms                           reachable_all
% 27.88/3.99  --bmc1_min_bound                        0
% 27.88/3.99  --bmc1_max_bound                        -1
% 27.88/3.99  --bmc1_max_bound_default                -1
% 27.88/3.99  --bmc1_symbol_reachability              true
% 27.88/3.99  --bmc1_property_lemmas                  false
% 27.88/3.99  --bmc1_k_induction                      false
% 27.88/3.99  --bmc1_non_equiv_states                 false
% 27.88/3.99  --bmc1_deadlock                         false
% 27.88/3.99  --bmc1_ucm                              false
% 27.88/3.99  --bmc1_add_unsat_core                   none
% 27.88/3.99  --bmc1_unsat_core_children              false
% 27.88/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.88/3.99  --bmc1_out_stat                         full
% 27.88/3.99  --bmc1_ground_init                      false
% 27.88/3.99  --bmc1_pre_inst_next_state              false
% 27.88/3.99  --bmc1_pre_inst_state                   false
% 27.88/3.99  --bmc1_pre_inst_reach_state             false
% 27.88/3.99  --bmc1_out_unsat_core                   false
% 27.88/3.99  --bmc1_aig_witness_out                  false
% 27.88/3.99  --bmc1_verbose                          false
% 27.88/3.99  --bmc1_dump_clauses_tptp                false
% 27.88/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.88/3.99  --bmc1_dump_file                        -
% 27.88/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.88/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.88/3.99  --bmc1_ucm_extend_mode                  1
% 27.88/3.99  --bmc1_ucm_init_mode                    2
% 27.88/3.99  --bmc1_ucm_cone_mode                    none
% 27.88/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.88/3.99  --bmc1_ucm_relax_model                  4
% 27.88/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.88/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.88/3.99  --bmc1_ucm_layered_model                none
% 27.88/3.99  --bmc1_ucm_max_lemma_size               10
% 27.88/3.99  
% 27.88/3.99  ------ AIG Options
% 27.88/3.99  
% 27.88/3.99  --aig_mode                              false
% 27.88/3.99  
% 27.88/3.99  ------ Instantiation Options
% 27.88/3.99  
% 27.88/3.99  --instantiation_flag                    true
% 27.88/3.99  --inst_sos_flag                         false
% 27.88/3.99  --inst_sos_phase                        true
% 27.88/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.88/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.88/3.99  --inst_lit_sel_side                     num_symb
% 27.88/3.99  --inst_solver_per_active                1400
% 27.88/3.99  --inst_solver_calls_frac                1.
% 27.88/3.99  --inst_passive_queue_type               priority_queues
% 27.88/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.88/3.99  --inst_passive_queues_freq              [25;2]
% 27.88/3.99  --inst_dismatching                      true
% 27.88/3.99  --inst_eager_unprocessed_to_passive     true
% 27.88/3.99  --inst_prop_sim_given                   true
% 27.88/3.99  --inst_prop_sim_new                     false
% 27.88/3.99  --inst_subs_new                         false
% 27.88/3.99  --inst_eq_res_simp                      false
% 27.88/3.99  --inst_subs_given                       false
% 27.88/3.99  --inst_orphan_elimination               true
% 27.88/3.99  --inst_learning_loop_flag               true
% 27.88/3.99  --inst_learning_start                   3000
% 27.88/3.99  --inst_learning_factor                  2
% 27.88/3.99  --inst_start_prop_sim_after_learn       3
% 27.88/3.99  --inst_sel_renew                        solver
% 27.88/3.99  --inst_lit_activity_flag                true
% 27.88/3.99  --inst_restr_to_given                   false
% 27.88/3.99  --inst_activity_threshold               500
% 27.88/3.99  --inst_out_proof                        true
% 27.88/3.99  
% 27.88/3.99  ------ Resolution Options
% 27.88/3.99  
% 27.88/3.99  --resolution_flag                       true
% 27.88/3.99  --res_lit_sel                           adaptive
% 27.88/3.99  --res_lit_sel_side                      none
% 27.88/3.99  --res_ordering                          kbo
% 27.88/3.99  --res_to_prop_solver                    active
% 27.88/3.99  --res_prop_simpl_new                    false
% 27.88/3.99  --res_prop_simpl_given                  true
% 27.88/3.99  --res_passive_queue_type                priority_queues
% 27.88/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.88/3.99  --res_passive_queues_freq               [15;5]
% 27.88/3.99  --res_forward_subs                      full
% 27.88/3.99  --res_backward_subs                     full
% 27.88/3.99  --res_forward_subs_resolution           true
% 27.88/3.99  --res_backward_subs_resolution          true
% 27.88/3.99  --res_orphan_elimination                true
% 27.88/3.99  --res_time_limit                        2.
% 27.88/3.99  --res_out_proof                         true
% 27.88/3.99  
% 27.88/3.99  ------ Superposition Options
% 27.88/3.99  
% 27.88/3.99  --superposition_flag                    true
% 27.88/3.99  --sup_passive_queue_type                priority_queues
% 27.88/3.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.88/3.99  --sup_passive_queues_freq               [1;4]
% 27.88/3.99  --demod_completeness_check              fast
% 27.88/3.99  --demod_use_ground                      true
% 27.88/3.99  --sup_to_prop_solver                    passive
% 27.88/3.99  --sup_prop_simpl_new                    true
% 27.88/3.99  --sup_prop_simpl_given                  true
% 27.88/3.99  --sup_fun_splitting                     false
% 27.88/3.99  --sup_smt_interval                      50000
% 27.88/3.99  
% 27.88/3.99  ------ Superposition Simplification Setup
% 27.88/3.99  
% 27.88/3.99  --sup_indices_passive                   []
% 27.88/3.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.88/3.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.88/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.88/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.88/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.88/3.99  --sup_full_bw                           [BwDemod]
% 27.88/3.99  --sup_immed_triv                        [TrivRules]
% 27.88/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.88/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.88/3.99  --sup_immed_bw_main                     []
% 27.88/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.88/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.88/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.88/3.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.88/3.99  
% 27.88/3.99  ------ Combination Options
% 27.88/3.99  
% 27.88/3.99  --comb_res_mult                         3
% 27.88/3.99  --comb_sup_mult                         2
% 27.88/3.99  --comb_inst_mult                        10
% 27.88/3.99  
% 27.88/3.99  ------ Debug Options
% 27.88/3.99  
% 27.88/3.99  --dbg_backtrace                         false
% 27.88/3.99  --dbg_dump_prop_clauses                 false
% 27.88/3.99  --dbg_dump_prop_clauses_file            -
% 27.88/3.99  --dbg_out_stat                          false
% 27.88/3.99  ------ Parsing...
% 27.88/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.88/3.99  
% 27.88/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 27.88/3.99  
% 27.88/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.88/3.99  
% 27.88/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.88/3.99  ------ Proving...
% 27.88/3.99  ------ Problem Properties 
% 27.88/3.99  
% 27.88/3.99  
% 27.88/3.99  clauses                                 13
% 27.88/3.99  conjectures                             1
% 27.88/3.99  EPR                                     0
% 27.88/3.99  Horn                                    13
% 27.88/3.99  unary                                   11
% 27.88/3.99  binary                                  2
% 27.88/3.99  lits                                    15
% 27.88/3.99  lits eq                                 11
% 27.88/3.99  fd_pure                                 0
% 27.88/3.99  fd_pseudo                               0
% 27.88/3.99  fd_cond                                 0
% 27.88/3.99  fd_pseudo_cond                          0
% 27.88/3.99  AC symbols                              1
% 27.88/3.99  
% 27.88/3.99  ------ Input Options Time Limit: Unbounded
% 27.88/3.99  
% 27.88/3.99  
% 27.88/3.99  ------ 
% 27.88/3.99  Current options:
% 27.88/3.99  ------ 
% 27.88/3.99  
% 27.88/3.99  ------ Input Options
% 27.88/3.99  
% 27.88/3.99  --out_options                           all
% 27.88/3.99  --tptp_safe_out                         true
% 27.88/3.99  --problem_path                          ""
% 27.88/3.99  --include_path                          ""
% 27.88/3.99  --clausifier                            res/vclausify_rel
% 27.88/3.99  --clausifier_options                    --mode clausify
% 27.88/3.99  --stdin                                 false
% 27.88/3.99  --stats_out                             sel
% 27.88/3.99  
% 27.88/3.99  ------ General Options
% 27.88/3.99  
% 27.88/3.99  --fof                                   false
% 27.88/3.99  --time_out_real                         604.99
% 27.88/3.99  --time_out_virtual                      -1.
% 27.88/3.99  --symbol_type_check                     false
% 27.88/3.99  --clausify_out                          false
% 27.88/3.99  --sig_cnt_out                           false
% 27.88/3.99  --trig_cnt_out                          false
% 27.88/3.99  --trig_cnt_out_tolerance                1.
% 27.88/3.99  --trig_cnt_out_sk_spl                   false
% 27.88/3.99  --abstr_cl_out                          false
% 27.88/3.99  
% 27.88/3.99  ------ Global Options
% 27.88/3.99  
% 27.88/3.99  --schedule                              none
% 27.88/3.99  --add_important_lit                     false
% 27.88/3.99  --prop_solver_per_cl                    1000
% 27.88/3.99  --min_unsat_core                        false
% 27.88/3.99  --soft_assumptions                      false
% 27.88/3.99  --soft_lemma_size                       3
% 27.88/3.99  --prop_impl_unit_size                   0
% 27.88/3.99  --prop_impl_unit                        []
% 27.88/3.99  --share_sel_clauses                     true
% 27.88/3.99  --reset_solvers                         false
% 27.88/3.99  --bc_imp_inh                            [conj_cone]
% 27.88/3.99  --conj_cone_tolerance                   3.
% 27.88/3.99  --extra_neg_conj                        none
% 27.88/3.99  --large_theory_mode                     true
% 27.88/3.99  --prolific_symb_bound                   200
% 27.88/3.99  --lt_threshold                          2000
% 27.88/3.99  --clause_weak_htbl                      true
% 27.88/3.99  --gc_record_bc_elim                     false
% 27.88/3.99  
% 27.88/3.99  ------ Preprocessing Options
% 27.88/3.99  
% 27.88/3.99  --preprocessing_flag                    true
% 27.88/3.99  --time_out_prep_mult                    0.1
% 27.88/3.99  --splitting_mode                        input
% 27.88/3.99  --splitting_grd                         true
% 27.88/3.99  --splitting_cvd                         false
% 27.88/3.99  --splitting_cvd_svl                     false
% 27.88/3.99  --splitting_nvd                         32
% 27.88/3.99  --sub_typing                            true
% 27.88/3.99  --prep_gs_sim                           false
% 27.88/3.99  --prep_unflatten                        true
% 27.88/3.99  --prep_res_sim                          true
% 27.88/3.99  --prep_upred                            true
% 27.88/3.99  --prep_sem_filter                       exhaustive
% 27.88/3.99  --prep_sem_filter_out                   false
% 27.88/3.99  --pred_elim                             false
% 27.88/3.99  --res_sim_input                         true
% 27.88/3.99  --eq_ax_congr_red                       true
% 27.88/3.99  --pure_diseq_elim                       true
% 27.88/3.99  --brand_transform                       false
% 27.88/3.99  --non_eq_to_eq                          false
% 27.88/3.99  --prep_def_merge                        true
% 27.88/3.99  --prep_def_merge_prop_impl              false
% 27.88/3.99  --prep_def_merge_mbd                    true
% 27.88/3.99  --prep_def_merge_tr_red                 false
% 27.88/3.99  --prep_def_merge_tr_cl                  false
% 27.88/3.99  --smt_preprocessing                     true
% 27.88/3.99  --smt_ac_axioms                         fast
% 27.88/3.99  --preprocessed_out                      false
% 27.88/3.99  --preprocessed_stats                    false
% 27.88/3.99  
% 27.88/3.99  ------ Abstraction refinement Options
% 27.88/3.99  
% 27.88/3.99  --abstr_ref                             []
% 27.88/3.99  --abstr_ref_prep                        false
% 27.88/3.99  --abstr_ref_until_sat                   false
% 27.88/3.99  --abstr_ref_sig_restrict                funpre
% 27.88/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.88/3.99  --abstr_ref_under                       []
% 27.88/3.99  
% 27.88/3.99  ------ SAT Options
% 27.88/3.99  
% 27.88/3.99  --sat_mode                              false
% 27.88/3.99  --sat_fm_restart_options                ""
% 27.88/3.99  --sat_gr_def                            false
% 27.88/3.99  --sat_epr_types                         true
% 27.88/3.99  --sat_non_cyclic_types                  false
% 27.88/3.99  --sat_finite_models                     false
% 27.88/3.99  --sat_fm_lemmas                         false
% 27.88/3.99  --sat_fm_prep                           false
% 27.88/3.99  --sat_fm_uc_incr                        true
% 27.88/3.99  --sat_out_model                         small
% 27.88/3.99  --sat_out_clauses                       false
% 27.88/3.99  
% 27.88/3.99  ------ QBF Options
% 27.88/3.99  
% 27.88/3.99  --qbf_mode                              false
% 27.88/3.99  --qbf_elim_univ                         false
% 27.88/3.99  --qbf_dom_inst                          none
% 27.88/3.99  --qbf_dom_pre_inst                      false
% 27.88/3.99  --qbf_sk_in                             false
% 27.88/3.99  --qbf_pred_elim                         true
% 27.88/3.99  --qbf_split                             512
% 27.88/3.99  
% 27.88/3.99  ------ BMC1 Options
% 27.88/3.99  
% 27.88/3.99  --bmc1_incremental                      false
% 27.88/3.99  --bmc1_axioms                           reachable_all
% 27.88/3.99  --bmc1_min_bound                        0
% 27.88/3.99  --bmc1_max_bound                        -1
% 27.88/3.99  --bmc1_max_bound_default                -1
% 27.88/3.99  --bmc1_symbol_reachability              true
% 27.88/3.99  --bmc1_property_lemmas                  false
% 27.88/3.99  --bmc1_k_induction                      false
% 27.88/3.99  --bmc1_non_equiv_states                 false
% 27.88/3.99  --bmc1_deadlock                         false
% 27.88/3.99  --bmc1_ucm                              false
% 27.88/3.99  --bmc1_add_unsat_core                   none
% 27.88/3.99  --bmc1_unsat_core_children              false
% 27.88/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.88/3.99  --bmc1_out_stat                         full
% 27.88/3.99  --bmc1_ground_init                      false
% 27.88/3.99  --bmc1_pre_inst_next_state              false
% 27.88/3.99  --bmc1_pre_inst_state                   false
% 27.88/3.99  --bmc1_pre_inst_reach_state             false
% 27.88/3.99  --bmc1_out_unsat_core                   false
% 27.88/3.99  --bmc1_aig_witness_out                  false
% 27.88/3.99  --bmc1_verbose                          false
% 27.88/3.99  --bmc1_dump_clauses_tptp                false
% 27.88/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.88/3.99  --bmc1_dump_file                        -
% 27.88/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.88/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.88/3.99  --bmc1_ucm_extend_mode                  1
% 27.88/3.99  --bmc1_ucm_init_mode                    2
% 27.88/3.99  --bmc1_ucm_cone_mode                    none
% 27.88/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.88/3.99  --bmc1_ucm_relax_model                  4
% 27.88/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.88/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.88/3.99  --bmc1_ucm_layered_model                none
% 27.88/3.99  --bmc1_ucm_max_lemma_size               10
% 27.88/3.99  
% 27.88/3.99  ------ AIG Options
% 27.88/3.99  
% 27.88/3.99  --aig_mode                              false
% 27.88/3.99  
% 27.88/3.99  ------ Instantiation Options
% 27.88/3.99  
% 27.88/3.99  --instantiation_flag                    true
% 27.88/3.99  --inst_sos_flag                         false
% 27.88/3.99  --inst_sos_phase                        true
% 27.88/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.88/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.88/3.99  --inst_lit_sel_side                     num_symb
% 27.88/3.99  --inst_solver_per_active                1400
% 27.88/3.99  --inst_solver_calls_frac                1.
% 27.88/3.99  --inst_passive_queue_type               priority_queues
% 27.88/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.88/3.99  --inst_passive_queues_freq              [25;2]
% 27.88/3.99  --inst_dismatching                      true
% 27.88/3.99  --inst_eager_unprocessed_to_passive     true
% 27.88/3.99  --inst_prop_sim_given                   true
% 27.88/3.99  --inst_prop_sim_new                     false
% 27.88/3.99  --inst_subs_new                         false
% 27.88/3.99  --inst_eq_res_simp                      false
% 27.88/3.99  --inst_subs_given                       false
% 27.88/3.99  --inst_orphan_elimination               true
% 27.88/3.99  --inst_learning_loop_flag               true
% 27.88/3.99  --inst_learning_start                   3000
% 27.88/3.99  --inst_learning_factor                  2
% 27.88/3.99  --inst_start_prop_sim_after_learn       3
% 27.88/3.99  --inst_sel_renew                        solver
% 27.88/3.99  --inst_lit_activity_flag                true
% 27.88/3.99  --inst_restr_to_given                   false
% 27.88/3.99  --inst_activity_threshold               500
% 27.88/3.99  --inst_out_proof                        true
% 27.88/3.99  
% 27.88/3.99  ------ Resolution Options
% 27.88/3.99  
% 27.88/3.99  --resolution_flag                       true
% 27.88/3.99  --res_lit_sel                           adaptive
% 27.88/3.99  --res_lit_sel_side                      none
% 27.88/3.99  --res_ordering                          kbo
% 27.88/3.99  --res_to_prop_solver                    active
% 27.88/3.99  --res_prop_simpl_new                    false
% 27.88/3.99  --res_prop_simpl_given                  true
% 27.88/3.99  --res_passive_queue_type                priority_queues
% 27.88/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.88/3.99  --res_passive_queues_freq               [15;5]
% 27.88/3.99  --res_forward_subs                      full
% 27.88/3.99  --res_backward_subs                     full
% 27.88/3.99  --res_forward_subs_resolution           true
% 27.88/3.99  --res_backward_subs_resolution          true
% 27.88/3.99  --res_orphan_elimination                true
% 27.88/3.99  --res_time_limit                        2.
% 27.88/3.99  --res_out_proof                         true
% 27.88/3.99  
% 27.88/3.99  ------ Superposition Options
% 27.88/3.99  
% 27.88/3.99  --superposition_flag                    true
% 27.88/3.99  --sup_passive_queue_type                priority_queues
% 27.88/3.99  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.88/3.99  --sup_passive_queues_freq               [1;4]
% 27.88/3.99  --demod_completeness_check              fast
% 27.88/3.99  --demod_use_ground                      true
% 27.88/3.99  --sup_to_prop_solver                    passive
% 27.88/3.99  --sup_prop_simpl_new                    true
% 27.88/3.99  --sup_prop_simpl_given                  true
% 27.88/3.99  --sup_fun_splitting                     false
% 27.88/3.99  --sup_smt_interval                      50000
% 27.88/3.99  
% 27.88/3.99  ------ Superposition Simplification Setup
% 27.88/3.99  
% 27.88/3.99  --sup_indices_passive                   []
% 27.88/3.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.88/3.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.88/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.88/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.88/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.88/3.99  --sup_full_bw                           [BwDemod]
% 27.88/3.99  --sup_immed_triv                        [TrivRules]
% 27.88/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.88/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.88/3.99  --sup_immed_bw_main                     []
% 27.88/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.88/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.88/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.88/3.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.88/3.99  
% 27.88/3.99  ------ Combination Options
% 27.88/3.99  
% 27.88/3.99  --comb_res_mult                         3
% 27.88/3.99  --comb_sup_mult                         2
% 27.88/3.99  --comb_inst_mult                        10
% 27.88/3.99  
% 27.88/3.99  ------ Debug Options
% 27.88/3.99  
% 27.88/3.99  --dbg_backtrace                         false
% 27.88/3.99  --dbg_dump_prop_clauses                 false
% 27.88/3.99  --dbg_dump_prop_clauses_file            -
% 27.88/3.99  --dbg_out_stat                          false
% 27.88/3.99  
% 27.88/3.99  
% 27.88/3.99  
% 27.88/3.99  
% 27.88/3.99  ------ Proving...
% 27.88/3.99  
% 27.88/3.99  
% 27.88/3.99  % SZS status Theorem for theBenchmark.p
% 27.88/3.99  
% 27.88/3.99   Resolution empty clause
% 27.88/3.99  
% 27.88/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.88/3.99  
% 27.88/3.99  fof(f5,axiom,(
% 27.88/3.99    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f25,plain,(
% 27.88/3.99    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 27.88/3.99    inference(cnf_transformation,[],[f5])).
% 27.88/3.99  
% 27.88/3.99  fof(f6,axiom,(
% 27.88/3.99    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f26,plain,(
% 27.88/3.99    ( ! [X2,X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 27.88/3.99    inference(cnf_transformation,[],[f6])).
% 27.88/3.99  
% 27.88/3.99  fof(f11,axiom,(
% 27.88/3.99    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f31,plain,(
% 27.88/3.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f11])).
% 27.88/3.99  
% 27.88/3.99  fof(f1,axiom,(
% 27.88/3.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f21,plain,(
% 27.88/3.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f1])).
% 27.88/3.99  
% 27.88/3.99  fof(f9,axiom,(
% 27.88/3.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f29,plain,(
% 27.88/3.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.88/3.99    inference(cnf_transformation,[],[f9])).
% 27.88/3.99  
% 27.88/3.99  fof(f10,axiom,(
% 27.88/3.99    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f30,plain,(
% 27.88/3.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 27.88/3.99    inference(cnf_transformation,[],[f10])).
% 27.88/3.99  
% 27.88/3.99  fof(f3,axiom,(
% 27.88/3.99    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2))),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f23,plain,(
% 27.88/3.99    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 27.88/3.99    inference(cnf_transformation,[],[f3])).
% 27.88/3.99  
% 27.88/3.99  fof(f13,conjecture,(
% 27.88/3.99    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 27.88/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.88/3.99  
% 27.88/3.99  fof(f14,negated_conjecture,(
% 27.88/3.99    ~! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 27.88/3.99    inference(negated_conjecture,[],[f13])).
% 27.88/3.99  
% 27.88/3.99  fof(f18,plain,(
% 27.88/3.99    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 27.88/3.99    inference(ennf_transformation,[],[f14])).
% 27.88/3.99  
% 27.88/3.99  fof(f19,plain,(
% 27.88/3.99    ? [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) != k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) => k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 27.88/3.99    introduced(choice_axiom,[])).
% 27.88/3.99  
% 27.88/3.99  fof(f20,plain,(
% 27.88/3.99    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 27.88/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 27.88/3.99  
% 27.88/3.99  fof(f33,plain,(
% 27.88/3.99    k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 27.88/3.99    inference(cnf_transformation,[],[f20])).
% 27.88/3.99  
% 27.88/3.99  cnf(c_4,plain,
% 27.88/3.99      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 27.88/3.99      inference(cnf_transformation,[],[f25]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_5,plain,
% 27.88/3.99      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.88/3.99      inference(cnf_transformation,[],[f26]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_684,plain,
% 27.88/3.99      ( k3_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(X0,k3_xboole_0(X0,X2)) ),
% 27.88/3.99      inference(superposition,[status(thm)],[c_4,c_5]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_10,plain,
% 27.88/3.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 27.88/3.99      inference(cnf_transformation,[],[f31]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_716,plain,
% 27.88/3.99      ( k3_xboole_0(X0,k2_xboole_0(X0,k2_xboole_0(X1,X2))) = k2_xboole_0(X0,k3_xboole_0(X0,X2)) ),
% 27.88/3.99      inference(light_normalisation,[status(thm)],[c_684,c_10]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_717,plain,
% 27.88/3.99      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 27.88/3.99      inference(demodulation,[status(thm)],[c_716,c_4]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_0,plain,
% 27.88/3.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 27.88/3.99      inference(cnf_transformation,[],[f21]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_210,plain,
% 27.88/3.99      ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
% 27.88/3.99      inference(superposition,[status(thm)],[c_0,c_4]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_8,plain,
% 27.88/3.99      ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 27.88/3.99      inference(cnf_transformation,[],[f29]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_1042,plain,
% 27.88/3.99      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(X0,X0) ),
% 27.88/3.99      inference(superposition,[status(thm)],[c_210,c_8]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_2258,plain,
% 27.88/3.99      ( k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 27.88/3.99      inference(superposition,[status(thm)],[c_717,c_1042]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_9,plain,
% 27.88/3.99      ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 27.88/3.99      inference(cnf_transformation,[],[f30]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_2279,plain,
% 27.88/3.99      ( k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 27.88/3.99      inference(demodulation,[status(thm)],[c_2258,c_9]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_2,plain,
% 27.88/3.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 27.88/3.99      inference(cnf_transformation,[],[f23]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_26130,plain,
% 27.88/3.99      ( k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(k3_xboole_0(X0,X1),X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
% 27.88/3.99      inference(superposition,[status(thm)],[c_2279,c_2]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_26255,plain,
% 27.88/3.99      ( k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X0)),k3_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
% 27.88/3.99      inference(light_normalisation,[status(thm)],[c_26130,c_9]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_427,plain,
% 27.88/3.99      ( k3_xboole_0(X0,k4_xboole_0(X1,k3_xboole_0(k3_xboole_0(X0,X1),X2))) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
% 27.88/3.99      inference(superposition,[status(thm)],[c_9,c_8]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_428,plain,
% 27.88/3.99      ( k3_xboole_0(X0,k4_xboole_0(X1,k3_xboole_0(k3_xboole_0(X0,X1),X2))) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 27.88/3.99      inference(light_normalisation,[status(thm)],[c_427,c_9]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_557,plain,
% 27.88/3.99      ( k2_xboole_0(k4_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(X0,k4_xboole_0(X1,X3))) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
% 27.88/3.99      inference(superposition,[status(thm)],[c_9,c_2]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_577,plain,
% 27.88/3.99      ( k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X2)),k3_xboole_0(X0,k4_xboole_0(X1,X3))) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
% 27.88/3.99      inference(light_normalisation,[status(thm)],[c_557,c_9]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_578,plain,
% 27.88/3.99      ( k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X2)),k3_xboole_0(X0,k4_xboole_0(X1,X3))) = k3_xboole_0(X0,k4_xboole_0(X1,k3_xboole_0(X2,X3))) ),
% 27.88/3.99      inference(demodulation,[status(thm)],[c_577,c_9]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_26256,plain,
% 27.88/3.99      ( k3_xboole_0(X0,k4_xboole_0(X1,k3_xboole_0(X0,X2))) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 27.88/3.99      inference(demodulation,[status(thm)],[c_26255,c_9,c_428,c_578]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_12,negated_conjecture,
% 27.88/3.99      ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
% 27.88/3.99      inference(cnf_transformation,[],[f33]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_149,plain,
% 27.88/3.99      ( k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK2))) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 27.88/3.99      inference(demodulation,[status(thm)],[c_12,c_9]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_74260,plain,
% 27.88/3.99      ( k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 27.88/3.99      inference(demodulation,[status(thm)],[c_26256,c_149]) ).
% 27.88/3.99  
% 27.88/3.99  cnf(c_74267,plain,
% 27.88/3.99      ( $false ),
% 27.88/3.99      inference(equality_resolution_simp,[status(thm)],[c_74260]) ).
% 27.88/3.99  
% 27.88/3.99  
% 27.88/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 27.88/3.99  
% 27.88/3.99  ------                               Statistics
% 27.88/3.99  
% 27.88/3.99  ------ Selected
% 27.88/3.99  
% 27.88/3.99  total_time:                             3.257
% 27.88/3.99  
%------------------------------------------------------------------------------
