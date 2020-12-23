%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:17 EST 2020

% Result     : Theorem 12.04s
% Output     : CNFRefutation 12.04s
% Verified   : 
% Statistics : Number of formulae       :   53 (  90 expanded)
%              Number of clauses        :   26 (  42 expanded)
%              Number of leaves         :   11 (  20 expanded)
%              Depth                    :   13
%              Number of atoms          :   66 ( 122 expanded)
%              Number of equality atoms :   49 (  81 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f22])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f10])).

fof(f13,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f11])).

fof(f15,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15])).

fof(f27,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_5,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_223,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_224,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_51158,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_223,c_224])).

cnf(c_7,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_221,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_53558,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_51158,c_221])).

cnf(c_471,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_223,c_221])).

cnf(c_8,plain,
    ( k2_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_752,plain,
    ( k2_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_471,c_8])).

cnf(c_3,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_758,plain,
    ( k2_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(demodulation,[status(thm)],[c_752,c_3])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_302,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_484,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_302])).

cnf(c_485,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_484,c_2])).

cnf(c_759,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(demodulation,[status(thm)],[c_758,c_1,c_2,c_485])).

cnf(c_54951,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_53558,c_759])).

cnf(c_55000,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_54951,c_53558])).

cnf(c_55001,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_55000,c_2])).

cnf(c_9,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_56551,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_55001,c_9])).

cnf(c_56554,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_56551])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:26:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 12.04/1.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.04/1.99  
% 12.04/1.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 12.04/1.99  
% 12.04/1.99  ------  iProver source info
% 12.04/1.99  
% 12.04/1.99  git: date: 2020-06-30 10:37:57 +0100
% 12.04/1.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 12.04/1.99  git: non_committed_changes: false
% 12.04/1.99  git: last_make_outside_of_git: false
% 12.04/1.99  
% 12.04/1.99  ------ 
% 12.04/1.99  
% 12.04/1.99  ------ Input Options
% 12.04/1.99  
% 12.04/1.99  --out_options                           all
% 12.04/1.99  --tptp_safe_out                         true
% 12.04/1.99  --problem_path                          ""
% 12.04/1.99  --include_path                          ""
% 12.04/1.99  --clausifier                            res/vclausify_rel
% 12.04/1.99  --clausifier_options                    ""
% 12.04/1.99  --stdin                                 false
% 12.04/1.99  --stats_out                             all
% 12.04/1.99  
% 12.04/1.99  ------ General Options
% 12.04/1.99  
% 12.04/1.99  --fof                                   false
% 12.04/1.99  --time_out_real                         305.
% 12.04/1.99  --time_out_virtual                      -1.
% 12.04/1.99  --symbol_type_check                     false
% 12.04/1.99  --clausify_out                          false
% 12.04/1.99  --sig_cnt_out                           false
% 12.04/1.99  --trig_cnt_out                          false
% 12.04/1.99  --trig_cnt_out_tolerance                1.
% 12.04/1.99  --trig_cnt_out_sk_spl                   false
% 12.04/1.99  --abstr_cl_out                          false
% 12.04/1.99  
% 12.04/1.99  ------ Global Options
% 12.04/1.99  
% 12.04/1.99  --schedule                              default
% 12.04/1.99  --add_important_lit                     false
% 12.04/1.99  --prop_solver_per_cl                    1000
% 12.04/1.99  --min_unsat_core                        false
% 12.04/1.99  --soft_assumptions                      false
% 12.04/1.99  --soft_lemma_size                       3
% 12.04/1.99  --prop_impl_unit_size                   0
% 12.04/1.99  --prop_impl_unit                        []
% 12.04/1.99  --share_sel_clauses                     true
% 12.04/1.99  --reset_solvers                         false
% 12.04/1.99  --bc_imp_inh                            [conj_cone]
% 12.04/1.99  --conj_cone_tolerance                   3.
% 12.04/1.99  --extra_neg_conj                        none
% 12.04/1.99  --large_theory_mode                     true
% 12.04/1.99  --prolific_symb_bound                   200
% 12.04/1.99  --lt_threshold                          2000
% 12.04/1.99  --clause_weak_htbl                      true
% 12.04/1.99  --gc_record_bc_elim                     false
% 12.04/1.99  
% 12.04/1.99  ------ Preprocessing Options
% 12.04/1.99  
% 12.04/1.99  --preprocessing_flag                    true
% 12.04/1.99  --time_out_prep_mult                    0.1
% 12.04/1.99  --splitting_mode                        input
% 12.04/1.99  --splitting_grd                         true
% 12.04/1.99  --splitting_cvd                         false
% 12.04/1.99  --splitting_cvd_svl                     false
% 12.04/1.99  --splitting_nvd                         32
% 12.04/1.99  --sub_typing                            true
% 12.04/1.99  --prep_gs_sim                           true
% 12.04/1.99  --prep_unflatten                        true
% 12.04/1.99  --prep_res_sim                          true
% 12.04/1.99  --prep_upred                            true
% 12.04/1.99  --prep_sem_filter                       exhaustive
% 12.04/1.99  --prep_sem_filter_out                   false
% 12.04/1.99  --pred_elim                             true
% 12.04/1.99  --res_sim_input                         true
% 12.04/1.99  --eq_ax_congr_red                       true
% 12.04/1.99  --pure_diseq_elim                       true
% 12.04/1.99  --brand_transform                       false
% 12.04/1.99  --non_eq_to_eq                          false
% 12.04/1.99  --prep_def_merge                        true
% 12.04/1.99  --prep_def_merge_prop_impl              false
% 12.04/1.99  --prep_def_merge_mbd                    true
% 12.04/1.99  --prep_def_merge_tr_red                 false
% 12.04/1.99  --prep_def_merge_tr_cl                  false
% 12.04/1.99  --smt_preprocessing                     true
% 12.04/1.99  --smt_ac_axioms                         fast
% 12.04/1.99  --preprocessed_out                      false
% 12.04/1.99  --preprocessed_stats                    false
% 12.04/1.99  
% 12.04/1.99  ------ Abstraction refinement Options
% 12.04/1.99  
% 12.04/1.99  --abstr_ref                             []
% 12.04/1.99  --abstr_ref_prep                        false
% 12.04/1.99  --abstr_ref_until_sat                   false
% 12.04/1.99  --abstr_ref_sig_restrict                funpre
% 12.04/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 12.04/1.99  --abstr_ref_under                       []
% 12.04/1.99  
% 12.04/1.99  ------ SAT Options
% 12.04/1.99  
% 12.04/1.99  --sat_mode                              false
% 12.04/1.99  --sat_fm_restart_options                ""
% 12.04/1.99  --sat_gr_def                            false
% 12.04/1.99  --sat_epr_types                         true
% 12.04/1.99  --sat_non_cyclic_types                  false
% 12.04/1.99  --sat_finite_models                     false
% 12.04/1.99  --sat_fm_lemmas                         false
% 12.04/1.99  --sat_fm_prep                           false
% 12.04/1.99  --sat_fm_uc_incr                        true
% 12.04/1.99  --sat_out_model                         small
% 12.04/1.99  --sat_out_clauses                       false
% 12.04/1.99  
% 12.04/1.99  ------ QBF Options
% 12.04/1.99  
% 12.04/1.99  --qbf_mode                              false
% 12.04/1.99  --qbf_elim_univ                         false
% 12.04/1.99  --qbf_dom_inst                          none
% 12.04/1.99  --qbf_dom_pre_inst                      false
% 12.04/1.99  --qbf_sk_in                             false
% 12.04/1.99  --qbf_pred_elim                         true
% 12.04/1.99  --qbf_split                             512
% 12.04/1.99  
% 12.04/1.99  ------ BMC1 Options
% 12.04/1.99  
% 12.04/1.99  --bmc1_incremental                      false
% 12.04/1.99  --bmc1_axioms                           reachable_all
% 12.04/1.99  --bmc1_min_bound                        0
% 12.04/1.99  --bmc1_max_bound                        -1
% 12.04/1.99  --bmc1_max_bound_default                -1
% 12.04/1.99  --bmc1_symbol_reachability              true
% 12.04/1.99  --bmc1_property_lemmas                  false
% 12.04/1.99  --bmc1_k_induction                      false
% 12.04/1.99  --bmc1_non_equiv_states                 false
% 12.04/1.99  --bmc1_deadlock                         false
% 12.04/1.99  --bmc1_ucm                              false
% 12.04/1.99  --bmc1_add_unsat_core                   none
% 12.04/1.99  --bmc1_unsat_core_children              false
% 12.04/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 12.04/1.99  --bmc1_out_stat                         full
% 12.04/1.99  --bmc1_ground_init                      false
% 12.04/1.99  --bmc1_pre_inst_next_state              false
% 12.04/1.99  --bmc1_pre_inst_state                   false
% 12.04/1.99  --bmc1_pre_inst_reach_state             false
% 12.04/1.99  --bmc1_out_unsat_core                   false
% 12.04/1.99  --bmc1_aig_witness_out                  false
% 12.04/1.99  --bmc1_verbose                          false
% 12.04/1.99  --bmc1_dump_clauses_tptp                false
% 12.04/1.99  --bmc1_dump_unsat_core_tptp             false
% 12.04/1.99  --bmc1_dump_file                        -
% 12.04/1.99  --bmc1_ucm_expand_uc_limit              128
% 12.04/1.99  --bmc1_ucm_n_expand_iterations          6
% 12.04/1.99  --bmc1_ucm_extend_mode                  1
% 12.04/1.99  --bmc1_ucm_init_mode                    2
% 12.04/1.99  --bmc1_ucm_cone_mode                    none
% 12.04/1.99  --bmc1_ucm_reduced_relation_type        0
% 12.04/1.99  --bmc1_ucm_relax_model                  4
% 12.04/1.99  --bmc1_ucm_full_tr_after_sat            true
% 12.04/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 12.04/1.99  --bmc1_ucm_layered_model                none
% 12.04/1.99  --bmc1_ucm_max_lemma_size               10
% 12.04/1.99  
% 12.04/1.99  ------ AIG Options
% 12.04/1.99  
% 12.04/1.99  --aig_mode                              false
% 12.04/1.99  
% 12.04/1.99  ------ Instantiation Options
% 12.04/1.99  
% 12.04/1.99  --instantiation_flag                    true
% 12.04/1.99  --inst_sos_flag                         true
% 12.04/1.99  --inst_sos_phase                        true
% 12.04/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.04/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.04/1.99  --inst_lit_sel_side                     num_symb
% 12.04/1.99  --inst_solver_per_active                1400
% 12.04/1.99  --inst_solver_calls_frac                1.
% 12.04/1.99  --inst_passive_queue_type               priority_queues
% 12.04/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.04/1.99  --inst_passive_queues_freq              [25;2]
% 12.04/1.99  --inst_dismatching                      true
% 12.04/1.99  --inst_eager_unprocessed_to_passive     true
% 12.04/1.99  --inst_prop_sim_given                   true
% 12.04/1.99  --inst_prop_sim_new                     false
% 12.04/1.99  --inst_subs_new                         false
% 12.04/1.99  --inst_eq_res_simp                      false
% 12.04/1.99  --inst_subs_given                       false
% 12.04/1.99  --inst_orphan_elimination               true
% 12.04/1.99  --inst_learning_loop_flag               true
% 12.04/1.99  --inst_learning_start                   3000
% 12.04/1.99  --inst_learning_factor                  2
% 12.04/1.99  --inst_start_prop_sim_after_learn       3
% 12.04/1.99  --inst_sel_renew                        solver
% 12.04/1.99  --inst_lit_activity_flag                true
% 12.04/1.99  --inst_restr_to_given                   false
% 12.04/1.99  --inst_activity_threshold               500
% 12.04/1.99  --inst_out_proof                        true
% 12.04/1.99  
% 12.04/1.99  ------ Resolution Options
% 12.04/1.99  
% 12.04/1.99  --resolution_flag                       true
% 12.04/1.99  --res_lit_sel                           adaptive
% 12.04/1.99  --res_lit_sel_side                      none
% 12.04/1.99  --res_ordering                          kbo
% 12.04/1.99  --res_to_prop_solver                    active
% 12.04/1.99  --res_prop_simpl_new                    false
% 12.04/1.99  --res_prop_simpl_given                  true
% 12.04/1.99  --res_passive_queue_type                priority_queues
% 12.04/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.04/1.99  --res_passive_queues_freq               [15;5]
% 12.04/1.99  --res_forward_subs                      full
% 12.04/1.99  --res_backward_subs                     full
% 12.04/1.99  --res_forward_subs_resolution           true
% 12.04/1.99  --res_backward_subs_resolution          true
% 12.04/1.99  --res_orphan_elimination                true
% 12.04/1.99  --res_time_limit                        2.
% 12.04/1.99  --res_out_proof                         true
% 12.04/1.99  
% 12.04/1.99  ------ Superposition Options
% 12.04/1.99  
% 12.04/1.99  --superposition_flag                    true
% 12.04/1.99  --sup_passive_queue_type                priority_queues
% 12.04/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.04/1.99  --sup_passive_queues_freq               [8;1;4]
% 12.04/1.99  --demod_completeness_check              fast
% 12.04/1.99  --demod_use_ground                      true
% 12.04/1.99  --sup_to_prop_solver                    passive
% 12.04/1.99  --sup_prop_simpl_new                    true
% 12.04/1.99  --sup_prop_simpl_given                  true
% 12.04/1.99  --sup_fun_splitting                     true
% 12.04/1.99  --sup_smt_interval                      50000
% 12.04/1.99  
% 12.04/1.99  ------ Superposition Simplification Setup
% 12.04/1.99  
% 12.04/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.04/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.04/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.04/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 12.04/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 12.04/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.04/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.04/1.99  --sup_immed_triv                        [TrivRules]
% 12.04/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.04/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.04/1.99  --sup_immed_bw_main                     []
% 12.04/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.04/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 12.04/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.04/1.99  --sup_input_bw                          []
% 12.04/1.99  
% 12.04/1.99  ------ Combination Options
% 12.04/1.99  
% 12.04/1.99  --comb_res_mult                         3
% 12.04/1.99  --comb_sup_mult                         2
% 12.04/1.99  --comb_inst_mult                        10
% 12.04/1.99  
% 12.04/1.99  ------ Debug Options
% 12.04/1.99  
% 12.04/1.99  --dbg_backtrace                         false
% 12.04/1.99  --dbg_dump_prop_clauses                 false
% 12.04/1.99  --dbg_dump_prop_clauses_file            -
% 12.04/1.99  --dbg_out_stat                          false
% 12.04/1.99  ------ Parsing...
% 12.04/1.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 12.04/1.99  
% 12.04/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 12.04/1.99  
% 12.04/1.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 12.04/1.99  
% 12.04/1.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 12.04/1.99  ------ Proving...
% 12.04/1.99  ------ Problem Properties 
% 12.04/1.99  
% 12.04/1.99  
% 12.04/1.99  clauses                                 10
% 12.04/1.99  conjectures                             1
% 12.04/1.99  EPR                                     1
% 12.04/1.99  Horn                                    10
% 12.04/1.99  unary                                   7
% 12.04/1.99  binary                                  3
% 12.04/1.99  lits                                    13
% 12.04/1.99  lits eq                                 8
% 12.04/1.99  fd_pure                                 0
% 12.04/1.99  fd_pseudo                               0
% 12.04/1.99  fd_cond                                 0
% 12.04/1.99  fd_pseudo_cond                          0
% 12.04/1.99  AC symbols                              0
% 12.04/1.99  
% 12.04/1.99  ------ Schedule dynamic 5 is on 
% 12.04/1.99  
% 12.04/1.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 12.04/1.99  
% 12.04/1.99  
% 12.04/1.99  ------ 
% 12.04/1.99  Current options:
% 12.04/1.99  ------ 
% 12.04/1.99  
% 12.04/1.99  ------ Input Options
% 12.04/1.99  
% 12.04/1.99  --out_options                           all
% 12.04/1.99  --tptp_safe_out                         true
% 12.04/1.99  --problem_path                          ""
% 12.04/1.99  --include_path                          ""
% 12.04/1.99  --clausifier                            res/vclausify_rel
% 12.04/1.99  --clausifier_options                    ""
% 12.04/1.99  --stdin                                 false
% 12.04/1.99  --stats_out                             all
% 12.04/1.99  
% 12.04/1.99  ------ General Options
% 12.04/1.99  
% 12.04/1.99  --fof                                   false
% 12.04/1.99  --time_out_real                         305.
% 12.04/1.99  --time_out_virtual                      -1.
% 12.04/1.99  --symbol_type_check                     false
% 12.04/1.99  --clausify_out                          false
% 12.04/1.99  --sig_cnt_out                           false
% 12.04/1.99  --trig_cnt_out                          false
% 12.04/1.99  --trig_cnt_out_tolerance                1.
% 12.04/1.99  --trig_cnt_out_sk_spl                   false
% 12.04/1.99  --abstr_cl_out                          false
% 12.04/1.99  
% 12.04/1.99  ------ Global Options
% 12.04/1.99  
% 12.04/1.99  --schedule                              default
% 12.04/1.99  --add_important_lit                     false
% 12.04/1.99  --prop_solver_per_cl                    1000
% 12.04/1.99  --min_unsat_core                        false
% 12.04/1.99  --soft_assumptions                      false
% 12.04/1.99  --soft_lemma_size                       3
% 12.04/1.99  --prop_impl_unit_size                   0
% 12.04/1.99  --prop_impl_unit                        []
% 12.04/1.99  --share_sel_clauses                     true
% 12.04/1.99  --reset_solvers                         false
% 12.04/1.99  --bc_imp_inh                            [conj_cone]
% 12.04/1.99  --conj_cone_tolerance                   3.
% 12.04/1.99  --extra_neg_conj                        none
% 12.04/1.99  --large_theory_mode                     true
% 12.04/1.99  --prolific_symb_bound                   200
% 12.04/1.99  --lt_threshold                          2000
% 12.04/1.99  --clause_weak_htbl                      true
% 12.04/1.99  --gc_record_bc_elim                     false
% 12.04/1.99  
% 12.04/1.99  ------ Preprocessing Options
% 12.04/1.99  
% 12.04/1.99  --preprocessing_flag                    true
% 12.04/1.99  --time_out_prep_mult                    0.1
% 12.04/1.99  --splitting_mode                        input
% 12.04/1.99  --splitting_grd                         true
% 12.04/1.99  --splitting_cvd                         false
% 12.04/1.99  --splitting_cvd_svl                     false
% 12.04/1.99  --splitting_nvd                         32
% 12.04/1.99  --sub_typing                            true
% 12.04/1.99  --prep_gs_sim                           true
% 12.04/1.99  --prep_unflatten                        true
% 12.04/1.99  --prep_res_sim                          true
% 12.04/1.99  --prep_upred                            true
% 12.04/1.99  --prep_sem_filter                       exhaustive
% 12.04/1.99  --prep_sem_filter_out                   false
% 12.04/1.99  --pred_elim                             true
% 12.04/1.99  --res_sim_input                         true
% 12.04/1.99  --eq_ax_congr_red                       true
% 12.04/1.99  --pure_diseq_elim                       true
% 12.04/1.99  --brand_transform                       false
% 12.04/1.99  --non_eq_to_eq                          false
% 12.04/1.99  --prep_def_merge                        true
% 12.04/1.99  --prep_def_merge_prop_impl              false
% 12.04/1.99  --prep_def_merge_mbd                    true
% 12.04/1.99  --prep_def_merge_tr_red                 false
% 12.04/1.99  --prep_def_merge_tr_cl                  false
% 12.04/1.99  --smt_preprocessing                     true
% 12.04/1.99  --smt_ac_axioms                         fast
% 12.04/1.99  --preprocessed_out                      false
% 12.04/1.99  --preprocessed_stats                    false
% 12.04/1.99  
% 12.04/1.99  ------ Abstraction refinement Options
% 12.04/1.99  
% 12.04/1.99  --abstr_ref                             []
% 12.04/1.99  --abstr_ref_prep                        false
% 12.04/1.99  --abstr_ref_until_sat                   false
% 12.04/1.99  --abstr_ref_sig_restrict                funpre
% 12.04/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 12.04/1.99  --abstr_ref_under                       []
% 12.04/1.99  
% 12.04/1.99  ------ SAT Options
% 12.04/1.99  
% 12.04/1.99  --sat_mode                              false
% 12.04/1.99  --sat_fm_restart_options                ""
% 12.04/1.99  --sat_gr_def                            false
% 12.04/1.99  --sat_epr_types                         true
% 12.04/1.99  --sat_non_cyclic_types                  false
% 12.04/1.99  --sat_finite_models                     false
% 12.04/1.99  --sat_fm_lemmas                         false
% 12.04/1.99  --sat_fm_prep                           false
% 12.04/1.99  --sat_fm_uc_incr                        true
% 12.04/1.99  --sat_out_model                         small
% 12.04/1.99  --sat_out_clauses                       false
% 12.04/1.99  
% 12.04/1.99  ------ QBF Options
% 12.04/1.99  
% 12.04/1.99  --qbf_mode                              false
% 12.04/1.99  --qbf_elim_univ                         false
% 12.04/1.99  --qbf_dom_inst                          none
% 12.04/1.99  --qbf_dom_pre_inst                      false
% 12.04/1.99  --qbf_sk_in                             false
% 12.04/1.99  --qbf_pred_elim                         true
% 12.04/1.99  --qbf_split                             512
% 12.04/1.99  
% 12.04/1.99  ------ BMC1 Options
% 12.04/1.99  
% 12.04/1.99  --bmc1_incremental                      false
% 12.04/1.99  --bmc1_axioms                           reachable_all
% 12.04/1.99  --bmc1_min_bound                        0
% 12.04/1.99  --bmc1_max_bound                        -1
% 12.04/1.99  --bmc1_max_bound_default                -1
% 12.04/1.99  --bmc1_symbol_reachability              true
% 12.04/1.99  --bmc1_property_lemmas                  false
% 12.04/1.99  --bmc1_k_induction                      false
% 12.04/1.99  --bmc1_non_equiv_states                 false
% 12.04/1.99  --bmc1_deadlock                         false
% 12.04/1.99  --bmc1_ucm                              false
% 12.04/1.99  --bmc1_add_unsat_core                   none
% 12.04/1.99  --bmc1_unsat_core_children              false
% 12.04/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 12.04/1.99  --bmc1_out_stat                         full
% 12.04/1.99  --bmc1_ground_init                      false
% 12.04/1.99  --bmc1_pre_inst_next_state              false
% 12.04/1.99  --bmc1_pre_inst_state                   false
% 12.04/1.99  --bmc1_pre_inst_reach_state             false
% 12.04/1.99  --bmc1_out_unsat_core                   false
% 12.04/1.99  --bmc1_aig_witness_out                  false
% 12.04/1.99  --bmc1_verbose                          false
% 12.04/1.99  --bmc1_dump_clauses_tptp                false
% 12.04/1.99  --bmc1_dump_unsat_core_tptp             false
% 12.04/1.99  --bmc1_dump_file                        -
% 12.04/1.99  --bmc1_ucm_expand_uc_limit              128
% 12.04/1.99  --bmc1_ucm_n_expand_iterations          6
% 12.04/1.99  --bmc1_ucm_extend_mode                  1
% 12.04/1.99  --bmc1_ucm_init_mode                    2
% 12.04/1.99  --bmc1_ucm_cone_mode                    none
% 12.04/1.99  --bmc1_ucm_reduced_relation_type        0
% 12.04/1.99  --bmc1_ucm_relax_model                  4
% 12.04/1.99  --bmc1_ucm_full_tr_after_sat            true
% 12.04/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 12.04/1.99  --bmc1_ucm_layered_model                none
% 12.04/1.99  --bmc1_ucm_max_lemma_size               10
% 12.04/1.99  
% 12.04/1.99  ------ AIG Options
% 12.04/1.99  
% 12.04/1.99  --aig_mode                              false
% 12.04/1.99  
% 12.04/1.99  ------ Instantiation Options
% 12.04/1.99  
% 12.04/1.99  --instantiation_flag                    true
% 12.04/1.99  --inst_sos_flag                         true
% 12.04/1.99  --inst_sos_phase                        true
% 12.04/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 12.04/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 12.04/1.99  --inst_lit_sel_side                     none
% 12.04/1.99  --inst_solver_per_active                1400
% 12.04/1.99  --inst_solver_calls_frac                1.
% 12.04/1.99  --inst_passive_queue_type               priority_queues
% 12.04/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 12.04/1.99  --inst_passive_queues_freq              [25;2]
% 12.04/1.99  --inst_dismatching                      true
% 12.04/1.99  --inst_eager_unprocessed_to_passive     true
% 12.04/1.99  --inst_prop_sim_given                   true
% 12.04/1.99  --inst_prop_sim_new                     false
% 12.04/1.99  --inst_subs_new                         false
% 12.04/1.99  --inst_eq_res_simp                      false
% 12.04/1.99  --inst_subs_given                       false
% 12.04/1.99  --inst_orphan_elimination               true
% 12.04/1.99  --inst_learning_loop_flag               true
% 12.04/1.99  --inst_learning_start                   3000
% 12.04/1.99  --inst_learning_factor                  2
% 12.04/1.99  --inst_start_prop_sim_after_learn       3
% 12.04/1.99  --inst_sel_renew                        solver
% 12.04/1.99  --inst_lit_activity_flag                true
% 12.04/1.99  --inst_restr_to_given                   false
% 12.04/1.99  --inst_activity_threshold               500
% 12.04/1.99  --inst_out_proof                        true
% 12.04/1.99  
% 12.04/1.99  ------ Resolution Options
% 12.04/1.99  
% 12.04/1.99  --resolution_flag                       false
% 12.04/1.99  --res_lit_sel                           adaptive
% 12.04/1.99  --res_lit_sel_side                      none
% 12.04/1.99  --res_ordering                          kbo
% 12.04/1.99  --res_to_prop_solver                    active
% 12.04/1.99  --res_prop_simpl_new                    false
% 12.04/1.99  --res_prop_simpl_given                  true
% 12.04/1.99  --res_passive_queue_type                priority_queues
% 12.04/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 12.04/1.99  --res_passive_queues_freq               [15;5]
% 12.04/1.99  --res_forward_subs                      full
% 12.04/1.99  --res_backward_subs                     full
% 12.04/1.99  --res_forward_subs_resolution           true
% 12.04/1.99  --res_backward_subs_resolution          true
% 12.04/1.99  --res_orphan_elimination                true
% 12.04/1.99  --res_time_limit                        2.
% 12.04/1.99  --res_out_proof                         true
% 12.04/1.99  
% 12.04/1.99  ------ Superposition Options
% 12.04/1.99  
% 12.04/1.99  --superposition_flag                    true
% 12.04/1.99  --sup_passive_queue_type                priority_queues
% 12.04/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 12.04/1.99  --sup_passive_queues_freq               [8;1;4]
% 12.04/1.99  --demod_completeness_check              fast
% 12.04/1.99  --demod_use_ground                      true
% 12.04/1.99  --sup_to_prop_solver                    passive
% 12.04/1.99  --sup_prop_simpl_new                    true
% 12.04/1.99  --sup_prop_simpl_given                  true
% 12.04/1.99  --sup_fun_splitting                     true
% 12.04/1.99  --sup_smt_interval                      50000
% 12.04/1.99  
% 12.04/1.99  ------ Superposition Simplification Setup
% 12.04/1.99  
% 12.04/1.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 12.04/1.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 12.04/1.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 12.04/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 12.04/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 12.04/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 12.04/1.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 12.04/1.99  --sup_immed_triv                        [TrivRules]
% 12.04/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 12.04/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.04/1.99  --sup_immed_bw_main                     []
% 12.04/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 12.04/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 12.04/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 12.04/1.99  --sup_input_bw                          []
% 12.04/1.99  
% 12.04/1.99  ------ Combination Options
% 12.04/1.99  
% 12.04/1.99  --comb_res_mult                         3
% 12.04/1.99  --comb_sup_mult                         2
% 12.04/1.99  --comb_inst_mult                        10
% 12.04/1.99  
% 12.04/1.99  ------ Debug Options
% 12.04/1.99  
% 12.04/1.99  --dbg_backtrace                         false
% 12.04/1.99  --dbg_dump_prop_clauses                 false
% 12.04/1.99  --dbg_dump_prop_clauses_file            -
% 12.04/1.99  --dbg_out_stat                          false
% 12.04/1.99  
% 12.04/1.99  
% 12.04/1.99  
% 12.04/1.99  
% 12.04/1.99  ------ Proving...
% 12.04/1.99  
% 12.04/1.99  
% 12.04/1.99  % SZS status Theorem for theBenchmark.p
% 12.04/1.99  
% 12.04/1.99   Resolution empty clause
% 12.04/1.99  
% 12.04/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 12.04/1.99  
% 12.04/1.99  fof(f7,axiom,(
% 12.04/1.99    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 12.04/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f23,plain,(
% 12.04/1.99    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 12.04/1.99    inference(cnf_transformation,[],[f7])).
% 12.04/1.99  
% 12.04/1.99  fof(f1,axiom,(
% 12.04/1.99    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 12.04/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f12,plain,(
% 12.04/1.99    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 12.04/1.99    inference(ennf_transformation,[],[f1])).
% 12.04/1.99  
% 12.04/1.99  fof(f17,plain,(
% 12.04/1.99    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 12.04/1.99    inference(cnf_transformation,[],[f12])).
% 12.04/1.99  
% 12.04/1.99  fof(f8,axiom,(
% 12.04/1.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 12.04/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f14,plain,(
% 12.04/1.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 12.04/1.99    inference(nnf_transformation,[],[f8])).
% 12.04/1.99  
% 12.04/1.99  fof(f24,plain,(
% 12.04/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 12.04/1.99    inference(cnf_transformation,[],[f14])).
% 12.04/1.99  
% 12.04/1.99  fof(f9,axiom,(
% 12.04/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 12.04/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f26,plain,(
% 12.04/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 12.04/1.99    inference(cnf_transformation,[],[f9])).
% 12.04/1.99  
% 12.04/1.99  fof(f6,axiom,(
% 12.04/1.99    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 12.04/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f22,plain,(
% 12.04/1.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 12.04/1.99    inference(cnf_transformation,[],[f6])).
% 12.04/1.99  
% 12.04/1.99  fof(f28,plain,(
% 12.04/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 12.04/1.99    inference(definition_unfolding,[],[f26,f22])).
% 12.04/1.99  
% 12.04/1.99  fof(f4,axiom,(
% 12.04/1.99    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 12.04/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f20,plain,(
% 12.04/1.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 12.04/1.99    inference(cnf_transformation,[],[f4])).
% 12.04/1.99  
% 12.04/1.99  fof(f2,axiom,(
% 12.04/1.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 12.04/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f18,plain,(
% 12.04/1.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.04/1.99    inference(cnf_transformation,[],[f2])).
% 12.04/1.99  
% 12.04/1.99  fof(f3,axiom,(
% 12.04/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 12.04/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f19,plain,(
% 12.04/1.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 12.04/1.99    inference(cnf_transformation,[],[f3])).
% 12.04/1.99  
% 12.04/1.99  fof(f5,axiom,(
% 12.04/1.99    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 12.04/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f21,plain,(
% 12.04/1.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 12.04/1.99    inference(cnf_transformation,[],[f5])).
% 12.04/1.99  
% 12.04/1.99  fof(f10,conjecture,(
% 12.04/1.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 12.04/1.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 12.04/1.99  
% 12.04/1.99  fof(f11,negated_conjecture,(
% 12.04/1.99    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 12.04/1.99    inference(negated_conjecture,[],[f10])).
% 12.04/1.99  
% 12.04/1.99  fof(f13,plain,(
% 12.04/1.99    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 12.04/1.99    inference(ennf_transformation,[],[f11])).
% 12.04/1.99  
% 12.04/1.99  fof(f15,plain,(
% 12.04/1.99    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 12.04/1.99    introduced(choice_axiom,[])).
% 12.04/1.99  
% 12.04/1.99  fof(f16,plain,(
% 12.04/1.99    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 12.04/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15])).
% 12.04/1.99  
% 12.04/1.99  fof(f27,plain,(
% 12.04/1.99    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 12.04/1.99    inference(cnf_transformation,[],[f16])).
% 12.04/1.99  
% 12.04/1.99  cnf(c_5,plain,
% 12.04/1.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 12.04/1.99      inference(cnf_transformation,[],[f23]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_223,plain,
% 12.04/1.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 12.04/1.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_0,plain,
% 12.04/1.99      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 12.04/1.99      inference(cnf_transformation,[],[f17]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_224,plain,
% 12.04/1.99      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 12.04/1.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_51158,plain,
% 12.04/1.99      ( r1_xboole_0(X0,k4_xboole_0(X1,X0)) = iProver_top ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_223,c_224]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_7,plain,
% 12.04/1.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 12.04/1.99      inference(cnf_transformation,[],[f24]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_221,plain,
% 12.04/1.99      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 12.04/1.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_53558,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_51158,c_221]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_471,plain,
% 12.04/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_223,c_221]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_8,plain,
% 12.04/1.99      ( k2_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
% 12.04/1.99      inference(cnf_transformation,[],[f28]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_752,plain,
% 12.04/1.99      ( k2_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_471,c_8]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_3,plain,
% 12.04/1.99      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 12.04/1.99      inference(cnf_transformation,[],[f20]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_758,plain,
% 12.04/1.99      ( k2_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),X1),k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1)))) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_752,c_3]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_1,plain,
% 12.04/1.99      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 12.04/1.99      inference(cnf_transformation,[],[f18]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_2,plain,
% 12.04/1.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 12.04/1.99      inference(cnf_transformation,[],[f19]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_4,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 12.04/1.99      inference(cnf_transformation,[],[f21]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_302,plain,
% 12.04/1.99      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_484,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_3,c_302]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_485,plain,
% 12.04/1.99      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_484,c_2]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_759,plain,
% 12.04/1.99      ( k5_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_758,c_1,c_2,c_485]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_54951,plain,
% 12.04/1.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 12.04/1.99      inference(superposition,[status(thm)],[c_53558,c_759]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_55000,plain,
% 12.04/1.99      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_54951,c_53558]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_55001,plain,
% 12.04/1.99      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 12.04/1.99      inference(light_normalisation,[status(thm)],[c_55000,c_2]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_9,negated_conjecture,
% 12.04/1.99      ( k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
% 12.04/1.99      inference(cnf_transformation,[],[f27]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_56551,plain,
% 12.04/1.99      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
% 12.04/1.99      inference(demodulation,[status(thm)],[c_55001,c_9]) ).
% 12.04/1.99  
% 12.04/1.99  cnf(c_56554,plain,
% 12.04/1.99      ( $false ),
% 12.04/1.99      inference(equality_resolution_simp,[status(thm)],[c_56551]) ).
% 12.04/1.99  
% 12.04/1.99  
% 12.04/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 12.04/1.99  
% 12.04/1.99  ------                               Statistics
% 12.04/1.99  
% 12.04/1.99  ------ General
% 12.04/1.99  
% 12.04/1.99  abstr_ref_over_cycles:                  0
% 12.04/1.99  abstr_ref_under_cycles:                 0
% 12.04/1.99  gc_basic_clause_elim:                   0
% 12.04/1.99  forced_gc_time:                         0
% 12.04/1.99  parsing_time:                           0.007
% 12.04/1.99  unif_index_cands_time:                  0.
% 12.04/1.99  unif_index_add_time:                    0.
% 12.04/1.99  orderings_time:                         0.
% 12.04/1.99  out_proof_time:                         0.005
% 12.04/1.99  total_time:                             1.461
% 12.04/1.99  num_of_symbols:                         38
% 12.04/1.99  num_of_terms:                           67734
% 12.04/1.99  
% 12.04/1.99  ------ Preprocessing
% 12.04/1.99  
% 12.04/1.99  num_of_splits:                          0
% 12.04/1.99  num_of_split_atoms:                     0
% 12.04/1.99  num_of_reused_defs:                     0
% 12.04/1.99  num_eq_ax_congr_red:                    2
% 12.04/1.99  num_of_sem_filtered_clauses:            1
% 12.04/1.99  num_of_subtypes:                        0
% 12.04/1.99  monotx_restored_types:                  0
% 12.04/1.99  sat_num_of_epr_types:                   0
% 12.04/1.99  sat_num_of_non_cyclic_types:            0
% 12.04/1.99  sat_guarded_non_collapsed_types:        0
% 12.04/1.99  num_pure_diseq_elim:                    0
% 12.04/1.99  simp_replaced_by:                       0
% 12.04/1.99  res_preprocessed:                       43
% 12.04/1.99  prep_upred:                             0
% 12.04/1.99  prep_unflattend:                        0
% 12.04/1.99  smt_new_axioms:                         0
% 12.04/1.99  pred_elim_cands:                        1
% 12.04/1.99  pred_elim:                              0
% 12.04/1.99  pred_elim_cl:                           0
% 12.04/1.99  pred_elim_cycles:                       1
% 12.04/1.99  merged_defs:                            6
% 12.04/1.99  merged_defs_ncl:                        0
% 12.04/1.99  bin_hyper_res:                          6
% 12.04/1.99  prep_cycles:                            3
% 12.04/1.99  pred_elim_time:                         0.
% 12.04/1.99  splitting_time:                         0.
% 12.04/1.99  sem_filter_time:                        0.
% 12.04/1.99  monotx_time:                            0.
% 12.04/1.99  subtype_inf_time:                       0.
% 12.04/1.99  
% 12.04/1.99  ------ Problem properties
% 12.04/1.99  
% 12.04/1.99  clauses:                                10
% 12.04/1.99  conjectures:                            1
% 12.04/1.99  epr:                                    1
% 12.04/1.99  horn:                                   10
% 12.04/1.99  ground:                                 1
% 12.04/1.99  unary:                                  7
% 12.04/1.99  binary:                                 3
% 12.04/1.99  lits:                                   13
% 12.04/1.99  lits_eq:                                8
% 12.04/1.99  fd_pure:                                0
% 12.04/1.99  fd_pseudo:                              0
% 12.04/1.99  fd_cond:                                0
% 12.04/1.99  fd_pseudo_cond:                         0
% 12.04/1.99  ac_symbols:                             0
% 12.04/1.99  
% 12.04/1.99  ------ Propositional Solver
% 12.04/1.99  
% 12.04/1.99  prop_solver_calls:                      32
% 12.04/1.99  prop_fast_solver_calls:                 422
% 12.04/1.99  smt_solver_calls:                       0
% 12.04/1.99  smt_fast_solver_calls:                  0
% 12.04/1.99  prop_num_of_clauses:                    12616
% 12.04/1.99  prop_preprocess_simplified:             14810
% 12.04/1.99  prop_fo_subsumed:                       0
% 12.04/1.99  prop_solver_time:                       0.
% 12.04/1.99  smt_solver_time:                        0.
% 12.04/1.99  smt_fast_solver_time:                   0.
% 12.04/1.99  prop_fast_solver_time:                  0.
% 12.04/1.99  prop_unsat_core_time:                   0.
% 12.04/1.99  
% 12.04/1.99  ------ QBF
% 12.04/1.99  
% 12.04/1.99  qbf_q_res:                              0
% 12.04/1.99  qbf_num_tautologies:                    0
% 12.04/1.99  qbf_prep_cycles:                        0
% 12.04/1.99  
% 12.04/1.99  ------ BMC1
% 12.04/1.99  
% 12.04/1.99  bmc1_current_bound:                     -1
% 12.04/1.99  bmc1_last_solved_bound:                 -1
% 12.04/1.99  bmc1_unsat_core_size:                   -1
% 12.04/1.99  bmc1_unsat_core_parents_size:           -1
% 12.04/1.99  bmc1_merge_next_fun:                    0
% 12.04/1.99  bmc1_unsat_core_clauses_time:           0.
% 12.04/1.99  
% 12.04/1.99  ------ Instantiation
% 12.04/1.99  
% 12.04/1.99  inst_num_of_clauses:                    3266
% 12.04/1.99  inst_num_in_passive:                    1412
% 12.04/1.99  inst_num_in_active:                     1073
% 12.04/1.99  inst_num_in_unprocessed:                781
% 12.04/1.99  inst_num_of_loops:                      1270
% 12.04/1.99  inst_num_of_learning_restarts:          0
% 12.04/1.99  inst_num_moves_active_passive:          192
% 12.04/1.99  inst_lit_activity:                      0
% 12.04/1.99  inst_lit_activity_moves:                1
% 12.04/1.99  inst_num_tautologies:                   0
% 12.04/1.99  inst_num_prop_implied:                  0
% 12.04/1.99  inst_num_existing_simplified:           0
% 12.04/1.99  inst_num_eq_res_simplified:             0
% 12.04/1.99  inst_num_child_elim:                    0
% 12.04/1.99  inst_num_of_dismatching_blockings:      3538
% 12.04/1.99  inst_num_of_non_proper_insts:           6030
% 12.04/1.99  inst_num_of_duplicates:                 0
% 12.04/1.99  inst_inst_num_from_inst_to_res:         0
% 12.04/1.99  inst_dismatching_checking_time:         0.
% 12.04/1.99  
% 12.04/1.99  ------ Resolution
% 12.04/1.99  
% 12.04/1.99  res_num_of_clauses:                     0
% 12.04/1.99  res_num_in_passive:                     0
% 12.04/1.99  res_num_in_active:                      0
% 12.04/1.99  res_num_of_loops:                       46
% 12.04/1.99  res_forward_subset_subsumed:            2760
% 12.04/1.99  res_backward_subset_subsumed:           0
% 12.04/1.99  res_forward_subsumed:                   0
% 12.04/1.99  res_backward_subsumed:                  0
% 12.04/1.99  res_forward_subsumption_resolution:     0
% 12.04/1.99  res_backward_subsumption_resolution:    0
% 12.04/1.99  res_clause_to_clause_subsumption:       62981
% 12.04/1.99  res_orphan_elimination:                 0
% 12.04/1.99  res_tautology_del:                      479
% 12.04/1.99  res_num_eq_res_simplified:              0
% 12.04/1.99  res_num_sel_changes:                    0
% 12.04/1.99  res_moves_from_active_to_pass:          0
% 12.04/1.99  
% 12.04/1.99  ------ Superposition
% 12.04/1.99  
% 12.04/1.99  sup_time_total:                         0.
% 12.04/1.99  sup_time_generating:                    0.
% 12.04/1.99  sup_time_sim_full:                      0.
% 12.04/1.99  sup_time_sim_immed:                     0.
% 12.04/1.99  
% 12.04/1.99  sup_num_of_clauses:                     3478
% 12.04/1.99  sup_num_in_active:                      152
% 12.04/1.99  sup_num_in_passive:                     3326
% 12.04/1.99  sup_num_of_loops:                       252
% 12.04/1.99  sup_fw_superposition:                   12448
% 12.04/1.99  sup_bw_superposition:                   10343
% 12.04/1.99  sup_immediate_simplified:               10691
% 12.04/1.99  sup_given_eliminated:                   3
% 12.04/1.99  comparisons_done:                       0
% 12.04/1.99  comparisons_avoided:                    0
% 12.04/1.99  
% 12.04/1.99  ------ Simplifications
% 12.04/1.99  
% 12.04/1.99  
% 12.04/1.99  sim_fw_subset_subsumed:                 0
% 12.04/1.99  sim_bw_subset_subsumed:                 0
% 12.04/1.99  sim_fw_subsumed:                        3203
% 12.04/1.99  sim_bw_subsumed:                        112
% 12.04/1.99  sim_fw_subsumption_res:                 0
% 12.04/1.99  sim_bw_subsumption_res:                 0
% 12.04/1.99  sim_tautology_del:                      0
% 12.04/1.99  sim_eq_tautology_del:                   2724
% 12.04/1.99  sim_eq_res_simp:                        25
% 12.04/1.99  sim_fw_demodulated:                     5291
% 12.04/1.99  sim_bw_demodulated:                     90
% 12.04/1.99  sim_light_normalised:                   3590
% 12.04/1.99  sim_joinable_taut:                      0
% 12.04/1.99  sim_joinable_simp:                      0
% 12.04/1.99  sim_ac_normalised:                      0
% 12.04/1.99  sim_smt_subsumption:                    0
% 12.04/1.99  
%------------------------------------------------------------------------------
