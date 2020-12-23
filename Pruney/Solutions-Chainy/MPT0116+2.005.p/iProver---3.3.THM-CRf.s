%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:03 EST 2020

% Result     : Theorem 6.90s
% Output     : CNFRefutation 6.90s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 131 expanded)
%              Number of clauses        :   27 (  54 expanded)
%              Number of leaves         :    8 (  30 expanded)
%              Depth                    :   17
%              Number of atoms          :   61 ( 191 expanded)
%              Number of equality atoms :   36 (  93 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k4_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k4_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f21,f16,f16])).

fof(f23,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f23,f16])).

cnf(c_1,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_164,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_166,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1878,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_164,c_166])).

cnf(c_2406,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_1878,c_1])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_2,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_168,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_291,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_168])).

cnf(c_2994,plain,
    ( r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2406,c_291])).

cnf(c_9722,plain,
    ( r1_tarski(sK0,k3_xboole_0(sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1878,c_2994])).

cnf(c_9957,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,sK1)) = sK0 ),
    inference(superposition,[status(thm)],[c_9722,c_166])).

cnf(c_9972,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),X0)) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_9957,c_1])).

cnf(c_11949,plain,
    ( k3_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,X0))) = k3_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_1,c_9972])).

cnf(c_5,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_65,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(theory_normalisation,[status(thm)],[c_5,c_1,c_0])).

cnf(c_14772,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,X0)) ),
    inference(superposition,[status(thm)],[c_11949,c_65])).

cnf(c_14873,plain,
    ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
    inference(light_normalisation,[status(thm)],[c_14772,c_1878])).

cnf(c_390,plain,
    ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_291])).

cnf(c_2426,plain,
    ( r1_tarski(k3_xboole_0(X0,sK0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1878,c_390])).

cnf(c_2705,plain,
    ( r1_tarski(k3_xboole_0(sK0,X0),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_2426])).

cnf(c_16577,plain,
    ( r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_14873,c_2705])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_165,plain,
    ( r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_31769,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_16577,c_165])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:46:00 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 6.90/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.90/1.48  
% 6.90/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.90/1.48  
% 6.90/1.48  ------  iProver source info
% 6.90/1.48  
% 6.90/1.48  git: date: 2020-06-30 10:37:57 +0100
% 6.90/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.90/1.48  git: non_committed_changes: false
% 6.90/1.48  git: last_make_outside_of_git: false
% 6.90/1.48  
% 6.90/1.48  ------ 
% 6.90/1.48  
% 6.90/1.48  ------ Input Options
% 6.90/1.48  
% 6.90/1.48  --out_options                           all
% 6.90/1.48  --tptp_safe_out                         true
% 6.90/1.48  --problem_path                          ""
% 6.90/1.48  --include_path                          ""
% 6.90/1.48  --clausifier                            res/vclausify_rel
% 6.90/1.48  --clausifier_options                    --mode clausify
% 6.90/1.48  --stdin                                 false
% 6.90/1.48  --stats_out                             all
% 6.90/1.48  
% 6.90/1.48  ------ General Options
% 6.90/1.48  
% 6.90/1.48  --fof                                   false
% 6.90/1.48  --time_out_real                         305.
% 6.90/1.48  --time_out_virtual                      -1.
% 6.90/1.48  --symbol_type_check                     false
% 6.90/1.48  --clausify_out                          false
% 6.90/1.48  --sig_cnt_out                           false
% 6.90/1.48  --trig_cnt_out                          false
% 6.90/1.48  --trig_cnt_out_tolerance                1.
% 6.90/1.48  --trig_cnt_out_sk_spl                   false
% 6.90/1.48  --abstr_cl_out                          false
% 6.90/1.48  
% 6.90/1.48  ------ Global Options
% 6.90/1.48  
% 6.90/1.48  --schedule                              default
% 6.90/1.48  --add_important_lit                     false
% 6.90/1.48  --prop_solver_per_cl                    1000
% 6.90/1.48  --min_unsat_core                        false
% 6.90/1.48  --soft_assumptions                      false
% 6.90/1.48  --soft_lemma_size                       3
% 6.90/1.48  --prop_impl_unit_size                   0
% 6.90/1.48  --prop_impl_unit                        []
% 6.90/1.48  --share_sel_clauses                     true
% 6.90/1.48  --reset_solvers                         false
% 6.90/1.48  --bc_imp_inh                            [conj_cone]
% 6.90/1.48  --conj_cone_tolerance                   3.
% 6.90/1.48  --extra_neg_conj                        none
% 6.90/1.48  --large_theory_mode                     true
% 6.90/1.48  --prolific_symb_bound                   200
% 6.90/1.48  --lt_threshold                          2000
% 6.90/1.48  --clause_weak_htbl                      true
% 6.90/1.48  --gc_record_bc_elim                     false
% 6.90/1.48  
% 6.90/1.48  ------ Preprocessing Options
% 6.90/1.48  
% 6.90/1.48  --preprocessing_flag                    true
% 6.90/1.48  --time_out_prep_mult                    0.1
% 6.90/1.48  --splitting_mode                        input
% 6.90/1.48  --splitting_grd                         true
% 6.90/1.48  --splitting_cvd                         false
% 6.90/1.48  --splitting_cvd_svl                     false
% 6.90/1.48  --splitting_nvd                         32
% 6.90/1.48  --sub_typing                            true
% 6.90/1.48  --prep_gs_sim                           true
% 6.90/1.48  --prep_unflatten                        true
% 6.90/1.48  --prep_res_sim                          true
% 6.90/1.48  --prep_upred                            true
% 6.90/1.48  --prep_sem_filter                       exhaustive
% 6.90/1.48  --prep_sem_filter_out                   false
% 6.90/1.48  --pred_elim                             true
% 6.90/1.48  --res_sim_input                         true
% 6.90/1.48  --eq_ax_congr_red                       true
% 6.90/1.48  --pure_diseq_elim                       true
% 6.90/1.48  --brand_transform                       false
% 6.90/1.48  --non_eq_to_eq                          false
% 6.90/1.48  --prep_def_merge                        true
% 6.90/1.48  --prep_def_merge_prop_impl              false
% 6.90/1.48  --prep_def_merge_mbd                    true
% 6.90/1.48  --prep_def_merge_tr_red                 false
% 6.90/1.48  --prep_def_merge_tr_cl                  false
% 6.90/1.48  --smt_preprocessing                     true
% 6.90/1.48  --smt_ac_axioms                         fast
% 6.90/1.48  --preprocessed_out                      false
% 6.90/1.48  --preprocessed_stats                    false
% 6.90/1.48  
% 6.90/1.48  ------ Abstraction refinement Options
% 6.90/1.48  
% 6.90/1.48  --abstr_ref                             []
% 6.90/1.48  --abstr_ref_prep                        false
% 6.90/1.48  --abstr_ref_until_sat                   false
% 6.90/1.48  --abstr_ref_sig_restrict                funpre
% 6.90/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.90/1.48  --abstr_ref_under                       []
% 6.90/1.48  
% 6.90/1.48  ------ SAT Options
% 6.90/1.48  
% 6.90/1.48  --sat_mode                              false
% 6.90/1.48  --sat_fm_restart_options                ""
% 6.90/1.48  --sat_gr_def                            false
% 6.90/1.48  --sat_epr_types                         true
% 6.90/1.48  --sat_non_cyclic_types                  false
% 6.90/1.48  --sat_finite_models                     false
% 6.90/1.48  --sat_fm_lemmas                         false
% 6.90/1.48  --sat_fm_prep                           false
% 6.90/1.48  --sat_fm_uc_incr                        true
% 6.90/1.48  --sat_out_model                         small
% 6.90/1.48  --sat_out_clauses                       false
% 6.90/1.48  
% 6.90/1.48  ------ QBF Options
% 6.90/1.48  
% 6.90/1.48  --qbf_mode                              false
% 6.90/1.48  --qbf_elim_univ                         false
% 6.90/1.48  --qbf_dom_inst                          none
% 6.90/1.48  --qbf_dom_pre_inst                      false
% 6.90/1.48  --qbf_sk_in                             false
% 6.90/1.48  --qbf_pred_elim                         true
% 6.90/1.48  --qbf_split                             512
% 6.90/1.48  
% 6.90/1.48  ------ BMC1 Options
% 6.90/1.48  
% 6.90/1.48  --bmc1_incremental                      false
% 6.90/1.48  --bmc1_axioms                           reachable_all
% 6.90/1.48  --bmc1_min_bound                        0
% 6.90/1.48  --bmc1_max_bound                        -1
% 6.90/1.48  --bmc1_max_bound_default                -1
% 6.90/1.48  --bmc1_symbol_reachability              true
% 6.90/1.48  --bmc1_property_lemmas                  false
% 6.90/1.48  --bmc1_k_induction                      false
% 6.90/1.48  --bmc1_non_equiv_states                 false
% 6.90/1.48  --bmc1_deadlock                         false
% 6.90/1.48  --bmc1_ucm                              false
% 6.90/1.48  --bmc1_add_unsat_core                   none
% 6.90/1.48  --bmc1_unsat_core_children              false
% 6.90/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.90/1.48  --bmc1_out_stat                         full
% 6.90/1.48  --bmc1_ground_init                      false
% 6.90/1.48  --bmc1_pre_inst_next_state              false
% 6.90/1.48  --bmc1_pre_inst_state                   false
% 6.90/1.48  --bmc1_pre_inst_reach_state             false
% 6.90/1.48  --bmc1_out_unsat_core                   false
% 6.90/1.48  --bmc1_aig_witness_out                  false
% 6.90/1.48  --bmc1_verbose                          false
% 6.90/1.48  --bmc1_dump_clauses_tptp                false
% 6.90/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.90/1.48  --bmc1_dump_file                        -
% 6.90/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.90/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.90/1.48  --bmc1_ucm_extend_mode                  1
% 6.90/1.48  --bmc1_ucm_init_mode                    2
% 6.90/1.48  --bmc1_ucm_cone_mode                    none
% 6.90/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.90/1.48  --bmc1_ucm_relax_model                  4
% 6.90/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.90/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.90/1.48  --bmc1_ucm_layered_model                none
% 6.90/1.48  --bmc1_ucm_max_lemma_size               10
% 6.90/1.48  
% 6.90/1.48  ------ AIG Options
% 6.90/1.48  
% 6.90/1.48  --aig_mode                              false
% 6.90/1.48  
% 6.90/1.48  ------ Instantiation Options
% 6.90/1.48  
% 6.90/1.48  --instantiation_flag                    true
% 6.90/1.48  --inst_sos_flag                         false
% 6.90/1.48  --inst_sos_phase                        true
% 6.90/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.90/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.90/1.48  --inst_lit_sel_side                     num_symb
% 6.90/1.48  --inst_solver_per_active                1400
% 6.90/1.48  --inst_solver_calls_frac                1.
% 6.90/1.48  --inst_passive_queue_type               priority_queues
% 6.90/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.90/1.48  --inst_passive_queues_freq              [25;2]
% 6.90/1.48  --inst_dismatching                      true
% 6.90/1.48  --inst_eager_unprocessed_to_passive     true
% 6.90/1.48  --inst_prop_sim_given                   true
% 6.90/1.48  --inst_prop_sim_new                     false
% 6.90/1.48  --inst_subs_new                         false
% 6.90/1.48  --inst_eq_res_simp                      false
% 6.90/1.48  --inst_subs_given                       false
% 6.90/1.48  --inst_orphan_elimination               true
% 6.90/1.48  --inst_learning_loop_flag               true
% 6.90/1.48  --inst_learning_start                   3000
% 6.90/1.48  --inst_learning_factor                  2
% 6.90/1.48  --inst_start_prop_sim_after_learn       3
% 6.90/1.48  --inst_sel_renew                        solver
% 6.90/1.48  --inst_lit_activity_flag                true
% 6.90/1.48  --inst_restr_to_given                   false
% 6.90/1.48  --inst_activity_threshold               500
% 6.90/1.48  --inst_out_proof                        true
% 6.90/1.48  
% 6.90/1.48  ------ Resolution Options
% 6.90/1.48  
% 6.90/1.48  --resolution_flag                       true
% 6.90/1.48  --res_lit_sel                           adaptive
% 6.90/1.48  --res_lit_sel_side                      none
% 6.90/1.48  --res_ordering                          kbo
% 6.90/1.48  --res_to_prop_solver                    active
% 6.90/1.48  --res_prop_simpl_new                    false
% 6.90/1.48  --res_prop_simpl_given                  true
% 6.90/1.48  --res_passive_queue_type                priority_queues
% 6.90/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.90/1.48  --res_passive_queues_freq               [15;5]
% 6.90/1.48  --res_forward_subs                      full
% 6.90/1.48  --res_backward_subs                     full
% 6.90/1.48  --res_forward_subs_resolution           true
% 6.90/1.48  --res_backward_subs_resolution          true
% 6.90/1.48  --res_orphan_elimination                true
% 6.90/1.48  --res_time_limit                        2.
% 6.90/1.48  --res_out_proof                         true
% 6.90/1.48  
% 6.90/1.48  ------ Superposition Options
% 6.90/1.48  
% 6.90/1.48  --superposition_flag                    true
% 6.90/1.48  --sup_passive_queue_type                priority_queues
% 6.90/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.90/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.90/1.48  --demod_completeness_check              fast
% 6.90/1.48  --demod_use_ground                      true
% 6.90/1.48  --sup_to_prop_solver                    passive
% 6.90/1.48  --sup_prop_simpl_new                    true
% 6.90/1.48  --sup_prop_simpl_given                  true
% 6.90/1.48  --sup_fun_splitting                     false
% 6.90/1.48  --sup_smt_interval                      50000
% 6.90/1.48  
% 6.90/1.48  ------ Superposition Simplification Setup
% 6.90/1.48  
% 6.90/1.48  --sup_indices_passive                   []
% 6.90/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.90/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.90/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.90/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.90/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.90/1.48  --sup_full_bw                           [BwDemod]
% 6.90/1.48  --sup_immed_triv                        [TrivRules]
% 6.90/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.90/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.90/1.48  --sup_immed_bw_main                     []
% 6.90/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.90/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.90/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.90/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.90/1.48  
% 6.90/1.48  ------ Combination Options
% 6.90/1.48  
% 6.90/1.48  --comb_res_mult                         3
% 6.90/1.48  --comb_sup_mult                         2
% 6.90/1.48  --comb_inst_mult                        10
% 6.90/1.48  
% 6.90/1.48  ------ Debug Options
% 6.90/1.48  
% 6.90/1.48  --dbg_backtrace                         false
% 6.90/1.48  --dbg_dump_prop_clauses                 false
% 6.90/1.48  --dbg_dump_prop_clauses_file            -
% 6.90/1.48  --dbg_out_stat                          false
% 6.90/1.48  ------ Parsing...
% 6.90/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.90/1.48  
% 6.90/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.90/1.48  
% 6.90/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.90/1.48  
% 6.90/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.90/1.48  ------ Proving...
% 6.90/1.48  ------ Problem Properties 
% 6.90/1.48  
% 6.90/1.48  
% 6.90/1.48  clauses                                 8
% 6.90/1.48  conjectures                             2
% 6.90/1.48  EPR                                     1
% 6.90/1.48  Horn                                    8
% 6.90/1.48  unary                                   6
% 6.90/1.48  binary                                  2
% 6.90/1.48  lits                                    10
% 6.90/1.48  lits eq                                 4
% 6.90/1.48  fd_pure                                 0
% 6.90/1.48  fd_pseudo                               0
% 6.90/1.48  fd_cond                                 0
% 6.90/1.48  fd_pseudo_cond                          0
% 6.90/1.48  AC symbols                              1
% 6.90/1.48  
% 6.90/1.48  ------ Schedule dynamic 5 is on 
% 6.90/1.48  
% 6.90/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.90/1.48  
% 6.90/1.48  
% 6.90/1.48  ------ 
% 6.90/1.48  Current options:
% 6.90/1.48  ------ 
% 6.90/1.48  
% 6.90/1.48  ------ Input Options
% 6.90/1.48  
% 6.90/1.48  --out_options                           all
% 6.90/1.48  --tptp_safe_out                         true
% 6.90/1.48  --problem_path                          ""
% 6.90/1.48  --include_path                          ""
% 6.90/1.48  --clausifier                            res/vclausify_rel
% 6.90/1.48  --clausifier_options                    --mode clausify
% 6.90/1.48  --stdin                                 false
% 6.90/1.48  --stats_out                             all
% 6.90/1.48  
% 6.90/1.48  ------ General Options
% 6.90/1.48  
% 6.90/1.48  --fof                                   false
% 6.90/1.48  --time_out_real                         305.
% 6.90/1.48  --time_out_virtual                      -1.
% 6.90/1.48  --symbol_type_check                     false
% 6.90/1.48  --clausify_out                          false
% 6.90/1.48  --sig_cnt_out                           false
% 6.90/1.48  --trig_cnt_out                          false
% 6.90/1.48  --trig_cnt_out_tolerance                1.
% 6.90/1.48  --trig_cnt_out_sk_spl                   false
% 6.90/1.48  --abstr_cl_out                          false
% 6.90/1.48  
% 6.90/1.48  ------ Global Options
% 6.90/1.48  
% 6.90/1.48  --schedule                              default
% 6.90/1.48  --add_important_lit                     false
% 6.90/1.48  --prop_solver_per_cl                    1000
% 6.90/1.48  --min_unsat_core                        false
% 6.90/1.48  --soft_assumptions                      false
% 6.90/1.48  --soft_lemma_size                       3
% 6.90/1.48  --prop_impl_unit_size                   0
% 6.90/1.48  --prop_impl_unit                        []
% 6.90/1.48  --share_sel_clauses                     true
% 6.90/1.48  --reset_solvers                         false
% 6.90/1.48  --bc_imp_inh                            [conj_cone]
% 6.90/1.48  --conj_cone_tolerance                   3.
% 6.90/1.48  --extra_neg_conj                        none
% 6.90/1.48  --large_theory_mode                     true
% 6.90/1.48  --prolific_symb_bound                   200
% 6.90/1.48  --lt_threshold                          2000
% 6.90/1.48  --clause_weak_htbl                      true
% 6.90/1.48  --gc_record_bc_elim                     false
% 6.90/1.48  
% 6.90/1.48  ------ Preprocessing Options
% 6.90/1.48  
% 6.90/1.48  --preprocessing_flag                    true
% 6.90/1.48  --time_out_prep_mult                    0.1
% 6.90/1.48  --splitting_mode                        input
% 6.90/1.48  --splitting_grd                         true
% 6.90/1.48  --splitting_cvd                         false
% 6.90/1.48  --splitting_cvd_svl                     false
% 6.90/1.48  --splitting_nvd                         32
% 6.90/1.48  --sub_typing                            true
% 6.90/1.48  --prep_gs_sim                           true
% 6.90/1.48  --prep_unflatten                        true
% 6.90/1.48  --prep_res_sim                          true
% 6.90/1.48  --prep_upred                            true
% 6.90/1.48  --prep_sem_filter                       exhaustive
% 6.90/1.48  --prep_sem_filter_out                   false
% 6.90/1.48  --pred_elim                             true
% 6.90/1.48  --res_sim_input                         true
% 6.90/1.48  --eq_ax_congr_red                       true
% 6.90/1.48  --pure_diseq_elim                       true
% 6.90/1.48  --brand_transform                       false
% 6.90/1.48  --non_eq_to_eq                          false
% 6.90/1.48  --prep_def_merge                        true
% 6.90/1.48  --prep_def_merge_prop_impl              false
% 6.90/1.48  --prep_def_merge_mbd                    true
% 6.90/1.48  --prep_def_merge_tr_red                 false
% 6.90/1.48  --prep_def_merge_tr_cl                  false
% 6.90/1.48  --smt_preprocessing                     true
% 6.90/1.48  --smt_ac_axioms                         fast
% 6.90/1.48  --preprocessed_out                      false
% 6.90/1.48  --preprocessed_stats                    false
% 6.90/1.48  
% 6.90/1.48  ------ Abstraction refinement Options
% 6.90/1.48  
% 6.90/1.48  --abstr_ref                             []
% 6.90/1.48  --abstr_ref_prep                        false
% 6.90/1.48  --abstr_ref_until_sat                   false
% 6.90/1.48  --abstr_ref_sig_restrict                funpre
% 6.90/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.90/1.48  --abstr_ref_under                       []
% 6.90/1.48  
% 6.90/1.48  ------ SAT Options
% 6.90/1.48  
% 6.90/1.48  --sat_mode                              false
% 6.90/1.48  --sat_fm_restart_options                ""
% 6.90/1.48  --sat_gr_def                            false
% 6.90/1.48  --sat_epr_types                         true
% 6.90/1.48  --sat_non_cyclic_types                  false
% 6.90/1.48  --sat_finite_models                     false
% 6.90/1.48  --sat_fm_lemmas                         false
% 6.90/1.48  --sat_fm_prep                           false
% 6.90/1.48  --sat_fm_uc_incr                        true
% 6.90/1.48  --sat_out_model                         small
% 6.90/1.48  --sat_out_clauses                       false
% 6.90/1.48  
% 6.90/1.48  ------ QBF Options
% 6.90/1.48  
% 6.90/1.48  --qbf_mode                              false
% 6.90/1.48  --qbf_elim_univ                         false
% 6.90/1.48  --qbf_dom_inst                          none
% 6.90/1.48  --qbf_dom_pre_inst                      false
% 6.90/1.48  --qbf_sk_in                             false
% 6.90/1.48  --qbf_pred_elim                         true
% 6.90/1.48  --qbf_split                             512
% 6.90/1.48  
% 6.90/1.48  ------ BMC1 Options
% 6.90/1.48  
% 6.90/1.48  --bmc1_incremental                      false
% 6.90/1.48  --bmc1_axioms                           reachable_all
% 6.90/1.48  --bmc1_min_bound                        0
% 6.90/1.48  --bmc1_max_bound                        -1
% 6.90/1.48  --bmc1_max_bound_default                -1
% 6.90/1.48  --bmc1_symbol_reachability              true
% 6.90/1.48  --bmc1_property_lemmas                  false
% 6.90/1.48  --bmc1_k_induction                      false
% 6.90/1.48  --bmc1_non_equiv_states                 false
% 6.90/1.48  --bmc1_deadlock                         false
% 6.90/1.48  --bmc1_ucm                              false
% 6.90/1.48  --bmc1_add_unsat_core                   none
% 6.90/1.48  --bmc1_unsat_core_children              false
% 6.90/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.90/1.48  --bmc1_out_stat                         full
% 6.90/1.48  --bmc1_ground_init                      false
% 6.90/1.48  --bmc1_pre_inst_next_state              false
% 6.90/1.48  --bmc1_pre_inst_state                   false
% 6.90/1.48  --bmc1_pre_inst_reach_state             false
% 6.90/1.48  --bmc1_out_unsat_core                   false
% 6.90/1.48  --bmc1_aig_witness_out                  false
% 6.90/1.48  --bmc1_verbose                          false
% 6.90/1.48  --bmc1_dump_clauses_tptp                false
% 6.90/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.90/1.48  --bmc1_dump_file                        -
% 6.90/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.90/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.90/1.48  --bmc1_ucm_extend_mode                  1
% 6.90/1.48  --bmc1_ucm_init_mode                    2
% 6.90/1.48  --bmc1_ucm_cone_mode                    none
% 6.90/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.90/1.48  --bmc1_ucm_relax_model                  4
% 6.90/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.90/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.90/1.48  --bmc1_ucm_layered_model                none
% 6.90/1.48  --bmc1_ucm_max_lemma_size               10
% 6.90/1.48  
% 6.90/1.48  ------ AIG Options
% 6.90/1.48  
% 6.90/1.48  --aig_mode                              false
% 6.90/1.48  
% 6.90/1.48  ------ Instantiation Options
% 6.90/1.48  
% 6.90/1.48  --instantiation_flag                    true
% 6.90/1.48  --inst_sos_flag                         false
% 6.90/1.48  --inst_sos_phase                        true
% 6.90/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.90/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.90/1.48  --inst_lit_sel_side                     none
% 6.90/1.48  --inst_solver_per_active                1400
% 6.90/1.48  --inst_solver_calls_frac                1.
% 6.90/1.48  --inst_passive_queue_type               priority_queues
% 6.90/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.90/1.48  --inst_passive_queues_freq              [25;2]
% 6.90/1.48  --inst_dismatching                      true
% 6.90/1.48  --inst_eager_unprocessed_to_passive     true
% 6.90/1.48  --inst_prop_sim_given                   true
% 6.90/1.48  --inst_prop_sim_new                     false
% 6.90/1.48  --inst_subs_new                         false
% 6.90/1.48  --inst_eq_res_simp                      false
% 6.90/1.48  --inst_subs_given                       false
% 6.90/1.48  --inst_orphan_elimination               true
% 6.90/1.48  --inst_learning_loop_flag               true
% 6.90/1.48  --inst_learning_start                   3000
% 6.90/1.48  --inst_learning_factor                  2
% 6.90/1.48  --inst_start_prop_sim_after_learn       3
% 6.90/1.48  --inst_sel_renew                        solver
% 6.90/1.48  --inst_lit_activity_flag                true
% 6.90/1.48  --inst_restr_to_given                   false
% 6.90/1.48  --inst_activity_threshold               500
% 6.90/1.48  --inst_out_proof                        true
% 6.90/1.48  
% 6.90/1.48  ------ Resolution Options
% 6.90/1.48  
% 6.90/1.48  --resolution_flag                       false
% 6.90/1.48  --res_lit_sel                           adaptive
% 6.90/1.48  --res_lit_sel_side                      none
% 6.90/1.48  --res_ordering                          kbo
% 6.90/1.48  --res_to_prop_solver                    active
% 6.90/1.48  --res_prop_simpl_new                    false
% 6.90/1.48  --res_prop_simpl_given                  true
% 6.90/1.48  --res_passive_queue_type                priority_queues
% 6.90/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.90/1.48  --res_passive_queues_freq               [15;5]
% 6.90/1.48  --res_forward_subs                      full
% 6.90/1.48  --res_backward_subs                     full
% 6.90/1.48  --res_forward_subs_resolution           true
% 6.90/1.48  --res_backward_subs_resolution          true
% 6.90/1.48  --res_orphan_elimination                true
% 6.90/1.48  --res_time_limit                        2.
% 6.90/1.48  --res_out_proof                         true
% 6.90/1.48  
% 6.90/1.48  ------ Superposition Options
% 6.90/1.48  
% 6.90/1.48  --superposition_flag                    true
% 6.90/1.48  --sup_passive_queue_type                priority_queues
% 6.90/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.90/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.90/1.48  --demod_completeness_check              fast
% 6.90/1.48  --demod_use_ground                      true
% 6.90/1.48  --sup_to_prop_solver                    passive
% 6.90/1.48  --sup_prop_simpl_new                    true
% 6.90/1.48  --sup_prop_simpl_given                  true
% 6.90/1.48  --sup_fun_splitting                     false
% 6.90/1.48  --sup_smt_interval                      50000
% 6.90/1.48  
% 6.90/1.48  ------ Superposition Simplification Setup
% 6.90/1.48  
% 6.90/1.48  --sup_indices_passive                   []
% 6.90/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.90/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.90/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.90/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.90/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.90/1.48  --sup_full_bw                           [BwDemod]
% 6.90/1.48  --sup_immed_triv                        [TrivRules]
% 6.90/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.90/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.90/1.48  --sup_immed_bw_main                     []
% 6.90/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.90/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.90/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.90/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.90/1.48  
% 6.90/1.48  ------ Combination Options
% 6.90/1.48  
% 6.90/1.48  --comb_res_mult                         3
% 6.90/1.48  --comb_sup_mult                         2
% 6.90/1.48  --comb_inst_mult                        10
% 6.90/1.48  
% 6.90/1.48  ------ Debug Options
% 6.90/1.48  
% 6.90/1.48  --dbg_backtrace                         false
% 6.90/1.48  --dbg_dump_prop_clauses                 false
% 6.90/1.48  --dbg_dump_prop_clauses_file            -
% 6.90/1.48  --dbg_out_stat                          false
% 6.90/1.48  
% 6.90/1.48  
% 6.90/1.48  
% 6.90/1.48  
% 6.90/1.48  ------ Proving...
% 6.90/1.48  
% 6.90/1.48  
% 6.90/1.48  % SZS status Theorem for theBenchmark.p
% 6.90/1.48  
% 6.90/1.48   Resolution empty clause
% 6.90/1.48  
% 6.90/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 6.90/1.48  
% 6.90/1.48  fof(f3,axiom,(
% 6.90/1.48    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 6.90/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.48  
% 6.90/1.48  fof(f17,plain,(
% 6.90/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 6.90/1.48    inference(cnf_transformation,[],[f3])).
% 6.90/1.48  
% 6.90/1.48  fof(f8,conjecture,(
% 6.90/1.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 6.90/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.48  
% 6.90/1.48  fof(f9,negated_conjecture,(
% 6.90/1.48    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 6.90/1.48    inference(negated_conjecture,[],[f8])).
% 6.90/1.48  
% 6.90/1.48  fof(f12,plain,(
% 6.90/1.48    ? [X0,X1,X2] : (~r1_tarski(k4_xboole_0(X0,X2),X1) & r1_tarski(X0,X1))),
% 6.90/1.48    inference(ennf_transformation,[],[f9])).
% 6.90/1.48  
% 6.90/1.48  fof(f13,plain,(
% 6.90/1.48    ? [X0,X1,X2] : (~r1_tarski(k4_xboole_0(X0,X2),X1) & r1_tarski(X0,X1)) => (~r1_tarski(k4_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1))),
% 6.90/1.48    introduced(choice_axiom,[])).
% 6.90/1.48  
% 6.90/1.48  fof(f14,plain,(
% 6.90/1.48    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1)),
% 6.90/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 6.90/1.48  
% 6.90/1.48  fof(f22,plain,(
% 6.90/1.48    r1_tarski(sK0,sK1)),
% 6.90/1.48    inference(cnf_transformation,[],[f14])).
% 6.90/1.48  
% 6.90/1.48  fof(f6,axiom,(
% 6.90/1.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.90/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.48  
% 6.90/1.48  fof(f11,plain,(
% 6.90/1.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.90/1.48    inference(ennf_transformation,[],[f6])).
% 6.90/1.48  
% 6.90/1.48  fof(f20,plain,(
% 6.90/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 6.90/1.48    inference(cnf_transformation,[],[f11])).
% 6.90/1.48  
% 6.90/1.48  fof(f1,axiom,(
% 6.90/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.90/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.48  
% 6.90/1.48  fof(f15,plain,(
% 6.90/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.90/1.48    inference(cnf_transformation,[],[f1])).
% 6.90/1.48  
% 6.90/1.48  fof(f4,axiom,(
% 6.90/1.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 6.90/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.48  
% 6.90/1.48  fof(f18,plain,(
% 6.90/1.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 6.90/1.48    inference(cnf_transformation,[],[f4])).
% 6.90/1.48  
% 6.90/1.48  fof(f7,axiom,(
% 6.90/1.48    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 6.90/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.48  
% 6.90/1.48  fof(f21,plain,(
% 6.90/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 6.90/1.48    inference(cnf_transformation,[],[f7])).
% 6.90/1.48  
% 6.90/1.48  fof(f2,axiom,(
% 6.90/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.90/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.90/1.48  
% 6.90/1.48  fof(f16,plain,(
% 6.90/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.90/1.48    inference(cnf_transformation,[],[f2])).
% 6.90/1.48  
% 6.90/1.48  fof(f24,plain,(
% 6.90/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 6.90/1.48    inference(definition_unfolding,[],[f21,f16,f16])).
% 6.90/1.48  
% 6.90/1.48  fof(f23,plain,(
% 6.90/1.48    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 6.90/1.48    inference(cnf_transformation,[],[f14])).
% 6.90/1.48  
% 6.90/1.48  fof(f25,plain,(
% 6.90/1.48    ~r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),
% 6.90/1.48    inference(definition_unfolding,[],[f23,f16])).
% 6.90/1.48  
% 6.90/1.48  cnf(c_1,plain,
% 6.90/1.48      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 6.90/1.48      inference(cnf_transformation,[],[f17]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_7,negated_conjecture,
% 6.90/1.48      ( r1_tarski(sK0,sK1) ),
% 6.90/1.48      inference(cnf_transformation,[],[f22]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_164,plain,
% 6.90/1.48      ( r1_tarski(sK0,sK1) = iProver_top ),
% 6.90/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_4,plain,
% 6.90/1.48      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 6.90/1.48      inference(cnf_transformation,[],[f20]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_166,plain,
% 6.90/1.48      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 6.90/1.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_1878,plain,
% 6.90/1.48      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 6.90/1.48      inference(superposition,[status(thm)],[c_164,c_166]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_2406,plain,
% 6.90/1.48      ( k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0) ),
% 6.90/1.48      inference(superposition,[status(thm)],[c_1878,c_1]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_0,plain,
% 6.90/1.48      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 6.90/1.48      inference(cnf_transformation,[],[f15]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_2,plain,
% 6.90/1.48      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 6.90/1.48      inference(cnf_transformation,[],[f18]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_168,plain,
% 6.90/1.48      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 6.90/1.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_291,plain,
% 6.90/1.48      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 6.90/1.48      inference(superposition,[status(thm)],[c_0,c_168]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_2994,plain,
% 6.90/1.48      ( r1_tarski(k3_xboole_0(sK0,X0),k3_xboole_0(sK1,X0)) = iProver_top ),
% 6.90/1.48      inference(superposition,[status(thm)],[c_2406,c_291]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_9722,plain,
% 6.90/1.48      ( r1_tarski(sK0,k3_xboole_0(sK1,sK1)) = iProver_top ),
% 6.90/1.48      inference(superposition,[status(thm)],[c_1878,c_2994]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_9957,plain,
% 6.90/1.48      ( k3_xboole_0(sK0,k3_xboole_0(sK1,sK1)) = sK0 ),
% 6.90/1.48      inference(superposition,[status(thm)],[c_9722,c_166]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_9972,plain,
% 6.90/1.48      ( k3_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK1,sK1),X0)) = k3_xboole_0(sK0,X0) ),
% 6.90/1.48      inference(superposition,[status(thm)],[c_9957,c_1]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_11949,plain,
% 6.90/1.48      ( k3_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(sK1,X0))) = k3_xboole_0(sK0,X0) ),
% 6.90/1.48      inference(superposition,[status(thm)],[c_1,c_9972]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_5,plain,
% 6.90/1.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 6.90/1.48      inference(cnf_transformation,[],[f24]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_65,plain,
% 6.90/1.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 6.90/1.48      inference(theory_normalisation,[status(thm)],[c_5,c_1,c_0]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_14772,plain,
% 6.90/1.48      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,X0)) ),
% 6.90/1.48      inference(superposition,[status(thm)],[c_11949,c_65]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_14873,plain,
% 6.90/1.48      ( k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k3_xboole_0(sK1,X0)))) = k5_xboole_0(sK0,k3_xboole_0(sK0,X0)) ),
% 6.90/1.48      inference(light_normalisation,[status(thm)],[c_14772,c_1878]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_390,plain,
% 6.90/1.48      ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X2) = iProver_top ),
% 6.90/1.48      inference(superposition,[status(thm)],[c_1,c_291]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_2426,plain,
% 6.90/1.48      ( r1_tarski(k3_xboole_0(X0,sK0),sK1) = iProver_top ),
% 6.90/1.48      inference(superposition,[status(thm)],[c_1878,c_390]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_2705,plain,
% 6.90/1.48      ( r1_tarski(k3_xboole_0(sK0,X0),sK1) = iProver_top ),
% 6.90/1.48      inference(superposition,[status(thm)],[c_0,c_2426]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_16577,plain,
% 6.90/1.48      ( r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,X0)),sK1) = iProver_top ),
% 6.90/1.48      inference(superposition,[status(thm)],[c_14873,c_2705]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_6,negated_conjecture,
% 6.90/1.48      ( ~ r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
% 6.90/1.48      inference(cnf_transformation,[],[f25]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_165,plain,
% 6.90/1.48      ( r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) != iProver_top ),
% 6.90/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 6.90/1.48  
% 6.90/1.48  cnf(c_31769,plain,
% 6.90/1.48      ( $false ),
% 6.90/1.48      inference(superposition,[status(thm)],[c_16577,c_165]) ).
% 6.90/1.48  
% 6.90/1.48  
% 6.90/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 6.90/1.48  
% 6.90/1.48  ------                               Statistics
% 6.90/1.48  
% 6.90/1.48  ------ General
% 6.90/1.48  
% 6.90/1.48  abstr_ref_over_cycles:                  0
% 6.90/1.48  abstr_ref_under_cycles:                 0
% 6.90/1.48  gc_basic_clause_elim:                   0
% 6.90/1.48  forced_gc_time:                         0
% 6.90/1.48  parsing_time:                           0.007
% 6.90/1.48  unif_index_cands_time:                  0.
% 6.90/1.48  unif_index_add_time:                    0.
% 6.90/1.48  orderings_time:                         0.
% 6.90/1.48  out_proof_time:                         0.005
% 6.90/1.48  total_time:                             0.749
% 6.90/1.48  num_of_symbols:                         37
% 6.90/1.48  num_of_terms:                           30152
% 6.90/1.48  
% 6.90/1.48  ------ Preprocessing
% 6.90/1.48  
% 6.90/1.48  num_of_splits:                          0
% 6.90/1.48  num_of_split_atoms:                     0
% 6.90/1.48  num_of_reused_defs:                     0
% 6.90/1.48  num_eq_ax_congr_red:                    0
% 6.90/1.48  num_of_sem_filtered_clauses:            1
% 6.90/1.48  num_of_subtypes:                        0
% 6.90/1.48  monotx_restored_types:                  0
% 6.90/1.48  sat_num_of_epr_types:                   0
% 6.90/1.48  sat_num_of_non_cyclic_types:            0
% 6.90/1.48  sat_guarded_non_collapsed_types:        0
% 6.90/1.48  num_pure_diseq_elim:                    0
% 6.90/1.48  simp_replaced_by:                       0
% 6.90/1.48  res_preprocessed:                       35
% 6.90/1.48  prep_upred:                             0
% 6.90/1.48  prep_unflattend:                        0
% 6.90/1.48  smt_new_axioms:                         0
% 6.90/1.48  pred_elim_cands:                        1
% 6.90/1.48  pred_elim:                              0
% 6.90/1.48  pred_elim_cl:                           0
% 6.90/1.48  pred_elim_cycles:                       1
% 6.90/1.48  merged_defs:                            0
% 6.90/1.48  merged_defs_ncl:                        0
% 6.90/1.48  bin_hyper_res:                          0
% 6.90/1.48  prep_cycles:                            3
% 6.90/1.48  pred_elim_time:                         0.
% 6.90/1.48  splitting_time:                         0.
% 6.90/1.48  sem_filter_time:                        0.
% 6.90/1.48  monotx_time:                            0.
% 6.90/1.48  subtype_inf_time:                       0.
% 6.90/1.48  
% 6.90/1.48  ------ Problem properties
% 6.90/1.48  
% 6.90/1.48  clauses:                                8
% 6.90/1.48  conjectures:                            2
% 6.90/1.48  epr:                                    1
% 6.90/1.48  horn:                                   8
% 6.90/1.48  ground:                                 2
% 6.90/1.48  unary:                                  6
% 6.90/1.48  binary:                                 2
% 6.90/1.48  lits:                                   10
% 6.90/1.48  lits_eq:                                4
% 6.90/1.48  fd_pure:                                0
% 6.90/1.48  fd_pseudo:                              0
% 6.90/1.48  fd_cond:                                0
% 6.90/1.48  fd_pseudo_cond:                         0
% 6.90/1.48  ac_symbols:                             1
% 6.90/1.48  
% 6.90/1.48  ------ Propositional Solver
% 6.90/1.48  
% 6.90/1.48  prop_solver_calls:                      26
% 6.90/1.48  prop_fast_solver_calls:                 266
% 6.90/1.48  smt_solver_calls:                       0
% 6.90/1.48  smt_fast_solver_calls:                  0
% 6.90/1.48  prop_num_of_clauses:                    7919
% 6.90/1.48  prop_preprocess_simplified:             9687
% 6.90/1.48  prop_fo_subsumed:                       0
% 6.90/1.48  prop_solver_time:                       0.
% 6.90/1.48  smt_solver_time:                        0.
% 6.90/1.48  smt_fast_solver_time:                   0.
% 6.90/1.48  prop_fast_solver_time:                  0.
% 6.90/1.48  prop_unsat_core_time:                   0.
% 6.90/1.48  
% 6.90/1.48  ------ QBF
% 6.90/1.48  
% 6.90/1.48  qbf_q_res:                              0
% 6.90/1.48  qbf_num_tautologies:                    0
% 6.90/1.48  qbf_prep_cycles:                        0
% 6.90/1.48  
% 6.90/1.48  ------ BMC1
% 6.90/1.48  
% 6.90/1.48  bmc1_current_bound:                     -1
% 6.90/1.48  bmc1_last_solved_bound:                 -1
% 6.90/1.48  bmc1_unsat_core_size:                   -1
% 6.90/1.48  bmc1_unsat_core_parents_size:           -1
% 6.90/1.48  bmc1_merge_next_fun:                    0
% 6.90/1.48  bmc1_unsat_core_clauses_time:           0.
% 6.90/1.48  
% 6.90/1.48  ------ Instantiation
% 6.90/1.48  
% 6.90/1.48  inst_num_of_clauses:                    1368
% 6.90/1.48  inst_num_in_passive:                    471
% 6.90/1.48  inst_num_in_active:                     664
% 6.90/1.48  inst_num_in_unprocessed:                238
% 6.90/1.48  inst_num_of_loops:                      720
% 6.90/1.48  inst_num_of_learning_restarts:          0
% 6.90/1.48  inst_num_moves_active_passive:          52
% 6.90/1.48  inst_lit_activity:                      0
% 6.90/1.48  inst_lit_activity_moves:                0
% 6.90/1.48  inst_num_tautologies:                   0
% 6.90/1.48  inst_num_prop_implied:                  0
% 6.90/1.48  inst_num_existing_simplified:           0
% 6.90/1.48  inst_num_eq_res_simplified:             0
% 6.90/1.48  inst_num_child_elim:                    0
% 6.90/1.48  inst_num_of_dismatching_blockings:      2580
% 6.90/1.48  inst_num_of_non_proper_insts:           3282
% 6.90/1.48  inst_num_of_duplicates:                 0
% 6.90/1.48  inst_inst_num_from_inst_to_res:         0
% 6.90/1.48  inst_dismatching_checking_time:         0.
% 6.90/1.48  
% 6.90/1.48  ------ Resolution
% 6.90/1.48  
% 6.90/1.48  res_num_of_clauses:                     0
% 6.90/1.48  res_num_in_passive:                     0
% 6.90/1.48  res_num_in_active:                      0
% 6.90/1.48  res_num_of_loops:                       38
% 6.90/1.48  res_forward_subset_subsumed:            171
% 6.90/1.48  res_backward_subset_subsumed:           20
% 6.90/1.48  res_forward_subsumed:                   0
% 6.90/1.48  res_backward_subsumed:                  0
% 6.90/1.48  res_forward_subsumption_resolution:     0
% 6.90/1.48  res_backward_subsumption_resolution:    0
% 6.90/1.48  res_clause_to_clause_subsumption:       26696
% 6.90/1.48  res_orphan_elimination:                 0
% 6.90/1.48  res_tautology_del:                      149
% 6.90/1.48  res_num_eq_res_simplified:              0
% 6.90/1.48  res_num_sel_changes:                    0
% 6.90/1.48  res_moves_from_active_to_pass:          0
% 6.90/1.48  
% 6.90/1.48  ------ Superposition
% 6.90/1.48  
% 6.90/1.48  sup_time_total:                         0.
% 6.90/1.48  sup_time_generating:                    0.
% 6.90/1.48  sup_time_sim_full:                      0.
% 6.90/1.48  sup_time_sim_immed:                     0.
% 6.90/1.48  
% 6.90/1.48  sup_num_of_clauses:                     2142
% 6.90/1.48  sup_num_in_active:                      139
% 6.90/1.48  sup_num_in_passive:                     2003
% 6.90/1.48  sup_num_of_loops:                       142
% 6.90/1.48  sup_fw_superposition:                   3045
% 6.90/1.48  sup_bw_superposition:                   3856
% 6.90/1.48  sup_immediate_simplified:               2182
% 6.90/1.48  sup_given_eliminated:                   2
% 6.90/1.48  comparisons_done:                       0
% 6.90/1.48  comparisons_avoided:                    0
% 6.90/1.48  
% 6.90/1.48  ------ Simplifications
% 6.90/1.48  
% 6.90/1.48  
% 6.90/1.48  sim_fw_subset_subsumed:                 0
% 6.90/1.48  sim_bw_subset_subsumed:                 0
% 6.90/1.48  sim_fw_subsumed:                        599
% 6.90/1.48  sim_bw_subsumed:                        14
% 6.90/1.48  sim_fw_subsumption_res:                 0
% 6.90/1.48  sim_bw_subsumption_res:                 0
% 6.90/1.48  sim_tautology_del:                      5
% 6.90/1.48  sim_eq_tautology_del:                   101
% 6.90/1.48  sim_eq_res_simp:                        0
% 6.90/1.48  sim_fw_demodulated:                     671
% 6.90/1.48  sim_bw_demodulated:                     346
% 6.90/1.48  sim_light_normalised:                   1056
% 6.90/1.48  sim_joinable_taut:                      66
% 6.90/1.48  sim_joinable_simp:                      0
% 6.90/1.48  sim_ac_normalised:                      0
% 6.90/1.48  sim_smt_subsumption:                    0
% 6.90/1.48  
%------------------------------------------------------------------------------
