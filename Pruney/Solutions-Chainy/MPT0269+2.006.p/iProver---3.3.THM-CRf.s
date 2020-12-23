%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:46 EST 2020

% Result     : Theorem 0.83s
% Output     : CNFRefutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   43 (  62 expanded)
%              Number of clauses        :   20 (  21 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :   13
%              Number of atoms          :   82 ( 127 expanded)
%              Number of equality atoms :   81 ( 126 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1] :
      ~ ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0
          & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_tarski(X1) != X0
      & k1_xboole_0 != X0
      & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( k1_tarski(X1) != X0
        & k1_xboole_0 != X0
        & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)) )
   => ( k1_tarski(sK1) != sK0
      & k1_xboole_0 != sK0
      & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( k1_tarski(sK1) != sK0
    & k1_xboole_0 != sK0
    & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f19,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f25,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK1)) ),
    inference(definition_unfolding,[],[f19,f16])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k2_xboole_0(X1,X2) != k2_tarski(X0,X0) ) ),
    inference(definition_unfolding,[],[f17,f16])).

fof(f20,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f21,plain,(
    k1_tarski(sK1) != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,(
    k2_tarski(sK1,sK1) != sK0 ),
    inference(definition_unfolding,[],[f21,f16])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k2_tarski(X0,X0),X1) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f18,f16])).

cnf(c_7,negated_conjecture,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_229,plain,
    ( k2_xboole_0(k2_tarski(sK1,sK1),sK0) = k2_xboole_0(k2_tarski(sK1,sK1),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7,c_2])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_236,plain,
    ( k2_xboole_0(k2_tarski(sK1,sK1),sK0) = k2_tarski(sK1,sK1) ),
    inference(demodulation,[status(thm)],[c_229,c_1])).

cnf(c_3,plain,
    ( X0 = X1
    | k2_tarski(X2,X2) != k2_xboole_0(X1,X0)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_315,plain,
    ( k2_tarski(X0,X0) != k2_tarski(sK1,sK1)
    | k2_tarski(sK1,sK1) = sK0
    | k2_tarski(sK1,sK1) = k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_236,c_3])).

cnf(c_6,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_5,negated_conjecture,
    ( k2_tarski(sK1,sK1) != sK0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_18,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_25,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_19,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_51,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_52,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_452,plain,
    ( k2_tarski(sK1,sK1) = k1_xboole_0
    | k2_tarski(X0,X0) != k2_tarski(sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_315,c_6,c_5,c_25,c_52])).

cnf(c_453,plain,
    ( k2_tarski(X0,X0) != k2_tarski(sK1,sK1)
    | k2_tarski(sK1,sK1) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_452])).

cnf(c_4,plain,
    ( k2_xboole_0(k2_tarski(X0,X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_182,plain,
    ( k2_tarski(X0,X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_457,plain,
    ( k2_tarski(X0,X0) != k2_tarski(sK1,sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_453,c_182])).

cnf(c_459,plain,
    ( $false ),
    inference(equality_resolution,[status(thm)],[c_457])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.10  % Command    : iproveropt_run.sh %d %s
% 0.10/0.30  % Computer   : n021.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 15:19:04 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.30  % Running in FOF mode
% 0.83/0.95  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.83/0.95  
% 0.83/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.83/0.95  
% 0.83/0.95  ------  iProver source info
% 0.83/0.95  
% 0.83/0.95  git: date: 2020-06-30 10:37:57 +0100
% 0.83/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.83/0.95  git: non_committed_changes: false
% 0.83/0.95  git: last_make_outside_of_git: false
% 0.83/0.95  
% 0.83/0.95  ------ 
% 0.83/0.95  
% 0.83/0.95  ------ Input Options
% 0.83/0.95  
% 0.83/0.95  --out_options                           all
% 0.83/0.95  --tptp_safe_out                         true
% 0.83/0.95  --problem_path                          ""
% 0.83/0.95  --include_path                          ""
% 0.83/0.95  --clausifier                            res/vclausify_rel
% 0.83/0.95  --clausifier_options                    --mode clausify
% 0.83/0.95  --stdin                                 false
% 0.83/0.95  --stats_out                             all
% 0.83/0.95  
% 0.83/0.95  ------ General Options
% 0.83/0.95  
% 0.83/0.95  --fof                                   false
% 0.83/0.95  --time_out_real                         305.
% 0.83/0.95  --time_out_virtual                      -1.
% 0.83/0.95  --symbol_type_check                     false
% 0.83/0.95  --clausify_out                          false
% 0.83/0.95  --sig_cnt_out                           false
% 0.83/0.95  --trig_cnt_out                          false
% 0.83/0.95  --trig_cnt_out_tolerance                1.
% 0.83/0.95  --trig_cnt_out_sk_spl                   false
% 0.83/0.95  --abstr_cl_out                          false
% 0.83/0.95  
% 0.83/0.95  ------ Global Options
% 0.83/0.95  
% 0.83/0.95  --schedule                              default
% 0.83/0.95  --add_important_lit                     false
% 0.83/0.95  --prop_solver_per_cl                    1000
% 0.83/0.95  --min_unsat_core                        false
% 0.83/0.95  --soft_assumptions                      false
% 0.83/0.95  --soft_lemma_size                       3
% 0.83/0.95  --prop_impl_unit_size                   0
% 0.83/0.95  --prop_impl_unit                        []
% 0.83/0.95  --share_sel_clauses                     true
% 0.83/0.95  --reset_solvers                         false
% 0.83/0.95  --bc_imp_inh                            [conj_cone]
% 0.83/0.95  --conj_cone_tolerance                   3.
% 0.83/0.95  --extra_neg_conj                        none
% 0.83/0.95  --large_theory_mode                     true
% 0.83/0.95  --prolific_symb_bound                   200
% 0.83/0.95  --lt_threshold                          2000
% 0.83/0.95  --clause_weak_htbl                      true
% 0.83/0.95  --gc_record_bc_elim                     false
% 0.83/0.95  
% 0.83/0.95  ------ Preprocessing Options
% 0.83/0.95  
% 0.83/0.95  --preprocessing_flag                    true
% 0.83/0.95  --time_out_prep_mult                    0.1
% 0.83/0.95  --splitting_mode                        input
% 0.83/0.95  --splitting_grd                         true
% 0.83/0.95  --splitting_cvd                         false
% 0.83/0.95  --splitting_cvd_svl                     false
% 0.83/0.95  --splitting_nvd                         32
% 0.83/0.95  --sub_typing                            true
% 0.83/0.95  --prep_gs_sim                           true
% 0.83/0.95  --prep_unflatten                        true
% 0.83/0.95  --prep_res_sim                          true
% 0.83/0.95  --prep_upred                            true
% 0.83/0.95  --prep_sem_filter                       exhaustive
% 0.83/0.95  --prep_sem_filter_out                   false
% 0.83/0.95  --pred_elim                             true
% 0.83/0.95  --res_sim_input                         true
% 0.83/0.95  --eq_ax_congr_red                       true
% 0.83/0.95  --pure_diseq_elim                       true
% 0.83/0.95  --brand_transform                       false
% 0.83/0.95  --non_eq_to_eq                          false
% 0.83/0.95  --prep_def_merge                        true
% 0.83/0.95  --prep_def_merge_prop_impl              false
% 0.83/0.95  --prep_def_merge_mbd                    true
% 0.83/0.95  --prep_def_merge_tr_red                 false
% 0.83/0.95  --prep_def_merge_tr_cl                  false
% 0.83/0.95  --smt_preprocessing                     true
% 0.83/0.95  --smt_ac_axioms                         fast
% 0.83/0.95  --preprocessed_out                      false
% 0.83/0.95  --preprocessed_stats                    false
% 0.83/0.95  
% 0.83/0.95  ------ Abstraction refinement Options
% 0.83/0.95  
% 0.83/0.95  --abstr_ref                             []
% 0.83/0.95  --abstr_ref_prep                        false
% 0.83/0.95  --abstr_ref_until_sat                   false
% 0.83/0.95  --abstr_ref_sig_restrict                funpre
% 0.83/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 0.83/0.95  --abstr_ref_under                       []
% 0.83/0.95  
% 0.83/0.95  ------ SAT Options
% 0.83/0.95  
% 0.83/0.95  --sat_mode                              false
% 0.83/0.95  --sat_fm_restart_options                ""
% 0.83/0.95  --sat_gr_def                            false
% 0.83/0.95  --sat_epr_types                         true
% 0.83/0.95  --sat_non_cyclic_types                  false
% 0.83/0.95  --sat_finite_models                     false
% 0.83/0.95  --sat_fm_lemmas                         false
% 0.83/0.95  --sat_fm_prep                           false
% 0.83/0.95  --sat_fm_uc_incr                        true
% 0.83/0.95  --sat_out_model                         small
% 0.83/0.95  --sat_out_clauses                       false
% 0.83/0.95  
% 0.83/0.95  ------ QBF Options
% 0.83/0.95  
% 0.83/0.95  --qbf_mode                              false
% 0.83/0.95  --qbf_elim_univ                         false
% 0.83/0.95  --qbf_dom_inst                          none
% 0.83/0.95  --qbf_dom_pre_inst                      false
% 0.83/0.95  --qbf_sk_in                             false
% 0.83/0.95  --qbf_pred_elim                         true
% 0.83/0.95  --qbf_split                             512
% 0.83/0.95  
% 0.83/0.95  ------ BMC1 Options
% 0.83/0.95  
% 0.83/0.95  --bmc1_incremental                      false
% 0.83/0.95  --bmc1_axioms                           reachable_all
% 0.83/0.95  --bmc1_min_bound                        0
% 0.83/0.95  --bmc1_max_bound                        -1
% 0.83/0.95  --bmc1_max_bound_default                -1
% 0.83/0.95  --bmc1_symbol_reachability              true
% 0.83/0.95  --bmc1_property_lemmas                  false
% 0.83/0.95  --bmc1_k_induction                      false
% 0.83/0.95  --bmc1_non_equiv_states                 false
% 0.83/0.95  --bmc1_deadlock                         false
% 0.83/0.95  --bmc1_ucm                              false
% 0.83/0.95  --bmc1_add_unsat_core                   none
% 0.83/0.95  --bmc1_unsat_core_children              false
% 0.83/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 0.83/0.95  --bmc1_out_stat                         full
% 0.83/0.95  --bmc1_ground_init                      false
% 0.83/0.95  --bmc1_pre_inst_next_state              false
% 0.83/0.95  --bmc1_pre_inst_state                   false
% 0.83/0.95  --bmc1_pre_inst_reach_state             false
% 0.83/0.95  --bmc1_out_unsat_core                   false
% 0.83/0.95  --bmc1_aig_witness_out                  false
% 0.83/0.95  --bmc1_verbose                          false
% 0.83/0.95  --bmc1_dump_clauses_tptp                false
% 0.83/0.95  --bmc1_dump_unsat_core_tptp             false
% 0.83/0.95  --bmc1_dump_file                        -
% 0.83/0.95  --bmc1_ucm_expand_uc_limit              128
% 0.83/0.95  --bmc1_ucm_n_expand_iterations          6
% 0.83/0.95  --bmc1_ucm_extend_mode                  1
% 0.83/0.95  --bmc1_ucm_init_mode                    2
% 0.83/0.95  --bmc1_ucm_cone_mode                    none
% 0.83/0.95  --bmc1_ucm_reduced_relation_type        0
% 0.83/0.95  --bmc1_ucm_relax_model                  4
% 0.83/0.95  --bmc1_ucm_full_tr_after_sat            true
% 0.83/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 0.83/0.95  --bmc1_ucm_layered_model                none
% 0.83/0.95  --bmc1_ucm_max_lemma_size               10
% 0.83/0.95  
% 0.83/0.95  ------ AIG Options
% 0.83/0.95  
% 0.83/0.95  --aig_mode                              false
% 0.83/0.95  
% 0.83/0.95  ------ Instantiation Options
% 0.83/0.95  
% 0.83/0.95  --instantiation_flag                    true
% 0.83/0.95  --inst_sos_flag                         false
% 0.83/0.95  --inst_sos_phase                        true
% 0.83/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.83/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.83/0.95  --inst_lit_sel_side                     num_symb
% 0.83/0.95  --inst_solver_per_active                1400
% 0.83/0.95  --inst_solver_calls_frac                1.
% 0.83/0.95  --inst_passive_queue_type               priority_queues
% 0.83/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.83/0.95  --inst_passive_queues_freq              [25;2]
% 0.83/0.95  --inst_dismatching                      true
% 0.83/0.95  --inst_eager_unprocessed_to_passive     true
% 0.83/0.95  --inst_prop_sim_given                   true
% 0.83/0.95  --inst_prop_sim_new                     false
% 0.83/0.95  --inst_subs_new                         false
% 0.83/0.95  --inst_eq_res_simp                      false
% 0.83/0.95  --inst_subs_given                       false
% 0.83/0.95  --inst_orphan_elimination               true
% 0.83/0.95  --inst_learning_loop_flag               true
% 0.83/0.95  --inst_learning_start                   3000
% 0.83/0.95  --inst_learning_factor                  2
% 0.83/0.95  --inst_start_prop_sim_after_learn       3
% 0.83/0.95  --inst_sel_renew                        solver
% 0.83/0.95  --inst_lit_activity_flag                true
% 0.83/0.95  --inst_restr_to_given                   false
% 0.83/0.95  --inst_activity_threshold               500
% 0.83/0.95  --inst_out_proof                        true
% 0.83/0.95  
% 0.83/0.95  ------ Resolution Options
% 0.83/0.95  
% 0.83/0.95  --resolution_flag                       true
% 0.83/0.95  --res_lit_sel                           adaptive
% 0.83/0.95  --res_lit_sel_side                      none
% 0.83/0.95  --res_ordering                          kbo
% 0.83/0.95  --res_to_prop_solver                    active
% 0.83/0.95  --res_prop_simpl_new                    false
% 0.83/0.95  --res_prop_simpl_given                  true
% 0.83/0.95  --res_passive_queue_type                priority_queues
% 0.83/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.83/0.95  --res_passive_queues_freq               [15;5]
% 0.83/0.95  --res_forward_subs                      full
% 0.83/0.95  --res_backward_subs                     full
% 0.83/0.95  --res_forward_subs_resolution           true
% 0.83/0.95  --res_backward_subs_resolution          true
% 0.83/0.95  --res_orphan_elimination                true
% 0.83/0.95  --res_time_limit                        2.
% 0.83/0.95  --res_out_proof                         true
% 0.83/0.95  
% 0.83/0.95  ------ Superposition Options
% 0.83/0.95  
% 0.83/0.95  --superposition_flag                    true
% 0.83/0.95  --sup_passive_queue_type                priority_queues
% 0.83/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.83/0.95  --sup_passive_queues_freq               [8;1;4]
% 0.83/0.95  --demod_completeness_check              fast
% 0.83/0.95  --demod_use_ground                      true
% 0.83/0.95  --sup_to_prop_solver                    passive
% 0.83/0.95  --sup_prop_simpl_new                    true
% 0.83/0.95  --sup_prop_simpl_given                  true
% 0.83/0.95  --sup_fun_splitting                     false
% 0.83/0.95  --sup_smt_interval                      50000
% 0.83/0.95  
% 0.83/0.95  ------ Superposition Simplification Setup
% 0.83/0.95  
% 0.83/0.95  --sup_indices_passive                   []
% 0.83/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 0.83/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.95  --sup_full_bw                           [BwDemod]
% 0.83/0.95  --sup_immed_triv                        [TrivRules]
% 0.83/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.83/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.95  --sup_immed_bw_main                     []
% 0.83/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 0.83/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/0.95  
% 0.83/0.95  ------ Combination Options
% 0.83/0.95  
% 0.83/0.95  --comb_res_mult                         3
% 0.83/0.95  --comb_sup_mult                         2
% 0.83/0.95  --comb_inst_mult                        10
% 0.83/0.95  
% 0.83/0.95  ------ Debug Options
% 0.83/0.95  
% 0.83/0.95  --dbg_backtrace                         false
% 0.83/0.95  --dbg_dump_prop_clauses                 false
% 0.83/0.95  --dbg_dump_prop_clauses_file            -
% 0.83/0.95  --dbg_out_stat                          false
% 0.83/0.95  ------ Parsing...
% 0.83/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.83/0.95  
% 0.83/0.95  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 0.83/0.95  
% 0.83/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.83/0.95  
% 0.83/0.95  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.83/0.95  ------ Proving...
% 0.83/0.95  ------ Problem Properties 
% 0.83/0.95  
% 0.83/0.95  
% 0.83/0.95  clauses                                 8
% 0.83/0.95  conjectures                             3
% 0.83/0.95  EPR                                     1
% 0.83/0.95  Horn                                    7
% 0.83/0.95  unary                                   7
% 0.83/0.95  binary                                  0
% 0.83/0.95  lits                                    11
% 0.83/0.95  lits eq                                 11
% 0.83/0.95  fd_pure                                 0
% 0.83/0.95  fd_pseudo                               0
% 0.83/0.95  fd_cond                                 0
% 0.83/0.95  fd_pseudo_cond                          1
% 0.83/0.95  AC symbols                              0
% 0.83/0.95  
% 0.83/0.95  ------ Schedule dynamic 5 is on 
% 0.83/0.95  
% 0.83/0.95  ------ pure equality problem: resolution off 
% 0.83/0.95  
% 0.83/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.83/0.95  
% 0.83/0.95  
% 0.83/0.95  ------ 
% 0.83/0.95  Current options:
% 0.83/0.95  ------ 
% 0.83/0.95  
% 0.83/0.95  ------ Input Options
% 0.83/0.95  
% 0.83/0.95  --out_options                           all
% 0.83/0.95  --tptp_safe_out                         true
% 0.83/0.95  --problem_path                          ""
% 0.83/0.95  --include_path                          ""
% 0.83/0.95  --clausifier                            res/vclausify_rel
% 0.83/0.95  --clausifier_options                    --mode clausify
% 0.83/0.95  --stdin                                 false
% 0.83/0.95  --stats_out                             all
% 0.83/0.95  
% 0.83/0.95  ------ General Options
% 0.83/0.95  
% 0.83/0.95  --fof                                   false
% 0.83/0.95  --time_out_real                         305.
% 0.83/0.95  --time_out_virtual                      -1.
% 0.83/0.95  --symbol_type_check                     false
% 0.83/0.95  --clausify_out                          false
% 0.83/0.95  --sig_cnt_out                           false
% 0.83/0.95  --trig_cnt_out                          false
% 0.83/0.95  --trig_cnt_out_tolerance                1.
% 0.83/0.95  --trig_cnt_out_sk_spl                   false
% 0.83/0.95  --abstr_cl_out                          false
% 0.83/0.95  
% 0.83/0.95  ------ Global Options
% 0.83/0.95  
% 0.83/0.95  --schedule                              default
% 0.83/0.95  --add_important_lit                     false
% 0.83/0.95  --prop_solver_per_cl                    1000
% 0.83/0.95  --min_unsat_core                        false
% 0.83/0.95  --soft_assumptions                      false
% 0.83/0.95  --soft_lemma_size                       3
% 0.83/0.95  --prop_impl_unit_size                   0
% 0.83/0.95  --prop_impl_unit                        []
% 0.83/0.95  --share_sel_clauses                     true
% 0.83/0.95  --reset_solvers                         false
% 0.83/0.95  --bc_imp_inh                            [conj_cone]
% 0.83/0.95  --conj_cone_tolerance                   3.
% 0.83/0.95  --extra_neg_conj                        none
% 0.83/0.95  --large_theory_mode                     true
% 0.83/0.95  --prolific_symb_bound                   200
% 0.83/0.95  --lt_threshold                          2000
% 0.83/0.95  --clause_weak_htbl                      true
% 0.83/0.95  --gc_record_bc_elim                     false
% 0.83/0.95  
% 0.83/0.95  ------ Preprocessing Options
% 0.83/0.95  
% 0.83/0.95  --preprocessing_flag                    true
% 0.83/0.95  --time_out_prep_mult                    0.1
% 0.83/0.95  --splitting_mode                        input
% 0.83/0.95  --splitting_grd                         true
% 0.83/0.95  --splitting_cvd                         false
% 0.83/0.95  --splitting_cvd_svl                     false
% 0.83/0.95  --splitting_nvd                         32
% 0.83/0.95  --sub_typing                            true
% 0.83/0.95  --prep_gs_sim                           true
% 0.83/0.95  --prep_unflatten                        true
% 0.83/0.95  --prep_res_sim                          true
% 0.83/0.95  --prep_upred                            true
% 0.83/0.95  --prep_sem_filter                       exhaustive
% 0.83/0.95  --prep_sem_filter_out                   false
% 0.83/0.95  --pred_elim                             true
% 0.83/0.95  --res_sim_input                         true
% 0.83/0.95  --eq_ax_congr_red                       true
% 0.83/0.95  --pure_diseq_elim                       true
% 0.83/0.95  --brand_transform                       false
% 0.83/0.95  --non_eq_to_eq                          false
% 0.83/0.95  --prep_def_merge                        true
% 0.83/0.95  --prep_def_merge_prop_impl              false
% 0.83/0.95  --prep_def_merge_mbd                    true
% 0.83/0.95  --prep_def_merge_tr_red                 false
% 0.83/0.95  --prep_def_merge_tr_cl                  false
% 0.83/0.95  --smt_preprocessing                     true
% 0.83/0.95  --smt_ac_axioms                         fast
% 0.83/0.95  --preprocessed_out                      false
% 0.83/0.95  --preprocessed_stats                    false
% 0.83/0.95  
% 0.83/0.95  ------ Abstraction refinement Options
% 0.83/0.95  
% 0.83/0.95  --abstr_ref                             []
% 0.83/0.95  --abstr_ref_prep                        false
% 0.83/0.95  --abstr_ref_until_sat                   false
% 0.83/0.95  --abstr_ref_sig_restrict                funpre
% 0.83/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 0.83/0.95  --abstr_ref_under                       []
% 0.83/0.95  
% 0.83/0.95  ------ SAT Options
% 0.83/0.95  
% 0.83/0.95  --sat_mode                              false
% 0.83/0.95  --sat_fm_restart_options                ""
% 0.83/0.95  --sat_gr_def                            false
% 0.83/0.95  --sat_epr_types                         true
% 0.83/0.95  --sat_non_cyclic_types                  false
% 0.83/0.95  --sat_finite_models                     false
% 0.83/0.95  --sat_fm_lemmas                         false
% 0.83/0.95  --sat_fm_prep                           false
% 0.83/0.95  --sat_fm_uc_incr                        true
% 0.83/0.95  --sat_out_model                         small
% 0.83/0.95  --sat_out_clauses                       false
% 0.83/0.95  
% 0.83/0.95  ------ QBF Options
% 0.83/0.95  
% 0.83/0.95  --qbf_mode                              false
% 0.83/0.95  --qbf_elim_univ                         false
% 0.83/0.95  --qbf_dom_inst                          none
% 0.83/0.95  --qbf_dom_pre_inst                      false
% 0.83/0.95  --qbf_sk_in                             false
% 0.83/0.95  --qbf_pred_elim                         true
% 0.83/0.95  --qbf_split                             512
% 0.83/0.95  
% 0.83/0.95  ------ BMC1 Options
% 0.83/0.95  
% 0.83/0.95  --bmc1_incremental                      false
% 0.83/0.95  --bmc1_axioms                           reachable_all
% 0.83/0.95  --bmc1_min_bound                        0
% 0.83/0.95  --bmc1_max_bound                        -1
% 0.83/0.95  --bmc1_max_bound_default                -1
% 0.83/0.95  --bmc1_symbol_reachability              true
% 0.83/0.95  --bmc1_property_lemmas                  false
% 0.83/0.95  --bmc1_k_induction                      false
% 0.83/0.95  --bmc1_non_equiv_states                 false
% 0.83/0.95  --bmc1_deadlock                         false
% 0.83/0.95  --bmc1_ucm                              false
% 0.83/0.95  --bmc1_add_unsat_core                   none
% 0.83/0.95  --bmc1_unsat_core_children              false
% 0.83/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 0.83/0.95  --bmc1_out_stat                         full
% 0.83/0.95  --bmc1_ground_init                      false
% 0.83/0.95  --bmc1_pre_inst_next_state              false
% 0.83/0.95  --bmc1_pre_inst_state                   false
% 0.83/0.95  --bmc1_pre_inst_reach_state             false
% 0.83/0.95  --bmc1_out_unsat_core                   false
% 0.83/0.95  --bmc1_aig_witness_out                  false
% 0.83/0.95  --bmc1_verbose                          false
% 0.83/0.95  --bmc1_dump_clauses_tptp                false
% 0.83/0.95  --bmc1_dump_unsat_core_tptp             false
% 0.83/0.95  --bmc1_dump_file                        -
% 0.83/0.95  --bmc1_ucm_expand_uc_limit              128
% 0.83/0.95  --bmc1_ucm_n_expand_iterations          6
% 0.83/0.95  --bmc1_ucm_extend_mode                  1
% 0.83/0.95  --bmc1_ucm_init_mode                    2
% 0.83/0.95  --bmc1_ucm_cone_mode                    none
% 0.83/0.95  --bmc1_ucm_reduced_relation_type        0
% 0.83/0.95  --bmc1_ucm_relax_model                  4
% 0.83/0.95  --bmc1_ucm_full_tr_after_sat            true
% 0.83/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 0.83/0.95  --bmc1_ucm_layered_model                none
% 0.83/0.95  --bmc1_ucm_max_lemma_size               10
% 0.83/0.95  
% 0.83/0.95  ------ AIG Options
% 0.83/0.95  
% 0.83/0.95  --aig_mode                              false
% 0.83/0.95  
% 0.83/0.95  ------ Instantiation Options
% 0.83/0.95  
% 0.83/0.95  --instantiation_flag                    true
% 0.83/0.95  --inst_sos_flag                         false
% 0.83/0.95  --inst_sos_phase                        true
% 0.83/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.83/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.83/0.95  --inst_lit_sel_side                     none
% 0.83/0.95  --inst_solver_per_active                1400
% 0.83/0.95  --inst_solver_calls_frac                1.
% 0.83/0.95  --inst_passive_queue_type               priority_queues
% 0.83/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.83/0.95  --inst_passive_queues_freq              [25;2]
% 0.83/0.95  --inst_dismatching                      true
% 0.83/0.95  --inst_eager_unprocessed_to_passive     true
% 0.83/0.95  --inst_prop_sim_given                   true
% 0.83/0.95  --inst_prop_sim_new                     false
% 0.83/0.95  --inst_subs_new                         false
% 0.83/0.95  --inst_eq_res_simp                      false
% 0.83/0.95  --inst_subs_given                       false
% 0.83/0.95  --inst_orphan_elimination               true
% 0.83/0.95  --inst_learning_loop_flag               true
% 0.83/0.95  --inst_learning_start                   3000
% 0.83/0.95  --inst_learning_factor                  2
% 0.83/0.95  --inst_start_prop_sim_after_learn       3
% 0.83/0.95  --inst_sel_renew                        solver
% 0.83/0.95  --inst_lit_activity_flag                true
% 0.83/0.95  --inst_restr_to_given                   false
% 0.83/0.95  --inst_activity_threshold               500
% 0.83/0.95  --inst_out_proof                        true
% 0.83/0.95  
% 0.83/0.95  ------ Resolution Options
% 0.83/0.95  
% 0.83/0.95  --resolution_flag                       false
% 0.83/0.95  --res_lit_sel                           adaptive
% 0.83/0.95  --res_lit_sel_side                      none
% 0.83/0.95  --res_ordering                          kbo
% 0.83/0.95  --res_to_prop_solver                    active
% 0.83/0.95  --res_prop_simpl_new                    false
% 0.83/0.95  --res_prop_simpl_given                  true
% 0.83/0.95  --res_passive_queue_type                priority_queues
% 0.83/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.83/0.95  --res_passive_queues_freq               [15;5]
% 0.83/0.95  --res_forward_subs                      full
% 0.83/0.95  --res_backward_subs                     full
% 0.83/0.95  --res_forward_subs_resolution           true
% 0.83/0.95  --res_backward_subs_resolution          true
% 0.83/0.95  --res_orphan_elimination                true
% 0.83/0.95  --res_time_limit                        2.
% 0.83/0.95  --res_out_proof                         true
% 0.83/0.95  
% 0.83/0.95  ------ Superposition Options
% 0.83/0.95  
% 0.83/0.95  --superposition_flag                    true
% 0.83/0.95  --sup_passive_queue_type                priority_queues
% 0.83/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.83/0.95  --sup_passive_queues_freq               [8;1;4]
% 0.83/0.95  --demod_completeness_check              fast
% 0.83/0.95  --demod_use_ground                      true
% 0.83/0.95  --sup_to_prop_solver                    passive
% 0.83/0.95  --sup_prop_simpl_new                    true
% 0.83/0.95  --sup_prop_simpl_given                  true
% 0.83/0.95  --sup_fun_splitting                     false
% 0.83/0.95  --sup_smt_interval                      50000
% 0.83/0.95  
% 0.83/0.95  ------ Superposition Simplification Setup
% 0.83/0.95  
% 0.83/0.95  --sup_indices_passive                   []
% 0.83/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 0.83/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.95  --sup_full_bw                           [BwDemod]
% 0.83/0.95  --sup_immed_triv                        [TrivRules]
% 0.83/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.83/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.95  --sup_immed_bw_main                     []
% 0.83/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 0.83/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/0.95  
% 0.83/0.95  ------ Combination Options
% 0.83/0.95  
% 0.83/0.95  --comb_res_mult                         3
% 0.83/0.95  --comb_sup_mult                         2
% 0.83/0.95  --comb_inst_mult                        10
% 0.83/0.95  
% 0.83/0.95  ------ Debug Options
% 0.83/0.95  
% 0.83/0.95  --dbg_backtrace                         false
% 0.83/0.95  --dbg_dump_prop_clauses                 false
% 0.83/0.95  --dbg_dump_prop_clauses_file            -
% 0.83/0.95  --dbg_out_stat                          false
% 0.83/0.95  
% 0.83/0.95  
% 0.83/0.95  
% 0.83/0.95  
% 0.83/0.95  ------ Proving...
% 0.83/0.95  
% 0.83/0.95  
% 0.83/0.95  % SZS status Theorem for theBenchmark.p
% 0.83/0.95  
% 0.83/0.95   Resolution empty clause
% 0.83/0.95  
% 0.83/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 0.83/0.95  
% 0.83/0.95  fof(f7,conjecture,(
% 0.83/0.95    ! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.83/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/0.95  
% 0.83/0.95  fof(f8,negated_conjecture,(
% 0.83/0.95    ~! [X0,X1] : ~(k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.83/0.95    inference(negated_conjecture,[],[f7])).
% 0.83/0.95  
% 0.83/0.95  fof(f10,plain,(
% 0.83/0.95    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1)))),
% 0.83/0.95    inference(ennf_transformation,[],[f8])).
% 0.83/0.95  
% 0.83/0.95  fof(f11,plain,(
% 0.83/0.95    ? [X0,X1] : (k1_tarski(X1) != X0 & k1_xboole_0 != X0 & k1_xboole_0 = k4_xboole_0(X0,k1_tarski(X1))) => (k1_tarski(sK1) != sK0 & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 0.83/0.95    introduced(choice_axiom,[])).
% 0.83/0.95  
% 0.83/0.95  fof(f12,plain,(
% 0.83/0.95    k1_tarski(sK1) != sK0 & k1_xboole_0 != sK0 & k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.83/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 0.83/0.95  
% 0.83/0.95  fof(f19,plain,(
% 0.83/0.95    k1_xboole_0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.83/0.95    inference(cnf_transformation,[],[f12])).
% 0.83/0.95  
% 0.83/0.95  fof(f4,axiom,(
% 0.83/0.95    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.83/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/0.95  
% 0.83/0.95  fof(f16,plain,(
% 0.83/0.95    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.83/0.95    inference(cnf_transformation,[],[f4])).
% 0.83/0.95  
% 0.83/0.95  fof(f25,plain,(
% 0.83/0.95    k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK1))),
% 0.83/0.95    inference(definition_unfolding,[],[f19,f16])).
% 0.83/0.95  
% 0.83/0.95  fof(f3,axiom,(
% 0.83/0.95    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.83/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/0.95  
% 0.83/0.95  fof(f15,plain,(
% 0.83/0.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.83/0.95    inference(cnf_transformation,[],[f3])).
% 0.83/0.95  
% 0.83/0.95  fof(f2,axiom,(
% 0.83/0.95    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.83/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/0.95  
% 0.83/0.95  fof(f14,plain,(
% 0.83/0.95    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.83/0.95    inference(cnf_transformation,[],[f2])).
% 0.83/0.95  
% 0.83/0.95  fof(f5,axiom,(
% 0.83/0.95    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 0.83/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/0.95  
% 0.83/0.95  fof(f9,plain,(
% 0.83/0.95    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0))),
% 0.83/0.95    inference(ennf_transformation,[],[f5])).
% 0.83/0.95  
% 0.83/0.95  fof(f17,plain,(
% 0.83/0.95    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0)) )),
% 0.83/0.95    inference(cnf_transformation,[],[f9])).
% 0.83/0.95  
% 0.83/0.95  fof(f22,plain,(
% 0.83/0.95    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k2_xboole_0(X1,X2) != k2_tarski(X0,X0)) )),
% 0.83/0.95    inference(definition_unfolding,[],[f17,f16])).
% 0.83/0.95  
% 0.83/0.95  fof(f20,plain,(
% 0.83/0.95    k1_xboole_0 != sK0),
% 0.83/0.95    inference(cnf_transformation,[],[f12])).
% 0.83/0.95  
% 0.83/0.95  fof(f21,plain,(
% 0.83/0.95    k1_tarski(sK1) != sK0),
% 0.83/0.95    inference(cnf_transformation,[],[f12])).
% 0.83/0.95  
% 0.83/0.95  fof(f24,plain,(
% 0.83/0.95    k2_tarski(sK1,sK1) != sK0),
% 0.83/0.95    inference(definition_unfolding,[],[f21,f16])).
% 0.83/0.95  
% 0.83/0.95  fof(f6,axiom,(
% 0.83/0.95    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.83/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/0.95  
% 0.83/0.95  fof(f18,plain,(
% 0.83/0.95    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.83/0.95    inference(cnf_transformation,[],[f6])).
% 0.83/0.95  
% 0.83/0.95  fof(f23,plain,(
% 0.83/0.95    ( ! [X0,X1] : (k2_xboole_0(k2_tarski(X0,X0),X1) != k1_xboole_0) )),
% 0.83/0.95    inference(definition_unfolding,[],[f18,f16])).
% 0.83/0.95  
% 0.83/0.95  cnf(c_7,negated_conjecture,
% 0.83/0.95      ( k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK1)) ),
% 0.83/0.95      inference(cnf_transformation,[],[f25]) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_2,plain,
% 0.83/0.95      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 0.83/0.95      inference(cnf_transformation,[],[f15]) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_229,plain,
% 0.83/0.95      ( k2_xboole_0(k2_tarski(sK1,sK1),sK0) = k2_xboole_0(k2_tarski(sK1,sK1),k1_xboole_0) ),
% 0.83/0.95      inference(superposition,[status(thm)],[c_7,c_2]) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_1,plain,
% 0.83/0.95      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 0.83/0.95      inference(cnf_transformation,[],[f14]) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_236,plain,
% 0.83/0.95      ( k2_xboole_0(k2_tarski(sK1,sK1),sK0) = k2_tarski(sK1,sK1) ),
% 0.83/0.95      inference(demodulation,[status(thm)],[c_229,c_1]) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_3,plain,
% 0.83/0.95      ( X0 = X1
% 0.83/0.95      | k2_tarski(X2,X2) != k2_xboole_0(X1,X0)
% 0.83/0.95      | k1_xboole_0 = X0
% 0.83/0.95      | k1_xboole_0 = X1 ),
% 0.83/0.95      inference(cnf_transformation,[],[f22]) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_315,plain,
% 0.83/0.95      ( k2_tarski(X0,X0) != k2_tarski(sK1,sK1)
% 0.83/0.95      | k2_tarski(sK1,sK1) = sK0
% 0.83/0.95      | k2_tarski(sK1,sK1) = k1_xboole_0
% 0.83/0.95      | sK0 = k1_xboole_0 ),
% 0.83/0.95      inference(superposition,[status(thm)],[c_236,c_3]) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_6,negated_conjecture,
% 0.83/0.95      ( k1_xboole_0 != sK0 ),
% 0.83/0.95      inference(cnf_transformation,[],[f20]) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_5,negated_conjecture,
% 0.83/0.95      ( k2_tarski(sK1,sK1) != sK0 ),
% 0.83/0.95      inference(cnf_transformation,[],[f24]) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_18,plain,( X0 = X0 ),theory(equality) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_25,plain,
% 0.83/0.95      ( k1_xboole_0 = k1_xboole_0 ),
% 0.83/0.95      inference(instantiation,[status(thm)],[c_18]) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_19,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_51,plain,
% 0.83/0.95      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 0.83/0.95      inference(instantiation,[status(thm)],[c_19]) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_52,plain,
% 0.83/0.95      ( sK0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 != k1_xboole_0 ),
% 0.83/0.95      inference(instantiation,[status(thm)],[c_51]) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_452,plain,
% 0.83/0.95      ( k2_tarski(sK1,sK1) = k1_xboole_0
% 0.83/0.95      | k2_tarski(X0,X0) != k2_tarski(sK1,sK1) ),
% 0.83/0.95      inference(global_propositional_subsumption,
% 0.83/0.95                [status(thm)],
% 0.83/0.95                [c_315,c_6,c_5,c_25,c_52]) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_453,plain,
% 0.83/0.95      ( k2_tarski(X0,X0) != k2_tarski(sK1,sK1)
% 0.83/0.95      | k2_tarski(sK1,sK1) = k1_xboole_0 ),
% 0.83/0.95      inference(renaming,[status(thm)],[c_452]) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_4,plain,
% 0.83/0.95      ( k2_xboole_0(k2_tarski(X0,X0),X1) != k1_xboole_0 ),
% 0.83/0.95      inference(cnf_transformation,[],[f23]) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_182,plain,
% 0.83/0.95      ( k2_tarski(X0,X0) != k1_xboole_0 ),
% 0.83/0.95      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_457,plain,
% 0.83/0.95      ( k2_tarski(X0,X0) != k2_tarski(sK1,sK1) ),
% 0.83/0.95      inference(forward_subsumption_resolution,[status(thm)],[c_453,c_182]) ).
% 0.83/0.95  
% 0.83/0.95  cnf(c_459,plain,
% 0.83/0.95      ( $false ),
% 0.83/0.95      inference(equality_resolution,[status(thm)],[c_457]) ).
% 0.83/0.95  
% 0.83/0.95  
% 0.83/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 0.83/0.95  
% 0.83/0.95  ------                               Statistics
% 0.83/0.95  
% 0.83/0.95  ------ General
% 0.83/0.95  
% 0.83/0.95  abstr_ref_over_cycles:                  0
% 0.83/0.95  abstr_ref_under_cycles:                 0
% 0.83/0.95  gc_basic_clause_elim:                   0
% 0.83/0.95  forced_gc_time:                         0
% 0.83/0.95  parsing_time:                           0.008
% 0.83/0.95  unif_index_cands_time:                  0.
% 0.83/0.95  unif_index_add_time:                    0.
% 0.83/0.95  orderings_time:                         0.
% 0.83/0.95  out_proof_time:                         0.006
% 0.83/0.95  total_time:                             0.051
% 0.83/0.95  num_of_symbols:                         37
% 0.83/0.95  num_of_terms:                           866
% 0.83/0.95  
% 0.83/0.95  ------ Preprocessing
% 0.83/0.95  
% 0.83/0.95  num_of_splits:                          0
% 0.83/0.95  num_of_split_atoms:                     0
% 0.83/0.95  num_of_reused_defs:                     0
% 0.83/0.95  num_eq_ax_congr_red:                    0
% 0.83/0.95  num_of_sem_filtered_clauses:            0
% 0.83/0.95  num_of_subtypes:                        0
% 0.83/0.95  monotx_restored_types:                  0
% 0.83/0.95  sat_num_of_epr_types:                   0
% 0.83/0.95  sat_num_of_non_cyclic_types:            0
% 0.83/0.95  sat_guarded_non_collapsed_types:        0
% 0.83/0.95  num_pure_diseq_elim:                    0
% 0.83/0.95  simp_replaced_by:                       0
% 0.83/0.95  res_preprocessed:                       21
% 0.83/0.95  prep_upred:                             0
% 0.83/0.95  prep_unflattend:                        0
% 0.83/0.95  smt_new_axioms:                         0
% 0.83/0.95  pred_elim_cands:                        0
% 0.83/0.95  pred_elim:                              0
% 0.83/0.95  pred_elim_cl:                           0
% 0.83/0.95  pred_elim_cycles:                       0
% 0.83/0.95  merged_defs:                            0
% 0.83/0.95  merged_defs_ncl:                        0
% 0.83/0.95  bin_hyper_res:                          0
% 0.83/0.95  prep_cycles:                            2
% 0.83/0.95  pred_elim_time:                         0.
% 0.83/0.95  splitting_time:                         0.
% 0.83/0.95  sem_filter_time:                        0.
% 0.83/0.95  monotx_time:                            0.001
% 0.83/0.95  subtype_inf_time:                       0.
% 0.83/0.95  
% 0.83/0.95  ------ Problem properties
% 0.83/0.95  
% 0.83/0.95  clauses:                                8
% 0.83/0.95  conjectures:                            3
% 0.83/0.95  epr:                                    1
% 0.83/0.95  horn:                                   7
% 0.83/0.95  ground:                                 3
% 0.83/0.95  unary:                                  7
% 0.83/0.95  binary:                                 0
% 0.83/0.95  lits:                                   11
% 0.83/0.95  lits_eq:                                11
% 0.83/0.95  fd_pure:                                0
% 0.83/0.95  fd_pseudo:                              0
% 0.83/0.95  fd_cond:                                0
% 0.83/0.95  fd_pseudo_cond:                         1
% 0.83/0.95  ac_symbols:                             0
% 0.83/0.95  
% 0.83/0.95  ------ Propositional Solver
% 0.83/0.95  
% 0.83/0.95  prop_solver_calls:                      18
% 0.83/0.95  prop_fast_solver_calls:                 93
% 0.83/0.95  smt_solver_calls:                       0
% 0.83/0.95  smt_fast_solver_calls:                  0
% 0.83/0.95  prop_num_of_clauses:                    206
% 0.83/0.95  prop_preprocess_simplified:             680
% 0.83/0.95  prop_fo_subsumed:                       2
% 0.83/0.95  prop_solver_time:                       0.
% 0.83/0.95  smt_solver_time:                        0.
% 0.83/0.95  smt_fast_solver_time:                   0.
% 0.83/0.95  prop_fast_solver_time:                  0.
% 0.83/0.95  prop_unsat_core_time:                   0.
% 0.83/0.95  
% 0.83/0.95  ------ QBF
% 0.83/0.95  
% 0.83/0.95  qbf_q_res:                              0
% 0.83/0.95  qbf_num_tautologies:                    0
% 0.83/0.95  qbf_prep_cycles:                        0
% 0.83/0.95  
% 0.83/0.95  ------ BMC1
% 0.83/0.95  
% 0.83/0.95  bmc1_current_bound:                     -1
% 0.83/0.95  bmc1_last_solved_bound:                 -1
% 0.83/0.95  bmc1_unsat_core_size:                   -1
% 0.83/0.95  bmc1_unsat_core_parents_size:           -1
% 0.83/0.95  bmc1_merge_next_fun:                    0
% 0.83/0.95  bmc1_unsat_core_clauses_time:           0.
% 0.83/0.95  
% 0.83/0.95  ------ Instantiation
% 0.83/0.95  
% 0.83/0.95  inst_num_of_clauses:                    125
% 0.83/0.95  inst_num_in_passive:                    61
% 0.83/0.95  inst_num_in_active:                     64
% 0.83/0.95  inst_num_in_unprocessed:                0
% 0.83/0.95  inst_num_of_loops:                      70
% 0.83/0.95  inst_num_of_learning_restarts:          0
% 0.83/0.95  inst_num_moves_active_passive:          3
% 0.83/0.95  inst_lit_activity:                      0
% 0.83/0.95  inst_lit_activity_moves:                0
% 0.83/0.95  inst_num_tautologies:                   0
% 0.83/0.95  inst_num_prop_implied:                  0
% 0.83/0.95  inst_num_existing_simplified:           0
% 0.83/0.95  inst_num_eq_res_simplified:             0
% 0.83/0.95  inst_num_child_elim:                    0
% 0.83/0.95  inst_num_of_dismatching_blockings:      38
% 0.83/0.95  inst_num_of_non_proper_insts:           118
% 0.83/0.95  inst_num_of_duplicates:                 0
% 0.83/0.95  inst_inst_num_from_inst_to_res:         0
% 0.83/0.95  inst_dismatching_checking_time:         0.
% 0.83/0.95  
% 0.83/0.95  ------ Resolution
% 0.83/0.95  
% 0.83/0.95  res_num_of_clauses:                     0
% 0.83/0.95  res_num_in_passive:                     0
% 0.83/0.95  res_num_in_active:                      0
% 0.83/0.95  res_num_of_loops:                       23
% 0.83/0.95  res_forward_subset_subsumed:            16
% 0.83/0.95  res_backward_subset_subsumed:           0
% 0.83/0.95  res_forward_subsumed:                   0
% 0.83/0.95  res_backward_subsumed:                  0
% 0.83/0.95  res_forward_subsumption_resolution:     0
% 0.83/0.95  res_backward_subsumption_resolution:    0
% 0.83/0.95  res_clause_to_clause_subsumption:       33
% 0.83/0.95  res_orphan_elimination:                 0
% 0.83/0.95  res_tautology_del:                      17
% 0.83/0.95  res_num_eq_res_simplified:              0
% 0.83/0.95  res_num_sel_changes:                    0
% 0.83/0.95  res_moves_from_active_to_pass:          0
% 0.83/0.95  
% 0.83/0.95  ------ Superposition
% 0.83/0.95  
% 0.83/0.95  sup_time_total:                         0.
% 0.83/0.95  sup_time_generating:                    0.
% 0.83/0.95  sup_time_sim_full:                      0.
% 0.83/0.95  sup_time_sim_immed:                     0.
% 0.83/0.95  
% 0.83/0.95  sup_num_of_clauses:                     16
% 0.83/0.95  sup_num_in_active:                      14
% 0.83/0.95  sup_num_in_passive:                     2
% 0.83/0.95  sup_num_of_loops:                       13
% 0.83/0.95  sup_fw_superposition:                   19
% 0.83/0.95  sup_bw_superposition:                   12
% 0.83/0.95  sup_immediate_simplified:               3
% 0.83/0.95  sup_given_eliminated:                   0
% 0.83/0.95  comparisons_done:                       0
% 0.83/0.95  comparisons_avoided:                    0
% 0.83/0.95  
% 0.83/0.95  ------ Simplifications
% 0.83/0.95  
% 0.83/0.95  
% 0.83/0.95  sim_fw_subset_subsumed:                 0
% 0.83/0.95  sim_bw_subset_subsumed:                 0
% 0.83/0.95  sim_fw_subsumed:                        1
% 0.83/0.95  sim_bw_subsumed:                        0
% 0.83/0.95  sim_fw_subsumption_res:                 1
% 0.83/0.95  sim_bw_subsumption_res:                 0
% 0.83/0.95  sim_tautology_del:                      0
% 0.83/0.95  sim_eq_tautology_del:                   2
% 0.83/0.95  sim_eq_res_simp:                        0
% 0.83/0.95  sim_fw_demodulated:                     1
% 0.83/0.95  sim_bw_demodulated:                     0
% 0.83/0.95  sim_light_normalised:                   1
% 0.83/0.95  sim_joinable_taut:                      0
% 0.83/0.95  sim_joinable_simp:                      0
% 0.83/0.95  sim_ac_normalised:                      0
% 0.83/0.95  sim_smt_subsumption:                    0
% 0.83/0.95  
%------------------------------------------------------------------------------
