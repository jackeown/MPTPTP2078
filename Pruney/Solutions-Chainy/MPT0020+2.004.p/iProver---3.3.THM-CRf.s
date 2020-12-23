%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:17 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   39 (  70 expanded)
%              Number of clauses        :   21 (  27 expanded)
%              Number of leaves         :    6 (  16 expanded)
%              Depth                    :   13
%              Number of atoms          :   63 ( 128 expanded)
%              Number of equality atoms :   28 (  47 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f17,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f18,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f13])).

cnf(c_6,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_70,plain,
    ( k2_xboole_0(X0,X1) = X1
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_6])).

cnf(c_71,plain,
    ( k2_xboole_0(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_70])).

cnf(c_2,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_354,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_71,c_2])).

cnf(c_503,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(X0,sK1)) = k2_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_354])).

cnf(c_5,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_65,plain,
    ( k2_xboole_0(X0,X1) = X1
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_5])).

cnf(c_66,plain,
    ( k2_xboole_0(sK2,sK3) = sK3 ),
    inference(unflattening,[status(thm)],[c_65])).

cnf(c_353,plain,
    ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,X0) ),
    inference(superposition,[status(thm)],[c_66,c_2])).

cnf(c_3,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_4,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_75,plain,
    ( k2_xboole_0(X0,X1) != k2_xboole_0(sK1,sK3)
    | k2_xboole_0(sK0,sK2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_4])).

cnf(c_76,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK2),X0) != k2_xboole_0(sK1,sK3) ),
    inference(unflattening,[status(thm)],[c_75])).

cnf(c_103,plain,
    ( k2_xboole_0(X0,k2_xboole_0(sK0,sK2)) != k2_xboole_0(sK1,sK3) ),
    inference(theory_normalisation,[status(thm)],[c_76,c_2,c_0])).

cnf(c_213,plain,
    ( k2_xboole_0(k2_xboole_0(sK0,sK2),X0) != k2_xboole_0(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_0,c_103])).

cnf(c_349,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK2,X0)) != k2_xboole_0(sK1,sK3) ),
    inference(demodulation,[status(thm)],[c_2,c_213])).

cnf(c_1248,plain,
    ( k2_xboole_0(sK0,k2_xboole_0(sK3,X0)) != k2_xboole_0(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_353,c_349])).

cnf(c_13362,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_503,c_1248])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.07  % Command    : iproveropt_run.sh %d %s
% 0.07/0.26  % Computer   : n023.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % WCLimit    : 600
% 0.07/0.26  % DateTime   : Tue Dec  1 16:48:05 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.26  % Running in FOF mode
% 3.07/0.92  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/0.92  
% 3.07/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.07/0.92  
% 3.07/0.92  ------  iProver source info
% 3.07/0.92  
% 3.07/0.92  git: date: 2020-06-30 10:37:57 +0100
% 3.07/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.07/0.92  git: non_committed_changes: false
% 3.07/0.92  git: last_make_outside_of_git: false
% 3.07/0.92  
% 3.07/0.92  ------ 
% 3.07/0.92  
% 3.07/0.92  ------ Input Options
% 3.07/0.92  
% 3.07/0.92  --out_options                           all
% 3.07/0.92  --tptp_safe_out                         true
% 3.07/0.92  --problem_path                          ""
% 3.07/0.92  --include_path                          ""
% 3.07/0.92  --clausifier                            res/vclausify_rel
% 3.07/0.92  --clausifier_options                    --mode clausify
% 3.07/0.92  --stdin                                 false
% 3.07/0.92  --stats_out                             all
% 3.07/0.92  
% 3.07/0.92  ------ General Options
% 3.07/0.92  
% 3.07/0.92  --fof                                   false
% 3.07/0.92  --time_out_real                         305.
% 3.07/0.92  --time_out_virtual                      -1.
% 3.07/0.92  --symbol_type_check                     false
% 3.07/0.92  --clausify_out                          false
% 3.07/0.92  --sig_cnt_out                           false
% 3.07/0.92  --trig_cnt_out                          false
% 3.07/0.92  --trig_cnt_out_tolerance                1.
% 3.07/0.92  --trig_cnt_out_sk_spl                   false
% 3.07/0.92  --abstr_cl_out                          false
% 3.07/0.92  
% 3.07/0.92  ------ Global Options
% 3.07/0.92  
% 3.07/0.92  --schedule                              default
% 3.07/0.92  --add_important_lit                     false
% 3.07/0.92  --prop_solver_per_cl                    1000
% 3.07/0.92  --min_unsat_core                        false
% 3.07/0.92  --soft_assumptions                      false
% 3.07/0.92  --soft_lemma_size                       3
% 3.07/0.92  --prop_impl_unit_size                   0
% 3.07/0.92  --prop_impl_unit                        []
% 3.07/0.92  --share_sel_clauses                     true
% 3.07/0.92  --reset_solvers                         false
% 3.07/0.92  --bc_imp_inh                            [conj_cone]
% 3.07/0.92  --conj_cone_tolerance                   3.
% 3.07/0.92  --extra_neg_conj                        none
% 3.07/0.92  --large_theory_mode                     true
% 3.07/0.92  --prolific_symb_bound                   200
% 3.07/0.92  --lt_threshold                          2000
% 3.07/0.92  --clause_weak_htbl                      true
% 3.07/0.92  --gc_record_bc_elim                     false
% 3.07/0.92  
% 3.07/0.92  ------ Preprocessing Options
% 3.07/0.92  
% 3.07/0.92  --preprocessing_flag                    true
% 3.07/0.92  --time_out_prep_mult                    0.1
% 3.07/0.92  --splitting_mode                        input
% 3.07/0.92  --splitting_grd                         true
% 3.07/0.92  --splitting_cvd                         false
% 3.07/0.92  --splitting_cvd_svl                     false
% 3.07/0.92  --splitting_nvd                         32
% 3.07/0.92  --sub_typing                            true
% 3.07/0.92  --prep_gs_sim                           true
% 3.07/0.92  --prep_unflatten                        true
% 3.07/0.92  --prep_res_sim                          true
% 3.07/0.92  --prep_upred                            true
% 3.07/0.92  --prep_sem_filter                       exhaustive
% 3.07/0.92  --prep_sem_filter_out                   false
% 3.07/0.92  --pred_elim                             true
% 3.07/0.92  --res_sim_input                         true
% 3.07/0.92  --eq_ax_congr_red                       true
% 3.07/0.92  --pure_diseq_elim                       true
% 3.07/0.92  --brand_transform                       false
% 3.07/0.92  --non_eq_to_eq                          false
% 3.07/0.92  --prep_def_merge                        true
% 3.07/0.92  --prep_def_merge_prop_impl              false
% 3.07/0.92  --prep_def_merge_mbd                    true
% 3.07/0.92  --prep_def_merge_tr_red                 false
% 3.07/0.92  --prep_def_merge_tr_cl                  false
% 3.07/0.92  --smt_preprocessing                     true
% 3.07/0.92  --smt_ac_axioms                         fast
% 3.07/0.92  --preprocessed_out                      false
% 3.07/0.92  --preprocessed_stats                    false
% 3.07/0.92  
% 3.07/0.92  ------ Abstraction refinement Options
% 3.07/0.92  
% 3.07/0.92  --abstr_ref                             []
% 3.07/0.92  --abstr_ref_prep                        false
% 3.07/0.92  --abstr_ref_until_sat                   false
% 3.07/0.92  --abstr_ref_sig_restrict                funpre
% 3.07/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/0.92  --abstr_ref_under                       []
% 3.07/0.92  
% 3.07/0.92  ------ SAT Options
% 3.07/0.92  
% 3.07/0.92  --sat_mode                              false
% 3.07/0.92  --sat_fm_restart_options                ""
% 3.07/0.92  --sat_gr_def                            false
% 3.07/0.92  --sat_epr_types                         true
% 3.07/0.92  --sat_non_cyclic_types                  false
% 3.07/0.92  --sat_finite_models                     false
% 3.07/0.92  --sat_fm_lemmas                         false
% 3.07/0.92  --sat_fm_prep                           false
% 3.07/0.92  --sat_fm_uc_incr                        true
% 3.07/0.92  --sat_out_model                         small
% 3.07/0.92  --sat_out_clauses                       false
% 3.07/0.92  
% 3.07/0.92  ------ QBF Options
% 3.07/0.92  
% 3.07/0.92  --qbf_mode                              false
% 3.07/0.92  --qbf_elim_univ                         false
% 3.07/0.92  --qbf_dom_inst                          none
% 3.07/0.92  --qbf_dom_pre_inst                      false
% 3.07/0.92  --qbf_sk_in                             false
% 3.07/0.92  --qbf_pred_elim                         true
% 3.07/0.92  --qbf_split                             512
% 3.07/0.92  
% 3.07/0.92  ------ BMC1 Options
% 3.07/0.92  
% 3.07/0.92  --bmc1_incremental                      false
% 3.07/0.92  --bmc1_axioms                           reachable_all
% 3.07/0.92  --bmc1_min_bound                        0
% 3.07/0.92  --bmc1_max_bound                        -1
% 3.07/0.92  --bmc1_max_bound_default                -1
% 3.07/0.92  --bmc1_symbol_reachability              true
% 3.07/0.92  --bmc1_property_lemmas                  false
% 3.07/0.92  --bmc1_k_induction                      false
% 3.07/0.92  --bmc1_non_equiv_states                 false
% 3.07/0.92  --bmc1_deadlock                         false
% 3.07/0.92  --bmc1_ucm                              false
% 3.07/0.92  --bmc1_add_unsat_core                   none
% 3.07/0.92  --bmc1_unsat_core_children              false
% 3.07/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/0.92  --bmc1_out_stat                         full
% 3.07/0.92  --bmc1_ground_init                      false
% 3.07/0.92  --bmc1_pre_inst_next_state              false
% 3.07/0.92  --bmc1_pre_inst_state                   false
% 3.07/0.92  --bmc1_pre_inst_reach_state             false
% 3.07/0.92  --bmc1_out_unsat_core                   false
% 3.07/0.92  --bmc1_aig_witness_out                  false
% 3.07/0.92  --bmc1_verbose                          false
% 3.07/0.92  --bmc1_dump_clauses_tptp                false
% 3.07/0.92  --bmc1_dump_unsat_core_tptp             false
% 3.07/0.92  --bmc1_dump_file                        -
% 3.07/0.92  --bmc1_ucm_expand_uc_limit              128
% 3.07/0.92  --bmc1_ucm_n_expand_iterations          6
% 3.07/0.92  --bmc1_ucm_extend_mode                  1
% 3.07/0.92  --bmc1_ucm_init_mode                    2
% 3.07/0.92  --bmc1_ucm_cone_mode                    none
% 3.07/0.92  --bmc1_ucm_reduced_relation_type        0
% 3.07/0.92  --bmc1_ucm_relax_model                  4
% 3.07/0.92  --bmc1_ucm_full_tr_after_sat            true
% 3.07/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/0.92  --bmc1_ucm_layered_model                none
% 3.07/0.92  --bmc1_ucm_max_lemma_size               10
% 3.07/0.92  
% 3.07/0.92  ------ AIG Options
% 3.07/0.92  
% 3.07/0.92  --aig_mode                              false
% 3.07/0.92  
% 3.07/0.92  ------ Instantiation Options
% 3.07/0.92  
% 3.07/0.92  --instantiation_flag                    true
% 3.07/0.92  --inst_sos_flag                         false
% 3.07/0.92  --inst_sos_phase                        true
% 3.07/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/0.92  --inst_lit_sel_side                     num_symb
% 3.07/0.92  --inst_solver_per_active                1400
% 3.07/0.92  --inst_solver_calls_frac                1.
% 3.07/0.92  --inst_passive_queue_type               priority_queues
% 3.07/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.07/0.92  --inst_passive_queues_freq              [25;2]
% 3.07/0.92  --inst_dismatching                      true
% 3.07/0.92  --inst_eager_unprocessed_to_passive     true
% 3.07/0.92  --inst_prop_sim_given                   true
% 3.07/0.92  --inst_prop_sim_new                     false
% 3.07/0.92  --inst_subs_new                         false
% 3.07/0.92  --inst_eq_res_simp                      false
% 3.07/0.92  --inst_subs_given                       false
% 3.07/0.92  --inst_orphan_elimination               true
% 3.07/0.92  --inst_learning_loop_flag               true
% 3.07/0.92  --inst_learning_start                   3000
% 3.07/0.92  --inst_learning_factor                  2
% 3.07/0.92  --inst_start_prop_sim_after_learn       3
% 3.07/0.92  --inst_sel_renew                        solver
% 3.07/0.92  --inst_lit_activity_flag                true
% 3.07/0.92  --inst_restr_to_given                   false
% 3.07/0.92  --inst_activity_threshold               500
% 3.07/0.92  --inst_out_proof                        true
% 3.07/0.92  
% 3.07/0.92  ------ Resolution Options
% 3.07/0.92  
% 3.07/0.92  --resolution_flag                       true
% 3.07/0.92  --res_lit_sel                           adaptive
% 3.07/0.92  --res_lit_sel_side                      none
% 3.07/0.92  --res_ordering                          kbo
% 3.07/0.92  --res_to_prop_solver                    active
% 3.07/0.92  --res_prop_simpl_new                    false
% 3.07/0.92  --res_prop_simpl_given                  true
% 3.07/0.92  --res_passive_queue_type                priority_queues
% 3.07/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.07/0.92  --res_passive_queues_freq               [15;5]
% 3.07/0.92  --res_forward_subs                      full
% 3.07/0.92  --res_backward_subs                     full
% 3.07/0.92  --res_forward_subs_resolution           true
% 3.07/0.92  --res_backward_subs_resolution          true
% 3.07/0.92  --res_orphan_elimination                true
% 3.07/0.92  --res_time_limit                        2.
% 3.07/0.92  --res_out_proof                         true
% 3.07/0.92  
% 3.07/0.92  ------ Superposition Options
% 3.07/0.92  
% 3.07/0.92  --superposition_flag                    true
% 3.07/0.92  --sup_passive_queue_type                priority_queues
% 3.07/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/0.92  --sup_passive_queues_freq               [8;1;4]
% 3.07/0.92  --demod_completeness_check              fast
% 3.07/0.92  --demod_use_ground                      true
% 3.07/0.92  --sup_to_prop_solver                    passive
% 3.07/0.92  --sup_prop_simpl_new                    true
% 3.07/0.92  --sup_prop_simpl_given                  true
% 3.07/0.92  --sup_fun_splitting                     false
% 3.07/0.92  --sup_smt_interval                      50000
% 3.07/0.92  
% 3.07/0.92  ------ Superposition Simplification Setup
% 3.07/0.92  
% 3.07/0.92  --sup_indices_passive                   []
% 3.07/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.92  --sup_full_bw                           [BwDemod]
% 3.07/0.92  --sup_immed_triv                        [TrivRules]
% 3.07/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.92  --sup_immed_bw_main                     []
% 3.07/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.92  
% 3.07/0.92  ------ Combination Options
% 3.07/0.92  
% 3.07/0.92  --comb_res_mult                         3
% 3.07/0.92  --comb_sup_mult                         2
% 3.07/0.92  --comb_inst_mult                        10
% 3.07/0.92  
% 3.07/0.92  ------ Debug Options
% 3.07/0.92  
% 3.07/0.92  --dbg_backtrace                         false
% 3.07/0.92  --dbg_dump_prop_clauses                 false
% 3.07/0.92  --dbg_dump_prop_clauses_file            -
% 3.07/0.92  --dbg_out_stat                          false
% 3.07/0.92  ------ Parsing...
% 3.07/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.07/0.92  
% 3.07/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 3.07/0.92  
% 3.07/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.07/0.92  
% 3.07/0.92  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.07/0.92  ------ Proving...
% 3.07/0.92  ------ Problem Properties 
% 3.07/0.92  
% 3.07/0.92  
% 3.07/0.92  clauses                                 8
% 3.07/0.92  conjectures                             0
% 3.07/0.92  EPR                                     0
% 3.07/0.92  Horn                                    8
% 3.07/0.92  unary                                   6
% 3.07/0.92  binary                                  2
% 3.07/0.92  lits                                    10
% 3.07/0.92  lits eq                                 10
% 3.07/0.92  fd_pure                                 0
% 3.07/0.92  fd_pseudo                               0
% 3.07/0.92  fd_cond                                 0
% 3.07/0.92  fd_pseudo_cond                          0
% 3.07/0.92  AC symbols                              1
% 3.07/0.92  
% 3.07/0.92  ------ Schedule dynamic 5 is on 
% 3.07/0.92  
% 3.07/0.92  ------ no conjectures: strip conj schedule 
% 3.07/0.92  
% 3.07/0.92  ------ pure equality problem: resolution off 
% 3.07/0.92  
% 3.07/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 3.07/0.92  
% 3.07/0.92  
% 3.07/0.92  ------ 
% 3.07/0.92  Current options:
% 3.07/0.92  ------ 
% 3.07/0.92  
% 3.07/0.92  ------ Input Options
% 3.07/0.92  
% 3.07/0.92  --out_options                           all
% 3.07/0.92  --tptp_safe_out                         true
% 3.07/0.92  --problem_path                          ""
% 3.07/0.92  --include_path                          ""
% 3.07/0.92  --clausifier                            res/vclausify_rel
% 3.07/0.92  --clausifier_options                    --mode clausify
% 3.07/0.92  --stdin                                 false
% 3.07/0.92  --stats_out                             all
% 3.07/0.92  
% 3.07/0.92  ------ General Options
% 3.07/0.92  
% 3.07/0.92  --fof                                   false
% 3.07/0.92  --time_out_real                         305.
% 3.07/0.92  --time_out_virtual                      -1.
% 3.07/0.92  --symbol_type_check                     false
% 3.07/0.92  --clausify_out                          false
% 3.07/0.92  --sig_cnt_out                           false
% 3.07/0.92  --trig_cnt_out                          false
% 3.07/0.92  --trig_cnt_out_tolerance                1.
% 3.07/0.92  --trig_cnt_out_sk_spl                   false
% 3.07/0.92  --abstr_cl_out                          false
% 3.07/0.92  
% 3.07/0.92  ------ Global Options
% 3.07/0.92  
% 3.07/0.92  --schedule                              default
% 3.07/0.92  --add_important_lit                     false
% 3.07/0.92  --prop_solver_per_cl                    1000
% 3.07/0.92  --min_unsat_core                        false
% 3.07/0.92  --soft_assumptions                      false
% 3.07/0.92  --soft_lemma_size                       3
% 3.07/0.92  --prop_impl_unit_size                   0
% 3.07/0.92  --prop_impl_unit                        []
% 3.07/0.92  --share_sel_clauses                     true
% 3.07/0.92  --reset_solvers                         false
% 3.07/0.92  --bc_imp_inh                            [conj_cone]
% 3.07/0.92  --conj_cone_tolerance                   3.
% 3.07/0.92  --extra_neg_conj                        none
% 3.07/0.92  --large_theory_mode                     true
% 3.07/0.92  --prolific_symb_bound                   200
% 3.07/0.92  --lt_threshold                          2000
% 3.07/0.92  --clause_weak_htbl                      true
% 3.07/0.92  --gc_record_bc_elim                     false
% 3.07/0.92  
% 3.07/0.92  ------ Preprocessing Options
% 3.07/0.92  
% 3.07/0.92  --preprocessing_flag                    true
% 3.07/0.92  --time_out_prep_mult                    0.1
% 3.07/0.92  --splitting_mode                        input
% 3.07/0.92  --splitting_grd                         true
% 3.07/0.92  --splitting_cvd                         false
% 3.07/0.92  --splitting_cvd_svl                     false
% 3.07/0.92  --splitting_nvd                         32
% 3.07/0.92  --sub_typing                            true
% 3.07/0.92  --prep_gs_sim                           true
% 3.07/0.92  --prep_unflatten                        true
% 3.07/0.92  --prep_res_sim                          true
% 3.07/0.92  --prep_upred                            true
% 3.07/0.92  --prep_sem_filter                       exhaustive
% 3.07/0.92  --prep_sem_filter_out                   false
% 3.07/0.92  --pred_elim                             true
% 3.07/0.92  --res_sim_input                         true
% 3.07/0.92  --eq_ax_congr_red                       true
% 3.07/0.92  --pure_diseq_elim                       true
% 3.07/0.92  --brand_transform                       false
% 3.07/0.92  --non_eq_to_eq                          false
% 3.07/0.92  --prep_def_merge                        true
% 3.07/0.92  --prep_def_merge_prop_impl              false
% 3.07/0.92  --prep_def_merge_mbd                    true
% 3.07/0.92  --prep_def_merge_tr_red                 false
% 3.07/0.92  --prep_def_merge_tr_cl                  false
% 3.07/0.92  --smt_preprocessing                     true
% 3.07/0.92  --smt_ac_axioms                         fast
% 3.07/0.92  --preprocessed_out                      false
% 3.07/0.92  --preprocessed_stats                    false
% 3.07/0.92  
% 3.07/0.92  ------ Abstraction refinement Options
% 3.07/0.92  
% 3.07/0.92  --abstr_ref                             []
% 3.07/0.92  --abstr_ref_prep                        false
% 3.07/0.92  --abstr_ref_until_sat                   false
% 3.07/0.92  --abstr_ref_sig_restrict                funpre
% 3.07/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 3.07/0.92  --abstr_ref_under                       []
% 3.07/0.92  
% 3.07/0.92  ------ SAT Options
% 3.07/0.92  
% 3.07/0.92  --sat_mode                              false
% 3.07/0.92  --sat_fm_restart_options                ""
% 3.07/0.92  --sat_gr_def                            false
% 3.07/0.92  --sat_epr_types                         true
% 3.07/0.92  --sat_non_cyclic_types                  false
% 3.07/0.92  --sat_finite_models                     false
% 3.07/0.92  --sat_fm_lemmas                         false
% 3.07/0.92  --sat_fm_prep                           false
% 3.07/0.92  --sat_fm_uc_incr                        true
% 3.07/0.92  --sat_out_model                         small
% 3.07/0.92  --sat_out_clauses                       false
% 3.07/0.92  
% 3.07/0.92  ------ QBF Options
% 3.07/0.92  
% 3.07/0.92  --qbf_mode                              false
% 3.07/0.92  --qbf_elim_univ                         false
% 3.07/0.92  --qbf_dom_inst                          none
% 3.07/0.92  --qbf_dom_pre_inst                      false
% 3.07/0.92  --qbf_sk_in                             false
% 3.07/0.92  --qbf_pred_elim                         true
% 3.07/0.92  --qbf_split                             512
% 3.07/0.92  
% 3.07/0.92  ------ BMC1 Options
% 3.07/0.92  
% 3.07/0.92  --bmc1_incremental                      false
% 3.07/0.92  --bmc1_axioms                           reachable_all
% 3.07/0.92  --bmc1_min_bound                        0
% 3.07/0.92  --bmc1_max_bound                        -1
% 3.07/0.92  --bmc1_max_bound_default                -1
% 3.07/0.92  --bmc1_symbol_reachability              true
% 3.07/0.92  --bmc1_property_lemmas                  false
% 3.07/0.92  --bmc1_k_induction                      false
% 3.07/0.92  --bmc1_non_equiv_states                 false
% 3.07/0.92  --bmc1_deadlock                         false
% 3.07/0.92  --bmc1_ucm                              false
% 3.07/0.92  --bmc1_add_unsat_core                   none
% 3.07/0.92  --bmc1_unsat_core_children              false
% 3.07/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 3.07/0.92  --bmc1_out_stat                         full
% 3.07/0.92  --bmc1_ground_init                      false
% 3.07/0.92  --bmc1_pre_inst_next_state              false
% 3.07/0.92  --bmc1_pre_inst_state                   false
% 3.07/0.92  --bmc1_pre_inst_reach_state             false
% 3.07/0.92  --bmc1_out_unsat_core                   false
% 3.07/0.92  --bmc1_aig_witness_out                  false
% 3.07/0.92  --bmc1_verbose                          false
% 3.07/0.92  --bmc1_dump_clauses_tptp                false
% 3.07/0.92  --bmc1_dump_unsat_core_tptp             false
% 3.07/0.92  --bmc1_dump_file                        -
% 3.07/0.92  --bmc1_ucm_expand_uc_limit              128
% 3.07/0.92  --bmc1_ucm_n_expand_iterations          6
% 3.07/0.92  --bmc1_ucm_extend_mode                  1
% 3.07/0.92  --bmc1_ucm_init_mode                    2
% 3.07/0.92  --bmc1_ucm_cone_mode                    none
% 3.07/0.92  --bmc1_ucm_reduced_relation_type        0
% 3.07/0.92  --bmc1_ucm_relax_model                  4
% 3.07/0.92  --bmc1_ucm_full_tr_after_sat            true
% 3.07/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 3.07/0.92  --bmc1_ucm_layered_model                none
% 3.07/0.92  --bmc1_ucm_max_lemma_size               10
% 3.07/0.92  
% 3.07/0.92  ------ AIG Options
% 3.07/0.92  
% 3.07/0.92  --aig_mode                              false
% 3.07/0.92  
% 3.07/0.92  ------ Instantiation Options
% 3.07/0.92  
% 3.07/0.92  --instantiation_flag                    true
% 3.07/0.92  --inst_sos_flag                         false
% 3.07/0.92  --inst_sos_phase                        true
% 3.07/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.07/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.07/0.92  --inst_lit_sel_side                     none
% 3.07/0.92  --inst_solver_per_active                1400
% 3.07/0.92  --inst_solver_calls_frac                1.
% 3.07/0.92  --inst_passive_queue_type               priority_queues
% 3.07/0.92  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 3.07/0.92  --inst_passive_queues_freq              [25;2]
% 3.07/0.92  --inst_dismatching                      true
% 3.07/0.92  --inst_eager_unprocessed_to_passive     true
% 3.07/0.92  --inst_prop_sim_given                   true
% 3.07/0.92  --inst_prop_sim_new                     false
% 3.07/0.92  --inst_subs_new                         false
% 3.07/0.92  --inst_eq_res_simp                      false
% 3.07/0.92  --inst_subs_given                       false
% 3.07/0.92  --inst_orphan_elimination               true
% 3.07/0.92  --inst_learning_loop_flag               true
% 3.07/0.92  --inst_learning_start                   3000
% 3.07/0.92  --inst_learning_factor                  2
% 3.07/0.92  --inst_start_prop_sim_after_learn       3
% 3.07/0.92  --inst_sel_renew                        solver
% 3.07/0.92  --inst_lit_activity_flag                true
% 3.07/0.92  --inst_restr_to_given                   false
% 3.07/0.92  --inst_activity_threshold               500
% 3.07/0.92  --inst_out_proof                        true
% 3.07/0.92  
% 3.07/0.92  ------ Resolution Options
% 3.07/0.92  
% 3.07/0.92  --resolution_flag                       false
% 3.07/0.92  --res_lit_sel                           adaptive
% 3.07/0.92  --res_lit_sel_side                      none
% 3.07/0.92  --res_ordering                          kbo
% 3.07/0.92  --res_to_prop_solver                    active
% 3.07/0.92  --res_prop_simpl_new                    false
% 3.07/0.92  --res_prop_simpl_given                  true
% 3.07/0.92  --res_passive_queue_type                priority_queues
% 3.07/0.92  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 3.07/0.92  --res_passive_queues_freq               [15;5]
% 3.07/0.92  --res_forward_subs                      full
% 3.07/0.92  --res_backward_subs                     full
% 3.07/0.92  --res_forward_subs_resolution           true
% 3.07/0.92  --res_backward_subs_resolution          true
% 3.07/0.92  --res_orphan_elimination                true
% 3.07/0.92  --res_time_limit                        2.
% 3.07/0.92  --res_out_proof                         true
% 3.07/0.92  
% 3.07/0.92  ------ Superposition Options
% 3.07/0.92  
% 3.07/0.92  --superposition_flag                    true
% 3.07/0.92  --sup_passive_queue_type                priority_queues
% 3.07/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.07/0.92  --sup_passive_queues_freq               [8;1;4]
% 3.07/0.92  --demod_completeness_check              fast
% 3.07/0.92  --demod_use_ground                      true
% 3.07/0.92  --sup_to_prop_solver                    passive
% 3.07/0.92  --sup_prop_simpl_new                    true
% 3.07/0.92  --sup_prop_simpl_given                  true
% 3.07/0.92  --sup_fun_splitting                     false
% 3.07/0.92  --sup_smt_interval                      50000
% 3.07/0.92  
% 3.07/0.92  ------ Superposition Simplification Setup
% 3.07/0.92  
% 3.07/0.92  --sup_indices_passive                   []
% 3.07/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.07/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 3.07/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.92  --sup_full_bw                           [BwDemod]
% 3.07/0.92  --sup_immed_triv                        [TrivRules]
% 3.07/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.07/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.92  --sup_immed_bw_main                     []
% 3.07/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 3.07/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.07/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.07/0.92  
% 3.07/0.92  ------ Combination Options
% 3.07/0.92  
% 3.07/0.92  --comb_res_mult                         3
% 3.07/0.92  --comb_sup_mult                         2
% 3.07/0.92  --comb_inst_mult                        10
% 3.07/0.92  
% 3.07/0.92  ------ Debug Options
% 3.07/0.92  
% 3.07/0.92  --dbg_backtrace                         false
% 3.07/0.92  --dbg_dump_prop_clauses                 false
% 3.07/0.92  --dbg_dump_prop_clauses_file            -
% 3.07/0.92  --dbg_out_stat                          false
% 3.07/0.92  
% 3.07/0.92  
% 3.07/0.92  
% 3.07/0.92  
% 3.07/0.92  ------ Proving...
% 3.07/0.92  
% 3.07/0.92  
% 3.07/0.92  % SZS status Theorem for theBenchmark.p
% 3.07/0.92  
% 3.07/0.92   Resolution empty clause
% 3.07/0.92  
% 3.07/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 3.07/0.92  
% 3.07/0.92  fof(f1,axiom,(
% 3.07/0.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.07/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.92  
% 3.07/0.92  fof(f12,plain,(
% 3.07/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.07/0.92    inference(cnf_transformation,[],[f1])).
% 3.07/0.92  
% 3.07/0.92  fof(f2,axiom,(
% 3.07/0.92    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.07/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.92  
% 3.07/0.92  fof(f7,plain,(
% 3.07/0.92    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.07/0.92    inference(ennf_transformation,[],[f2])).
% 3.07/0.92  
% 3.07/0.92  fof(f13,plain,(
% 3.07/0.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.07/0.92    inference(cnf_transformation,[],[f7])).
% 3.07/0.92  
% 3.07/0.92  fof(f5,conjecture,(
% 3.07/0.92    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 3.07/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.92  
% 3.07/0.92  fof(f6,negated_conjecture,(
% 3.07/0.92    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)))),
% 3.07/0.92    inference(negated_conjecture,[],[f5])).
% 3.07/0.92  
% 3.07/0.92  fof(f8,plain,(
% 3.07/0.92    ? [X0,X1,X2,X3] : (~r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 3.07/0.92    inference(ennf_transformation,[],[f6])).
% 3.07/0.92  
% 3.07/0.92  fof(f9,plain,(
% 3.07/0.92    ? [X0,X1,X2,X3] : (~r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 3.07/0.92    inference(flattening,[],[f8])).
% 3.07/0.92  
% 3.07/0.92  fof(f10,plain,(
% 3.07/0.92    ? [X0,X1,X2,X3] : (~r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (~r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 3.07/0.92    introduced(choice_axiom,[])).
% 3.07/0.92  
% 3.07/0.92  fof(f11,plain,(
% 3.07/0.92    ~r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 3.07/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f9,f10])).
% 3.07/0.92  
% 3.07/0.92  fof(f16,plain,(
% 3.07/0.92    r1_tarski(sK0,sK1)),
% 3.07/0.92    inference(cnf_transformation,[],[f11])).
% 3.07/0.92  
% 3.07/0.92  fof(f3,axiom,(
% 3.07/0.92    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 3.07/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.92  
% 3.07/0.92  fof(f14,plain,(
% 3.07/0.92    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 3.07/0.92    inference(cnf_transformation,[],[f3])).
% 3.07/0.92  
% 3.07/0.92  fof(f17,plain,(
% 3.07/0.92    r1_tarski(sK2,sK3)),
% 3.07/0.92    inference(cnf_transformation,[],[f11])).
% 3.07/0.92  
% 3.07/0.92  fof(f4,axiom,(
% 3.07/0.92    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.07/0.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.07/0.92  
% 3.07/0.92  fof(f15,plain,(
% 3.07/0.92    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.07/0.92    inference(cnf_transformation,[],[f4])).
% 3.07/0.92  
% 3.07/0.92  fof(f18,plain,(
% 3.07/0.92    ~r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3))),
% 3.07/0.92    inference(cnf_transformation,[],[f11])).
% 3.07/0.92  
% 3.07/0.92  cnf(c_0,plain,
% 3.07/0.92      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.07/0.92      inference(cnf_transformation,[],[f12]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_1,plain,
% 3.07/0.92      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.07/0.92      inference(cnf_transformation,[],[f13]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_6,negated_conjecture,
% 3.07/0.92      ( r1_tarski(sK0,sK1) ),
% 3.07/0.92      inference(cnf_transformation,[],[f16]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_70,plain,
% 3.07/0.92      ( k2_xboole_0(X0,X1) = X1 | sK1 != X1 | sK0 != X0 ),
% 3.07/0.92      inference(resolution_lifted,[status(thm)],[c_1,c_6]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_71,plain,
% 3.07/0.92      ( k2_xboole_0(sK0,sK1) = sK1 ),
% 3.07/0.92      inference(unflattening,[status(thm)],[c_70]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_2,plain,
% 3.07/0.92      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 3.07/0.92      inference(cnf_transformation,[],[f14]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_354,plain,
% 3.07/0.92      ( k2_xboole_0(sK0,k2_xboole_0(sK1,X0)) = k2_xboole_0(sK1,X0) ),
% 3.07/0.92      inference(superposition,[status(thm)],[c_71,c_2]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_503,plain,
% 3.07/0.92      ( k2_xboole_0(sK0,k2_xboole_0(X0,sK1)) = k2_xboole_0(sK1,X0) ),
% 3.07/0.92      inference(superposition,[status(thm)],[c_0,c_354]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_5,negated_conjecture,
% 3.07/0.92      ( r1_tarski(sK2,sK3) ),
% 3.07/0.92      inference(cnf_transformation,[],[f17]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_65,plain,
% 3.07/0.92      ( k2_xboole_0(X0,X1) = X1 | sK3 != X1 | sK2 != X0 ),
% 3.07/0.92      inference(resolution_lifted,[status(thm)],[c_1,c_5]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_66,plain,
% 3.07/0.92      ( k2_xboole_0(sK2,sK3) = sK3 ),
% 3.07/0.92      inference(unflattening,[status(thm)],[c_65]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_353,plain,
% 3.07/0.92      ( k2_xboole_0(sK2,k2_xboole_0(sK3,X0)) = k2_xboole_0(sK3,X0) ),
% 3.07/0.92      inference(superposition,[status(thm)],[c_66,c_2]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_3,plain,
% 3.07/0.92      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 3.07/0.92      inference(cnf_transformation,[],[f15]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_4,negated_conjecture,
% 3.07/0.92      ( ~ r1_tarski(k2_xboole_0(sK0,sK2),k2_xboole_0(sK1,sK3)) ),
% 3.07/0.92      inference(cnf_transformation,[],[f18]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_75,plain,
% 3.07/0.92      ( k2_xboole_0(X0,X1) != k2_xboole_0(sK1,sK3)
% 3.07/0.92      | k2_xboole_0(sK0,sK2) != X0 ),
% 3.07/0.92      inference(resolution_lifted,[status(thm)],[c_3,c_4]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_76,plain,
% 3.07/0.92      ( k2_xboole_0(k2_xboole_0(sK0,sK2),X0) != k2_xboole_0(sK1,sK3) ),
% 3.07/0.92      inference(unflattening,[status(thm)],[c_75]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_103,plain,
% 3.07/0.92      ( k2_xboole_0(X0,k2_xboole_0(sK0,sK2)) != k2_xboole_0(sK1,sK3) ),
% 3.07/0.92      inference(theory_normalisation,[status(thm)],[c_76,c_2,c_0]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_213,plain,
% 3.07/0.92      ( k2_xboole_0(k2_xboole_0(sK0,sK2),X0) != k2_xboole_0(sK1,sK3) ),
% 3.07/0.92      inference(superposition,[status(thm)],[c_0,c_103]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_349,plain,
% 3.07/0.92      ( k2_xboole_0(sK0,k2_xboole_0(sK2,X0)) != k2_xboole_0(sK1,sK3) ),
% 3.07/0.92      inference(demodulation,[status(thm)],[c_2,c_213]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_1248,plain,
% 3.07/0.92      ( k2_xboole_0(sK0,k2_xboole_0(sK3,X0)) != k2_xboole_0(sK1,sK3) ),
% 3.07/0.92      inference(superposition,[status(thm)],[c_353,c_349]) ).
% 3.07/0.92  
% 3.07/0.92  cnf(c_13362,plain,
% 3.07/0.92      ( $false ),
% 3.07/0.92      inference(superposition,[status(thm)],[c_503,c_1248]) ).
% 3.07/0.92  
% 3.07/0.92  
% 3.07/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 3.07/0.92  
% 3.07/0.92  ------                               Statistics
% 3.07/0.92  
% 3.07/0.92  ------ General
% 3.07/0.92  
% 3.07/0.92  abstr_ref_over_cycles:                  0
% 3.07/0.92  abstr_ref_under_cycles:                 0
% 3.07/0.92  gc_basic_clause_elim:                   0
% 3.07/0.92  forced_gc_time:                         0
% 3.07/0.92  parsing_time:                           0.007
% 3.07/0.92  unif_index_cands_time:                  0.
% 3.07/0.92  unif_index_add_time:                    0.
% 3.07/0.92  orderings_time:                         0.
% 3.07/0.92  out_proof_time:                         0.006
% 3.07/0.92  total_time:                             0.372
% 3.07/0.92  num_of_symbols:                         37
% 3.07/0.92  num_of_terms:                           12960
% 3.07/0.92  
% 3.07/0.92  ------ Preprocessing
% 3.07/0.92  
% 3.07/0.92  num_of_splits:                          0
% 3.07/0.92  num_of_split_atoms:                     0
% 3.07/0.92  num_of_reused_defs:                     0
% 3.07/0.92  num_eq_ax_congr_red:                    0
% 3.07/0.92  num_of_sem_filtered_clauses:            0
% 3.07/0.92  num_of_subtypes:                        1
% 3.07/0.92  monotx_restored_types:                  0
% 3.07/0.92  sat_num_of_epr_types:                   0
% 3.07/0.92  sat_num_of_non_cyclic_types:            0
% 3.07/0.92  sat_guarded_non_collapsed_types:        0
% 3.07/0.92  num_pure_diseq_elim:                    0
% 3.07/0.92  simp_replaced_by:                       0
% 3.07/0.92  res_preprocessed:                       18
% 3.07/0.92  prep_upred:                             0
% 3.07/0.92  prep_unflattend:                        7
% 3.07/0.92  smt_new_axioms:                         0
% 3.07/0.92  pred_elim_cands:                        1
% 3.07/0.92  pred_elim:                              1
% 3.07/0.92  pred_elim_cl:                           -1
% 3.07/0.92  pred_elim_cycles:                       2
% 3.07/0.92  merged_defs:                            0
% 3.07/0.92  merged_defs_ncl:                        0
% 3.07/0.92  bin_hyper_res:                          0
% 3.07/0.92  prep_cycles:                            2
% 3.07/0.92  pred_elim_time:                         0.001
% 3.07/0.92  splitting_time:                         0.
% 3.07/0.92  sem_filter_time:                        0.
% 3.07/0.92  monotx_time:                            0.
% 3.07/0.92  subtype_inf_time:                       0.
% 3.07/0.92  
% 3.07/0.92  ------ Problem properties
% 3.07/0.92  
% 3.07/0.92  clauses:                                8
% 3.07/0.92  conjectures:                            0
% 3.07/0.92  epr:                                    0
% 3.07/0.92  horn:                                   8
% 3.07/0.92  ground:                                 4
% 3.07/0.92  unary:                                  6
% 3.07/0.92  binary:                                 2
% 3.07/0.92  lits:                                   10
% 3.07/0.92  lits_eq:                                10
% 3.07/0.92  fd_pure:                                0
% 3.07/0.92  fd_pseudo:                              0
% 3.07/0.92  fd_cond:                                0
% 3.07/0.92  fd_pseudo_cond:                         0
% 3.07/0.92  ac_symbols:                             1
% 3.07/0.92  
% 3.07/0.92  ------ Propositional Solver
% 3.07/0.92  
% 3.07/0.92  prop_solver_calls:                      24
% 3.07/0.92  prop_fast_solver_calls:                 166
% 3.07/0.92  smt_solver_calls:                       0
% 3.07/0.92  smt_fast_solver_calls:                  0
% 3.07/0.92  prop_num_of_clauses:                    3400
% 3.07/0.92  prop_preprocess_simplified:             3510
% 3.07/0.92  prop_fo_subsumed:                       0
% 3.07/0.92  prop_solver_time:                       0.
% 3.07/0.92  smt_solver_time:                        0.
% 3.07/0.92  smt_fast_solver_time:                   0.
% 3.07/0.92  prop_fast_solver_time:                  0.
% 3.07/0.92  prop_unsat_core_time:                   0.
% 3.07/0.92  
% 3.07/0.92  ------ QBF
% 3.07/0.92  
% 3.07/0.92  qbf_q_res:                              0
% 3.07/0.92  qbf_num_tautologies:                    0
% 3.07/0.92  qbf_prep_cycles:                        0
% 3.07/0.92  
% 3.07/0.92  ------ BMC1
% 3.07/0.92  
% 3.07/0.92  bmc1_current_bound:                     -1
% 3.07/0.92  bmc1_last_solved_bound:                 -1
% 3.07/0.92  bmc1_unsat_core_size:                   -1
% 3.07/0.92  bmc1_unsat_core_parents_size:           -1
% 3.07/0.92  bmc1_merge_next_fun:                    0
% 3.07/0.92  bmc1_unsat_core_clauses_time:           0.
% 3.07/0.92  
% 3.07/0.92  ------ Instantiation
% 3.07/0.92  
% 3.07/0.92  inst_num_of_clauses:                    995
% 3.07/0.92  inst_num_in_passive:                    377
% 3.07/0.92  inst_num_in_active:                     506
% 3.07/0.92  inst_num_in_unprocessed:                112
% 3.07/0.92  inst_num_of_loops:                      510
% 3.07/0.92  inst_num_of_learning_restarts:          0
% 3.07/0.92  inst_num_moves_active_passive:          0
% 3.07/0.92  inst_lit_activity:                      0
% 3.07/0.92  inst_lit_activity_moves:                0
% 3.07/0.92  inst_num_tautologies:                   0
% 3.07/0.92  inst_num_prop_implied:                  0
% 3.07/0.92  inst_num_existing_simplified:           0
% 3.07/0.92  inst_num_eq_res_simplified:             0
% 3.07/0.92  inst_num_child_elim:                    0
% 3.07/0.92  inst_num_of_dismatching_blockings:      232
% 3.07/0.92  inst_num_of_non_proper_insts:           1003
% 3.07/0.92  inst_num_of_duplicates:                 0
% 3.07/0.92  inst_inst_num_from_inst_to_res:         0
% 3.07/0.92  inst_dismatching_checking_time:         0.
% 3.07/0.92  
% 3.07/0.92  ------ Resolution
% 3.07/0.92  
% 3.07/0.92  res_num_of_clauses:                     0
% 3.07/0.92  res_num_in_passive:                     0
% 3.07/0.92  res_num_in_active:                      0
% 3.07/0.92  res_num_of_loops:                       20
% 3.07/0.92  res_forward_subset_subsumed:            277
% 3.07/0.92  res_backward_subset_subsumed:           2
% 3.07/0.92  res_forward_subsumed:                   0
% 3.07/0.92  res_backward_subsumed:                  0
% 3.07/0.92  res_forward_subsumption_resolution:     0
% 3.07/0.92  res_backward_subsumption_resolution:    0
% 3.07/0.92  res_clause_to_clause_subsumption:       21971
% 3.07/0.92  res_orphan_elimination:                 0
% 3.07/0.92  res_tautology_del:                      92
% 3.07/0.92  res_num_eq_res_simplified:              0
% 3.07/0.92  res_num_sel_changes:                    0
% 3.07/0.92  res_moves_from_active_to_pass:          0
% 3.07/0.92  
% 3.07/0.92  ------ Superposition
% 3.07/0.92  
% 3.07/0.92  sup_time_total:                         0.
% 3.07/0.92  sup_time_generating:                    0.
% 3.07/0.92  sup_time_sim_full:                      0.
% 3.07/0.92  sup_time_sim_immed:                     0.
% 3.07/0.92  
% 3.07/0.92  sup_num_of_clauses:                     1133
% 3.07/0.92  sup_num_in_active:                      88
% 3.07/0.92  sup_num_in_passive:                     1045
% 3.07/0.92  sup_num_of_loops:                       100
% 3.07/0.92  sup_fw_superposition:                   2081
% 3.07/0.92  sup_bw_superposition:                   2036
% 3.07/0.92  sup_immediate_simplified:               1966
% 3.07/0.92  sup_given_eliminated:                   6
% 3.07/0.92  comparisons_done:                       0
% 3.07/0.92  comparisons_avoided:                    0
% 3.07/0.92  
% 3.07/0.92  ------ Simplifications
% 3.07/0.92  
% 3.07/0.92  
% 3.07/0.92  sim_fw_subset_subsumed:                 0
% 3.07/0.92  sim_bw_subset_subsumed:                 0
% 3.07/0.92  sim_fw_subsumed:                        286
% 3.07/0.92  sim_bw_subsumed:                        4
% 3.07/0.92  sim_fw_subsumption_res:                 0
% 3.07/0.92  sim_bw_subsumption_res:                 0
% 3.07/0.92  sim_tautology_del:                      0
% 3.07/0.92  sim_eq_tautology_del:                   209
% 3.07/0.92  sim_eq_res_simp:                        0
% 3.07/0.92  sim_fw_demodulated:                     603
% 3.07/0.92  sim_bw_demodulated:                     153
% 3.07/0.92  sim_light_normalised:                   981
% 3.07/0.92  sim_joinable_taut:                      102
% 3.07/0.92  sim_joinable_simp:                      0
% 3.07/0.92  sim_ac_normalised:                      0
% 3.07/0.92  sim_smt_subsumption:                    0
% 3.07/0.92  
%------------------------------------------------------------------------------
