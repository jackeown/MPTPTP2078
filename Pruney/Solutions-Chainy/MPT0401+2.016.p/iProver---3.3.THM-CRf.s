%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:05 EST 2020

% Result     : Theorem 0.64s
% Output     : CNFRefutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   47 (  59 expanded)
%              Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :    9 (  15 expanded)
%              Depth                    :   13
%              Number of atoms          :   88 ( 132 expanded)
%              Number of equality atoms :   23 (  23 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X1,k1_tarski(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X1,k1_tarski(X0))
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X0)
          & r2_hidden(X2,X1) )
      & r1_setfam_1(X1,k1_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r1_tarski(sK2,X0)
        & r2_hidden(sK2,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,X0)
            & r2_hidden(X2,X1) )
        & r1_setfam_1(X1,k1_tarski(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,sK0)
          & r2_hidden(X2,sK1) )
      & r1_setfam_1(sK1,k1_tarski(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ~ r1_tarski(sK2,sK0)
    & r2_hidden(sK2,sK1)
    & r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16,f15])).

fof(f25,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f24,plain,(
    r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f28,plain,(
    r1_setfam_1(sK1,k2_tarski(sK0,sK0)) ),
    inference(definition_unfolding,[],[f24,f20])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    ~ r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_5,negated_conjecture,
    ( r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_70,plain,
    ( r1_tarski(X0,k3_tarski(X1))
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_5])).

cnf(c_71,plain,
    ( r1_tarski(sK2,k3_tarski(sK1)) ),
    inference(unflattening,[status(thm)],[c_70])).

cnf(c_199,plain,
    ( r1_tarski(sK2,k3_tarski(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_3,plain,
    ( ~ r1_setfam_1(X0,X1)
    | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_6,negated_conjecture,
    ( r1_setfam_1(sK1,k2_tarski(sK0,sK0)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_79,plain,
    ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
    | k2_tarski(sK0,sK0) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_6])).

cnf(c_80,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_tarski(sK0,sK0))) ),
    inference(unflattening,[status(thm)],[c_79])).

cnf(c_198,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_tarski(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_80])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_208,plain,
    ( r1_tarski(k3_tarski(sK1),sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_198,c_0])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X0)
    | r1_tarski(X2,X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_201,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_362,plain,
    ( r1_tarski(X0,k3_tarski(sK1)) != iProver_top
    | r1_tarski(X0,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_208,c_201])).

cnf(c_492,plain,
    ( r1_tarski(sK2,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_199,c_362])).

cnf(c_4,negated_conjecture,
    ( ~ r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_9,plain,
    ( r1_tarski(sK2,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_492,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : iproveropt_run.sh %d %s
% 0.09/0.29  % Computer   : n025.cluster.edu
% 0.09/0.29  % Model      : x86_64 x86_64
% 0.09/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.09/0.29  % Memory     : 8042.1875MB
% 0.09/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.09/0.29  % CPULimit   : 60
% 0.09/0.29  % WCLimit    : 600
% 0.09/0.29  % DateTime   : Tue Dec  1 19:40:35 EST 2020
% 0.09/0.29  % CPUTime    : 
% 0.09/0.29  % Running in FOF mode
% 0.64/0.89  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.64/0.89  
% 0.64/0.89  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.64/0.89  
% 0.64/0.89  ------  iProver source info
% 0.64/0.89  
% 0.64/0.89  git: date: 2020-06-30 10:37:57 +0100
% 0.64/0.89  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.64/0.89  git: non_committed_changes: false
% 0.64/0.89  git: last_make_outside_of_git: false
% 0.64/0.89  
% 0.64/0.89  ------ 
% 0.64/0.89  
% 0.64/0.89  ------ Input Options
% 0.64/0.89  
% 0.64/0.89  --out_options                           all
% 0.64/0.89  --tptp_safe_out                         true
% 0.64/0.89  --problem_path                          ""
% 0.64/0.89  --include_path                          ""
% 0.64/0.89  --clausifier                            res/vclausify_rel
% 0.64/0.89  --clausifier_options                    --mode clausify
% 0.64/0.89  --stdin                                 false
% 0.64/0.89  --stats_out                             all
% 0.64/0.89  
% 0.64/0.89  ------ General Options
% 0.64/0.89  
% 0.64/0.89  --fof                                   false
% 0.64/0.89  --time_out_real                         305.
% 0.64/0.89  --time_out_virtual                      -1.
% 0.64/0.89  --symbol_type_check                     false
% 0.64/0.89  --clausify_out                          false
% 0.64/0.89  --sig_cnt_out                           false
% 0.64/0.89  --trig_cnt_out                          false
% 0.64/0.89  --trig_cnt_out_tolerance                1.
% 0.64/0.89  --trig_cnt_out_sk_spl                   false
% 0.64/0.89  --abstr_cl_out                          false
% 0.64/0.89  
% 0.64/0.89  ------ Global Options
% 0.64/0.89  
% 0.64/0.89  --schedule                              default
% 0.64/0.89  --add_important_lit                     false
% 0.64/0.89  --prop_solver_per_cl                    1000
% 0.64/0.89  --min_unsat_core                        false
% 0.64/0.89  --soft_assumptions                      false
% 0.64/0.89  --soft_lemma_size                       3
% 0.64/0.89  --prop_impl_unit_size                   0
% 0.64/0.89  --prop_impl_unit                        []
% 0.64/0.89  --share_sel_clauses                     true
% 0.64/0.89  --reset_solvers                         false
% 0.64/0.89  --bc_imp_inh                            [conj_cone]
% 0.64/0.89  --conj_cone_tolerance                   3.
% 0.64/0.89  --extra_neg_conj                        none
% 0.64/0.89  --large_theory_mode                     true
% 0.64/0.89  --prolific_symb_bound                   200
% 0.64/0.89  --lt_threshold                          2000
% 0.64/0.89  --clause_weak_htbl                      true
% 0.64/0.89  --gc_record_bc_elim                     false
% 0.64/0.89  
% 0.64/0.89  ------ Preprocessing Options
% 0.64/0.89  
% 0.64/0.89  --preprocessing_flag                    true
% 0.64/0.89  --time_out_prep_mult                    0.1
% 0.64/0.89  --splitting_mode                        input
% 0.64/0.89  --splitting_grd                         true
% 0.64/0.89  --splitting_cvd                         false
% 0.64/0.89  --splitting_cvd_svl                     false
% 0.64/0.89  --splitting_nvd                         32
% 0.64/0.89  --sub_typing                            true
% 0.64/0.89  --prep_gs_sim                           true
% 0.64/0.89  --prep_unflatten                        true
% 0.64/0.89  --prep_res_sim                          true
% 0.64/0.89  --prep_upred                            true
% 0.64/0.89  --prep_sem_filter                       exhaustive
% 0.64/0.89  --prep_sem_filter_out                   false
% 0.64/0.89  --pred_elim                             true
% 0.64/0.89  --res_sim_input                         true
% 0.64/0.89  --eq_ax_congr_red                       true
% 0.64/0.89  --pure_diseq_elim                       true
% 0.64/0.89  --brand_transform                       false
% 0.64/0.89  --non_eq_to_eq                          false
% 0.64/0.89  --prep_def_merge                        true
% 0.64/0.89  --prep_def_merge_prop_impl              false
% 0.64/0.89  --prep_def_merge_mbd                    true
% 0.64/0.89  --prep_def_merge_tr_red                 false
% 0.64/0.89  --prep_def_merge_tr_cl                  false
% 0.64/0.89  --smt_preprocessing                     true
% 0.64/0.89  --smt_ac_axioms                         fast
% 0.64/0.89  --preprocessed_out                      false
% 0.64/0.89  --preprocessed_stats                    false
% 0.64/0.89  
% 0.64/0.89  ------ Abstraction refinement Options
% 0.64/0.89  
% 0.64/0.89  --abstr_ref                             []
% 0.64/0.89  --abstr_ref_prep                        false
% 0.64/0.89  --abstr_ref_until_sat                   false
% 0.64/0.89  --abstr_ref_sig_restrict                funpre
% 0.64/0.89  --abstr_ref_af_restrict_to_split_sk     false
% 0.64/0.89  --abstr_ref_under                       []
% 0.64/0.89  
% 0.64/0.89  ------ SAT Options
% 0.64/0.89  
% 0.64/0.89  --sat_mode                              false
% 0.64/0.89  --sat_fm_restart_options                ""
% 0.64/0.89  --sat_gr_def                            false
% 0.64/0.89  --sat_epr_types                         true
% 0.64/0.89  --sat_non_cyclic_types                  false
% 0.64/0.89  --sat_finite_models                     false
% 0.64/0.89  --sat_fm_lemmas                         false
% 0.64/0.89  --sat_fm_prep                           false
% 0.64/0.89  --sat_fm_uc_incr                        true
% 0.64/0.89  --sat_out_model                         small
% 0.64/0.89  --sat_out_clauses                       false
% 0.64/0.89  
% 0.64/0.89  ------ QBF Options
% 0.64/0.89  
% 0.64/0.89  --qbf_mode                              false
% 0.64/0.89  --qbf_elim_univ                         false
% 0.64/0.89  --qbf_dom_inst                          none
% 0.64/0.89  --qbf_dom_pre_inst                      false
% 0.64/0.89  --qbf_sk_in                             false
% 0.64/0.89  --qbf_pred_elim                         true
% 0.64/0.89  --qbf_split                             512
% 0.64/0.89  
% 0.64/0.89  ------ BMC1 Options
% 0.64/0.89  
% 0.64/0.89  --bmc1_incremental                      false
% 0.64/0.89  --bmc1_axioms                           reachable_all
% 0.64/0.89  --bmc1_min_bound                        0
% 0.64/0.89  --bmc1_max_bound                        -1
% 0.64/0.89  --bmc1_max_bound_default                -1
% 0.64/0.89  --bmc1_symbol_reachability              true
% 0.64/0.89  --bmc1_property_lemmas                  false
% 0.64/0.89  --bmc1_k_induction                      false
% 0.64/0.89  --bmc1_non_equiv_states                 false
% 0.64/0.89  --bmc1_deadlock                         false
% 0.64/0.89  --bmc1_ucm                              false
% 0.64/0.89  --bmc1_add_unsat_core                   none
% 0.64/0.89  --bmc1_unsat_core_children              false
% 0.64/0.89  --bmc1_unsat_core_extrapolate_axioms    false
% 0.64/0.89  --bmc1_out_stat                         full
% 0.64/0.89  --bmc1_ground_init                      false
% 0.64/0.89  --bmc1_pre_inst_next_state              false
% 0.64/0.89  --bmc1_pre_inst_state                   false
% 0.64/0.89  --bmc1_pre_inst_reach_state             false
% 0.64/0.89  --bmc1_out_unsat_core                   false
% 0.64/0.89  --bmc1_aig_witness_out                  false
% 0.64/0.89  --bmc1_verbose                          false
% 0.64/0.89  --bmc1_dump_clauses_tptp                false
% 0.64/0.89  --bmc1_dump_unsat_core_tptp             false
% 0.64/0.89  --bmc1_dump_file                        -
% 0.64/0.89  --bmc1_ucm_expand_uc_limit              128
% 0.64/0.89  --bmc1_ucm_n_expand_iterations          6
% 0.64/0.89  --bmc1_ucm_extend_mode                  1
% 0.64/0.89  --bmc1_ucm_init_mode                    2
% 0.64/0.89  --bmc1_ucm_cone_mode                    none
% 0.64/0.89  --bmc1_ucm_reduced_relation_type        0
% 0.64/0.89  --bmc1_ucm_relax_model                  4
% 0.64/0.89  --bmc1_ucm_full_tr_after_sat            true
% 0.64/0.89  --bmc1_ucm_expand_neg_assumptions       false
% 0.64/0.89  --bmc1_ucm_layered_model                none
% 0.64/0.89  --bmc1_ucm_max_lemma_size               10
% 0.64/0.89  
% 0.64/0.89  ------ AIG Options
% 0.64/0.89  
% 0.64/0.89  --aig_mode                              false
% 0.64/0.89  
% 0.64/0.89  ------ Instantiation Options
% 0.64/0.89  
% 0.64/0.89  --instantiation_flag                    true
% 0.64/0.89  --inst_sos_flag                         false
% 0.64/0.89  --inst_sos_phase                        true
% 0.64/0.89  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.64/0.89  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.64/0.89  --inst_lit_sel_side                     num_symb
% 0.64/0.89  --inst_solver_per_active                1400
% 0.64/0.89  --inst_solver_calls_frac                1.
% 0.64/0.89  --inst_passive_queue_type               priority_queues
% 0.64/0.89  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.64/0.89  --inst_passive_queues_freq              [25;2]
% 0.64/0.89  --inst_dismatching                      true
% 0.64/0.89  --inst_eager_unprocessed_to_passive     true
% 0.64/0.89  --inst_prop_sim_given                   true
% 0.64/0.89  --inst_prop_sim_new                     false
% 0.64/0.89  --inst_subs_new                         false
% 0.64/0.89  --inst_eq_res_simp                      false
% 0.64/0.89  --inst_subs_given                       false
% 0.64/0.89  --inst_orphan_elimination               true
% 0.64/0.89  --inst_learning_loop_flag               true
% 0.64/0.89  --inst_learning_start                   3000
% 0.64/0.89  --inst_learning_factor                  2
% 0.64/0.89  --inst_start_prop_sim_after_learn       3
% 0.64/0.89  --inst_sel_renew                        solver
% 0.64/0.89  --inst_lit_activity_flag                true
% 0.64/0.89  --inst_restr_to_given                   false
% 0.64/0.89  --inst_activity_threshold               500
% 0.64/0.89  --inst_out_proof                        true
% 0.64/0.89  
% 0.64/0.89  ------ Resolution Options
% 0.64/0.89  
% 0.64/0.89  --resolution_flag                       true
% 0.64/0.89  --res_lit_sel                           adaptive
% 0.64/0.89  --res_lit_sel_side                      none
% 0.64/0.89  --res_ordering                          kbo
% 0.64/0.89  --res_to_prop_solver                    active
% 0.64/0.89  --res_prop_simpl_new                    false
% 0.64/0.89  --res_prop_simpl_given                  true
% 0.64/0.89  --res_passive_queue_type                priority_queues
% 0.64/0.89  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.64/0.89  --res_passive_queues_freq               [15;5]
% 0.64/0.89  --res_forward_subs                      full
% 0.64/0.89  --res_backward_subs                     full
% 0.64/0.89  --res_forward_subs_resolution           true
% 0.64/0.89  --res_backward_subs_resolution          true
% 0.64/0.89  --res_orphan_elimination                true
% 0.64/0.89  --res_time_limit                        2.
% 0.64/0.89  --res_out_proof                         true
% 0.64/0.89  
% 0.64/0.89  ------ Superposition Options
% 0.64/0.89  
% 0.64/0.89  --superposition_flag                    true
% 0.64/0.89  --sup_passive_queue_type                priority_queues
% 0.64/0.89  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.64/0.89  --sup_passive_queues_freq               [8;1;4]
% 0.64/0.89  --demod_completeness_check              fast
% 0.64/0.89  --demod_use_ground                      true
% 0.64/0.89  --sup_to_prop_solver                    passive
% 0.64/0.89  --sup_prop_simpl_new                    true
% 0.64/0.89  --sup_prop_simpl_given                  true
% 0.64/0.89  --sup_fun_splitting                     false
% 0.64/0.89  --sup_smt_interval                      50000
% 0.64/0.89  
% 0.64/0.89  ------ Superposition Simplification Setup
% 0.64/0.89  
% 0.64/0.89  --sup_indices_passive                   []
% 0.64/0.89  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.64/0.89  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.64/0.89  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.64/0.89  --sup_full_triv                         [TrivRules;PropSubs]
% 0.64/0.89  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.64/0.89  --sup_full_bw                           [BwDemod]
% 0.64/0.89  --sup_immed_triv                        [TrivRules]
% 0.64/0.89  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.64/0.89  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.64/0.89  --sup_immed_bw_main                     []
% 0.64/0.89  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.64/0.89  --sup_input_triv                        [Unflattening;TrivRules]
% 0.64/0.89  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.64/0.89  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.64/0.89  
% 0.64/0.89  ------ Combination Options
% 0.64/0.89  
% 0.64/0.89  --comb_res_mult                         3
% 0.64/0.89  --comb_sup_mult                         2
% 0.64/0.89  --comb_inst_mult                        10
% 0.64/0.89  
% 0.64/0.89  ------ Debug Options
% 0.64/0.89  
% 0.64/0.89  --dbg_backtrace                         false
% 0.64/0.89  --dbg_dump_prop_clauses                 false
% 0.64/0.89  --dbg_dump_prop_clauses_file            -
% 0.64/0.89  --dbg_out_stat                          false
% 0.64/0.89  ------ Parsing...
% 0.64/0.89  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.64/0.89  
% 0.64/0.89  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.64/0.89  
% 0.64/0.89  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.64/0.89  
% 0.64/0.89  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.64/0.89  ------ Proving...
% 0.64/0.89  ------ Problem Properties 
% 0.64/0.89  
% 0.64/0.89  
% 0.64/0.89  clauses                                 5
% 0.64/0.89  conjectures                             1
% 0.64/0.89  EPR                                     2
% 0.64/0.89  Horn                                    5
% 0.64/0.89  unary                                   4
% 0.64/0.89  binary                                  0
% 0.64/0.89  lits                                    7
% 0.64/0.89  lits eq                                 1
% 0.64/0.89  fd_pure                                 0
% 0.64/0.89  fd_pseudo                               0
% 0.64/0.89  fd_cond                                 0
% 0.64/0.89  fd_pseudo_cond                          0
% 0.64/0.89  AC symbols                              0
% 0.64/0.89  
% 0.64/0.89  ------ Schedule dynamic 5 is on 
% 0.64/0.89  
% 0.64/0.89  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.64/0.89  
% 0.64/0.89  
% 0.64/0.89  ------ 
% 0.64/0.89  Current options:
% 0.64/0.89  ------ 
% 0.64/0.89  
% 0.64/0.89  ------ Input Options
% 0.64/0.89  
% 0.64/0.89  --out_options                           all
% 0.64/0.89  --tptp_safe_out                         true
% 0.64/0.89  --problem_path                          ""
% 0.64/0.89  --include_path                          ""
% 0.64/0.89  --clausifier                            res/vclausify_rel
% 0.64/0.89  --clausifier_options                    --mode clausify
% 0.64/0.89  --stdin                                 false
% 0.64/0.89  --stats_out                             all
% 0.64/0.89  
% 0.64/0.89  ------ General Options
% 0.64/0.89  
% 0.64/0.89  --fof                                   false
% 0.64/0.89  --time_out_real                         305.
% 0.64/0.89  --time_out_virtual                      -1.
% 0.64/0.89  --symbol_type_check                     false
% 0.64/0.89  --clausify_out                          false
% 0.64/0.89  --sig_cnt_out                           false
% 0.64/0.89  --trig_cnt_out                          false
% 0.64/0.89  --trig_cnt_out_tolerance                1.
% 0.64/0.89  --trig_cnt_out_sk_spl                   false
% 0.64/0.89  --abstr_cl_out                          false
% 0.64/0.89  
% 0.64/0.89  ------ Global Options
% 0.64/0.89  
% 0.64/0.89  --schedule                              default
% 0.64/0.89  --add_important_lit                     false
% 0.64/0.89  --prop_solver_per_cl                    1000
% 0.64/0.89  --min_unsat_core                        false
% 0.64/0.89  --soft_assumptions                      false
% 0.64/0.89  --soft_lemma_size                       3
% 0.64/0.89  --prop_impl_unit_size                   0
% 0.64/0.89  --prop_impl_unit                        []
% 0.64/0.89  --share_sel_clauses                     true
% 0.64/0.89  --reset_solvers                         false
% 0.64/0.89  --bc_imp_inh                            [conj_cone]
% 0.64/0.89  --conj_cone_tolerance                   3.
% 0.64/0.89  --extra_neg_conj                        none
% 0.64/0.89  --large_theory_mode                     true
% 0.64/0.89  --prolific_symb_bound                   200
% 0.64/0.89  --lt_threshold                          2000
% 0.64/0.89  --clause_weak_htbl                      true
% 0.64/0.89  --gc_record_bc_elim                     false
% 0.64/0.89  
% 0.64/0.89  ------ Preprocessing Options
% 0.64/0.89  
% 0.64/0.89  --preprocessing_flag                    true
% 0.64/0.89  --time_out_prep_mult                    0.1
% 0.64/0.89  --splitting_mode                        input
% 0.64/0.89  --splitting_grd                         true
% 0.64/0.89  --splitting_cvd                         false
% 0.64/0.89  --splitting_cvd_svl                     false
% 0.64/0.89  --splitting_nvd                         32
% 0.64/0.89  --sub_typing                            true
% 0.64/0.89  --prep_gs_sim                           true
% 0.64/0.89  --prep_unflatten                        true
% 0.64/0.89  --prep_res_sim                          true
% 0.64/0.89  --prep_upred                            true
% 0.64/0.89  --prep_sem_filter                       exhaustive
% 0.64/0.89  --prep_sem_filter_out                   false
% 0.64/0.89  --pred_elim                             true
% 0.64/0.89  --res_sim_input                         true
% 0.64/0.89  --eq_ax_congr_red                       true
% 0.64/0.89  --pure_diseq_elim                       true
% 0.64/0.89  --brand_transform                       false
% 0.64/0.89  --non_eq_to_eq                          false
% 0.64/0.89  --prep_def_merge                        true
% 0.64/0.89  --prep_def_merge_prop_impl              false
% 0.64/0.89  --prep_def_merge_mbd                    true
% 0.64/0.89  --prep_def_merge_tr_red                 false
% 0.64/0.89  --prep_def_merge_tr_cl                  false
% 0.64/0.89  --smt_preprocessing                     true
% 0.64/0.89  --smt_ac_axioms                         fast
% 0.64/0.89  --preprocessed_out                      false
% 0.64/0.89  --preprocessed_stats                    false
% 0.64/0.89  
% 0.64/0.89  ------ Abstraction refinement Options
% 0.64/0.89  
% 0.64/0.89  --abstr_ref                             []
% 0.64/0.89  --abstr_ref_prep                        false
% 0.64/0.89  --abstr_ref_until_sat                   false
% 0.64/0.89  --abstr_ref_sig_restrict                funpre
% 0.64/0.89  --abstr_ref_af_restrict_to_split_sk     false
% 0.64/0.89  --abstr_ref_under                       []
% 0.64/0.89  
% 0.64/0.89  ------ SAT Options
% 0.64/0.89  
% 0.64/0.89  --sat_mode                              false
% 0.64/0.89  --sat_fm_restart_options                ""
% 0.64/0.89  --sat_gr_def                            false
% 0.64/0.89  --sat_epr_types                         true
% 0.64/0.89  --sat_non_cyclic_types                  false
% 0.64/0.89  --sat_finite_models                     false
% 0.64/0.89  --sat_fm_lemmas                         false
% 0.64/0.89  --sat_fm_prep                           false
% 0.64/0.89  --sat_fm_uc_incr                        true
% 0.64/0.89  --sat_out_model                         small
% 0.64/0.89  --sat_out_clauses                       false
% 0.64/0.89  
% 0.64/0.89  ------ QBF Options
% 0.64/0.89  
% 0.64/0.89  --qbf_mode                              false
% 0.64/0.89  --qbf_elim_univ                         false
% 0.64/0.89  --qbf_dom_inst                          none
% 0.64/0.89  --qbf_dom_pre_inst                      false
% 0.64/0.89  --qbf_sk_in                             false
% 0.64/0.89  --qbf_pred_elim                         true
% 0.64/0.89  --qbf_split                             512
% 0.64/0.89  
% 0.64/0.89  ------ BMC1 Options
% 0.64/0.89  
% 0.64/0.89  --bmc1_incremental                      false
% 0.64/0.89  --bmc1_axioms                           reachable_all
% 0.64/0.89  --bmc1_min_bound                        0
% 0.64/0.89  --bmc1_max_bound                        -1
% 0.64/0.89  --bmc1_max_bound_default                -1
% 0.64/0.89  --bmc1_symbol_reachability              true
% 0.64/0.89  --bmc1_property_lemmas                  false
% 0.64/0.89  --bmc1_k_induction                      false
% 0.64/0.89  --bmc1_non_equiv_states                 false
% 0.64/0.89  --bmc1_deadlock                         false
% 0.64/0.89  --bmc1_ucm                              false
% 0.64/0.89  --bmc1_add_unsat_core                   none
% 0.64/0.89  --bmc1_unsat_core_children              false
% 0.64/0.89  --bmc1_unsat_core_extrapolate_axioms    false
% 0.64/0.89  --bmc1_out_stat                         full
% 0.64/0.89  --bmc1_ground_init                      false
% 0.64/0.89  --bmc1_pre_inst_next_state              false
% 0.64/0.89  --bmc1_pre_inst_state                   false
% 0.64/0.89  --bmc1_pre_inst_reach_state             false
% 0.64/0.89  --bmc1_out_unsat_core                   false
% 0.64/0.89  --bmc1_aig_witness_out                  false
% 0.64/0.89  --bmc1_verbose                          false
% 0.64/0.89  --bmc1_dump_clauses_tptp                false
% 0.64/0.89  --bmc1_dump_unsat_core_tptp             false
% 0.64/0.89  --bmc1_dump_file                        -
% 0.64/0.89  --bmc1_ucm_expand_uc_limit              128
% 0.64/0.89  --bmc1_ucm_n_expand_iterations          6
% 0.64/0.89  --bmc1_ucm_extend_mode                  1
% 0.64/0.89  --bmc1_ucm_init_mode                    2
% 0.64/0.89  --bmc1_ucm_cone_mode                    none
% 0.64/0.89  --bmc1_ucm_reduced_relation_type        0
% 0.64/0.89  --bmc1_ucm_relax_model                  4
% 0.64/0.89  --bmc1_ucm_full_tr_after_sat            true
% 0.64/0.89  --bmc1_ucm_expand_neg_assumptions       false
% 0.64/0.89  --bmc1_ucm_layered_model                none
% 0.64/0.89  --bmc1_ucm_max_lemma_size               10
% 0.64/0.89  
% 0.64/0.89  ------ AIG Options
% 0.64/0.89  
% 0.64/0.89  --aig_mode                              false
% 0.64/0.89  
% 0.64/0.89  ------ Instantiation Options
% 0.64/0.89  
% 0.64/0.89  --instantiation_flag                    true
% 0.64/0.89  --inst_sos_flag                         false
% 0.64/0.89  --inst_sos_phase                        true
% 0.64/0.89  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.64/0.89  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.64/0.89  --inst_lit_sel_side                     none
% 0.64/0.89  --inst_solver_per_active                1400
% 0.64/0.89  --inst_solver_calls_frac                1.
% 0.64/0.89  --inst_passive_queue_type               priority_queues
% 0.64/0.89  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.64/0.89  --inst_passive_queues_freq              [25;2]
% 0.64/0.89  --inst_dismatching                      true
% 0.64/0.89  --inst_eager_unprocessed_to_passive     true
% 0.64/0.89  --inst_prop_sim_given                   true
% 0.64/0.89  --inst_prop_sim_new                     false
% 0.64/0.89  --inst_subs_new                         false
% 0.64/0.89  --inst_eq_res_simp                      false
% 0.64/0.89  --inst_subs_given                       false
% 0.64/0.89  --inst_orphan_elimination               true
% 0.64/0.89  --inst_learning_loop_flag               true
% 0.64/0.89  --inst_learning_start                   3000
% 0.64/0.89  --inst_learning_factor                  2
% 0.64/0.89  --inst_start_prop_sim_after_learn       3
% 0.64/0.89  --inst_sel_renew                        solver
% 0.64/0.89  --inst_lit_activity_flag                true
% 0.64/0.89  --inst_restr_to_given                   false
% 0.64/0.89  --inst_activity_threshold               500
% 0.64/0.89  --inst_out_proof                        true
% 0.64/0.89  
% 0.64/0.89  ------ Resolution Options
% 0.64/0.89  
% 0.64/0.89  --resolution_flag                       false
% 0.64/0.89  --res_lit_sel                           adaptive
% 0.64/0.89  --res_lit_sel_side                      none
% 0.64/0.89  --res_ordering                          kbo
% 0.64/0.89  --res_to_prop_solver                    active
% 0.64/0.89  --res_prop_simpl_new                    false
% 0.64/0.89  --res_prop_simpl_given                  true
% 0.64/0.89  --res_passive_queue_type                priority_queues
% 0.64/0.89  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.64/0.89  --res_passive_queues_freq               [15;5]
% 0.64/0.89  --res_forward_subs                      full
% 0.64/0.89  --res_backward_subs                     full
% 0.64/0.89  --res_forward_subs_resolution           true
% 0.64/0.89  --res_backward_subs_resolution          true
% 0.64/0.89  --res_orphan_elimination                true
% 0.64/0.89  --res_time_limit                        2.
% 0.64/0.89  --res_out_proof                         true
% 0.64/0.89  
% 0.64/0.89  ------ Superposition Options
% 0.64/0.89  
% 0.64/0.89  --superposition_flag                    true
% 0.64/0.89  --sup_passive_queue_type                priority_queues
% 0.64/0.89  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.64/0.89  --sup_passive_queues_freq               [8;1;4]
% 0.64/0.89  --demod_completeness_check              fast
% 0.64/0.89  --demod_use_ground                      true
% 0.64/0.89  --sup_to_prop_solver                    passive
% 0.64/0.89  --sup_prop_simpl_new                    true
% 0.64/0.89  --sup_prop_simpl_given                  true
% 0.64/0.89  --sup_fun_splitting                     false
% 0.64/0.89  --sup_smt_interval                      50000
% 0.64/0.89  
% 0.64/0.89  ------ Superposition Simplification Setup
% 0.64/0.89  
% 0.64/0.89  --sup_indices_passive                   []
% 0.64/0.89  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.64/0.89  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.64/0.89  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.64/0.89  --sup_full_triv                         [TrivRules;PropSubs]
% 0.64/0.89  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.64/0.89  --sup_full_bw                           [BwDemod]
% 0.64/0.89  --sup_immed_triv                        [TrivRules]
% 0.64/0.89  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.64/0.89  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.64/0.89  --sup_immed_bw_main                     []
% 0.64/0.89  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.64/0.89  --sup_input_triv                        [Unflattening;TrivRules]
% 0.64/0.89  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.64/0.89  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.64/0.89  
% 0.64/0.89  ------ Combination Options
% 0.64/0.89  
% 0.64/0.89  --comb_res_mult                         3
% 0.64/0.89  --comb_sup_mult                         2
% 0.64/0.89  --comb_inst_mult                        10
% 0.64/0.89  
% 0.64/0.89  ------ Debug Options
% 0.64/0.89  
% 0.64/0.89  --dbg_backtrace                         false
% 0.64/0.89  --dbg_dump_prop_clauses                 false
% 0.64/0.89  --dbg_dump_prop_clauses_file            -
% 0.64/0.89  --dbg_out_stat                          false
% 0.64/0.89  
% 0.64/0.89  
% 0.64/0.89  
% 0.64/0.89  
% 0.64/0.89  ------ Proving...
% 0.64/0.89  
% 0.64/0.89  
% 0.64/0.89  % SZS status Theorem for theBenchmark.p
% 0.64/0.89  
% 0.64/0.89  % SZS output start CNFRefutation for theBenchmark.p
% 0.64/0.89  
% 0.64/0.89  fof(f5,axiom,(
% 0.64/0.89    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.64/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.64/0.89  
% 0.64/0.89  fof(f12,plain,(
% 0.64/0.89    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.64/0.89    inference(ennf_transformation,[],[f5])).
% 0.64/0.89  
% 0.64/0.89  fof(f22,plain,(
% 0.64/0.89    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.64/0.89    inference(cnf_transformation,[],[f12])).
% 0.64/0.89  
% 0.64/0.89  fof(f7,conjecture,(
% 0.64/0.89    ! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.64/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.64/0.89  
% 0.64/0.89  fof(f8,negated_conjecture,(
% 0.64/0.89    ~! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.64/0.89    inference(negated_conjecture,[],[f7])).
% 0.64/0.89  
% 0.64/0.89  fof(f14,plain,(
% 0.64/0.89    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0)))),
% 0.64/0.89    inference(ennf_transformation,[],[f8])).
% 0.64/0.89  
% 0.64/0.89  fof(f16,plain,(
% 0.64/0.89    ( ! [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) => (~r1_tarski(sK2,X0) & r2_hidden(sK2,X1))) )),
% 0.64/0.89    introduced(choice_axiom,[])).
% 0.64/0.89  
% 0.64/0.89  fof(f15,plain,(
% 0.64/0.89    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0))) => (? [X2] : (~r1_tarski(X2,sK0) & r2_hidden(X2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0)))),
% 0.64/0.89    introduced(choice_axiom,[])).
% 0.64/0.89  
% 0.64/0.89  fof(f17,plain,(
% 0.64/0.89    (~r1_tarski(sK2,sK0) & r2_hidden(sK2,sK1)) & r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.64/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16,f15])).
% 0.64/0.89  
% 0.64/0.89  fof(f25,plain,(
% 0.64/0.89    r2_hidden(sK2,sK1)),
% 0.64/0.89    inference(cnf_transformation,[],[f17])).
% 0.64/0.89  
% 0.64/0.89  fof(f6,axiom,(
% 0.64/0.89    ! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.64/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.64/0.89  
% 0.64/0.89  fof(f13,plain,(
% 0.64/0.89    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1))),
% 0.64/0.89    inference(ennf_transformation,[],[f6])).
% 0.64/0.89  
% 0.64/0.89  fof(f23,plain,(
% 0.64/0.89    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_setfam_1(X0,X1)) )),
% 0.64/0.89    inference(cnf_transformation,[],[f13])).
% 0.64/0.89  
% 0.64/0.89  fof(f24,plain,(
% 0.64/0.89    r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.64/0.89    inference(cnf_transformation,[],[f17])).
% 0.64/0.89  
% 0.64/0.89  fof(f3,axiom,(
% 0.64/0.89    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.64/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.64/0.89  
% 0.64/0.89  fof(f20,plain,(
% 0.64/0.89    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.64/0.89    inference(cnf_transformation,[],[f3])).
% 0.64/0.89  
% 0.64/0.89  fof(f28,plain,(
% 0.64/0.89    r1_setfam_1(sK1,k2_tarski(sK0,sK0))),
% 0.64/0.89    inference(definition_unfolding,[],[f24,f20])).
% 0.64/0.89  
% 0.64/0.89  fof(f1,axiom,(
% 0.64/0.89    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.64/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.64/0.89  
% 0.64/0.89  fof(f9,plain,(
% 0.64/0.89    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.64/0.89    inference(rectify,[],[f1])).
% 0.64/0.89  
% 0.64/0.89  fof(f18,plain,(
% 0.64/0.89    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.64/0.89    inference(cnf_transformation,[],[f9])).
% 0.64/0.89  
% 0.64/0.89  fof(f4,axiom,(
% 0.64/0.89    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.64/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.64/0.89  
% 0.64/0.89  fof(f21,plain,(
% 0.64/0.89    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.64/0.89    inference(cnf_transformation,[],[f4])).
% 0.64/0.89  
% 0.64/0.89  fof(f27,plain,(
% 0.64/0.89    ( ! [X0] : (k3_tarski(k2_tarski(X0,X0)) = X0) )),
% 0.64/0.89    inference(definition_unfolding,[],[f18,f21])).
% 0.64/0.89  
% 0.64/0.89  fof(f2,axiom,(
% 0.64/0.89    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.64/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.64/0.89  
% 0.64/0.89  fof(f10,plain,(
% 0.64/0.89    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.64/0.89    inference(ennf_transformation,[],[f2])).
% 0.64/0.89  
% 0.64/0.89  fof(f11,plain,(
% 0.64/0.89    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.64/0.89    inference(flattening,[],[f10])).
% 0.64/0.89  
% 0.64/0.89  fof(f19,plain,(
% 0.64/0.89    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.64/0.89    inference(cnf_transformation,[],[f11])).
% 0.64/0.89  
% 0.64/0.89  fof(f26,plain,(
% 0.64/0.89    ~r1_tarski(sK2,sK0)),
% 0.64/0.89    inference(cnf_transformation,[],[f17])).
% 0.64/0.89  
% 0.64/0.89  cnf(c_2,plain,
% 0.64/0.89      ( ~ r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1)) ),
% 0.64/0.89      inference(cnf_transformation,[],[f22]) ).
% 0.64/0.89  
% 0.64/0.89  cnf(c_5,negated_conjecture,
% 0.64/0.89      ( r2_hidden(sK2,sK1) ),
% 0.64/0.89      inference(cnf_transformation,[],[f25]) ).
% 0.64/0.89  
% 0.64/0.89  cnf(c_70,plain,
% 0.64/0.89      ( r1_tarski(X0,k3_tarski(X1)) | sK1 != X1 | sK2 != X0 ),
% 0.64/0.89      inference(resolution_lifted,[status(thm)],[c_2,c_5]) ).
% 0.64/0.89  
% 0.64/0.89  cnf(c_71,plain,
% 0.64/0.89      ( r1_tarski(sK2,k3_tarski(sK1)) ),
% 0.64/0.89      inference(unflattening,[status(thm)],[c_70]) ).
% 0.64/0.89  
% 0.64/0.89  cnf(c_199,plain,
% 0.64/0.89      ( r1_tarski(sK2,k3_tarski(sK1)) = iProver_top ),
% 0.64/0.89      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 0.64/0.89  
% 0.64/0.89  cnf(c_3,plain,
% 0.64/0.89      ( ~ r1_setfam_1(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ),
% 0.64/0.89      inference(cnf_transformation,[],[f23]) ).
% 0.64/0.89  
% 0.64/0.89  cnf(c_6,negated_conjecture,
% 0.64/0.89      ( r1_setfam_1(sK1,k2_tarski(sK0,sK0)) ),
% 0.64/0.89      inference(cnf_transformation,[],[f28]) ).
% 0.64/0.89  
% 0.64/0.89  cnf(c_79,plain,
% 0.64/0.89      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
% 0.64/0.89      | k2_tarski(sK0,sK0) != X1
% 0.64/0.89      | sK1 != X0 ),
% 0.64/0.89      inference(resolution_lifted,[status(thm)],[c_3,c_6]) ).
% 0.64/0.89  
% 0.64/0.89  cnf(c_80,plain,
% 0.64/0.89      ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_tarski(sK0,sK0))) ),
% 0.64/0.89      inference(unflattening,[status(thm)],[c_79]) ).
% 0.64/0.89  
% 0.64/0.89  cnf(c_198,plain,
% 0.64/0.89      ( r1_tarski(k3_tarski(sK1),k3_tarski(k2_tarski(sK0,sK0))) = iProver_top ),
% 0.64/0.89      inference(predicate_to_equality,[status(thm)],[c_80]) ).
% 0.64/0.89  
% 0.64/0.89  cnf(c_0,plain,
% 0.64/0.89      ( k3_tarski(k2_tarski(X0,X0)) = X0 ),
% 0.64/0.89      inference(cnf_transformation,[],[f27]) ).
% 0.64/0.89  
% 0.64/0.89  cnf(c_208,plain,
% 0.64/0.89      ( r1_tarski(k3_tarski(sK1),sK0) = iProver_top ),
% 0.64/0.89      inference(demodulation,[status(thm)],[c_198,c_0]) ).
% 0.64/0.89  
% 0.64/0.89  cnf(c_1,plain,
% 0.64/0.89      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X2,X0) | r1_tarski(X2,X1) ),
% 0.64/0.89      inference(cnf_transformation,[],[f19]) ).
% 0.64/0.89  
% 0.64/0.89  cnf(c_201,plain,
% 0.64/0.89      ( r1_tarski(X0,X1) != iProver_top
% 0.64/0.89      | r1_tarski(X2,X0) != iProver_top
% 0.64/0.89      | r1_tarski(X2,X1) = iProver_top ),
% 0.64/0.89      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 0.64/0.89  
% 0.64/0.89  cnf(c_362,plain,
% 0.64/0.89      ( r1_tarski(X0,k3_tarski(sK1)) != iProver_top
% 0.64/0.89      | r1_tarski(X0,sK0) = iProver_top ),
% 0.64/0.89      inference(superposition,[status(thm)],[c_208,c_201]) ).
% 0.64/0.89  
% 0.64/0.89  cnf(c_492,plain,
% 0.64/0.89      ( r1_tarski(sK2,sK0) = iProver_top ),
% 0.64/0.89      inference(superposition,[status(thm)],[c_199,c_362]) ).
% 0.64/0.89  
% 0.64/0.89  cnf(c_4,negated_conjecture,
% 0.64/0.89      ( ~ r1_tarski(sK2,sK0) ),
% 0.64/0.89      inference(cnf_transformation,[],[f26]) ).
% 0.64/0.89  
% 0.64/0.89  cnf(c_9,plain,
% 0.64/0.89      ( r1_tarski(sK2,sK0) != iProver_top ),
% 0.64/0.89      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 0.64/0.89  
% 0.64/0.89  cnf(contradiction,plain,
% 0.64/0.89      ( $false ),
% 0.64/0.89      inference(minisat,[status(thm)],[c_492,c_9]) ).
% 0.64/0.89  
% 0.64/0.89  
% 0.64/0.89  % SZS output end CNFRefutation for theBenchmark.p
% 0.64/0.89  
% 0.64/0.89  ------                               Statistics
% 0.64/0.89  
% 0.64/0.89  ------ General
% 0.64/0.89  
% 0.64/0.89  abstr_ref_over_cycles:                  0
% 0.64/0.89  abstr_ref_under_cycles:                 0
% 0.64/0.89  gc_basic_clause_elim:                   0
% 0.64/0.89  forced_gc_time:                         0
% 0.64/0.89  parsing_time:                           0.012
% 0.64/0.89  unif_index_cands_time:                  0.
% 0.64/0.89  unif_index_add_time:                    0.
% 0.64/0.89  orderings_time:                         0.
% 0.64/0.89  out_proof_time:                         0.006
% 0.64/0.89  total_time:                             0.05
% 0.64/0.89  num_of_symbols:                         39
% 0.64/0.89  num_of_terms:                           451
% 0.64/0.89  
% 0.64/0.89  ------ Preprocessing
% 0.64/0.89  
% 0.64/0.89  num_of_splits:                          0
% 0.64/0.89  num_of_split_atoms:                     0
% 0.64/0.89  num_of_reused_defs:                     0
% 0.64/0.89  num_eq_ax_congr_red:                    0
% 0.64/0.89  num_of_sem_filtered_clauses:            1
% 0.64/0.89  num_of_subtypes:                        0
% 0.64/0.89  monotx_restored_types:                  0
% 0.64/0.89  sat_num_of_epr_types:                   0
% 0.64/0.89  sat_num_of_non_cyclic_types:            0
% 0.64/0.89  sat_guarded_non_collapsed_types:        0
% 0.64/0.89  num_pure_diseq_elim:                    0
% 0.64/0.89  simp_replaced_by:                       0
% 0.64/0.89  res_preprocessed:                       33
% 0.64/0.89  prep_upred:                             0
% 0.64/0.89  prep_unflattend:                        4
% 0.64/0.89  smt_new_axioms:                         0
% 0.64/0.89  pred_elim_cands:                        1
% 0.64/0.89  pred_elim:                              2
% 0.64/0.89  pred_elim_cl:                           2
% 0.64/0.89  pred_elim_cycles:                       4
% 0.64/0.89  merged_defs:                            0
% 0.64/0.89  merged_defs_ncl:                        0
% 0.64/0.89  bin_hyper_res:                          0
% 0.64/0.89  prep_cycles:                            4
% 0.64/0.89  pred_elim_time:                         0.
% 0.64/0.89  splitting_time:                         0.
% 0.64/0.89  sem_filter_time:                        0.
% 0.64/0.89  monotx_time:                            0.
% 0.64/0.89  subtype_inf_time:                       0.
% 0.64/0.89  
% 0.64/0.89  ------ Problem properties
% 0.64/0.89  
% 0.64/0.89  clauses:                                5
% 0.64/0.89  conjectures:                            1
% 0.64/0.89  epr:                                    2
% 0.64/0.89  horn:                                   5
% 0.64/0.89  ground:                                 3
% 0.64/0.89  unary:                                  4
% 0.64/0.89  binary:                                 0
% 0.64/0.89  lits:                                   7
% 0.64/0.89  lits_eq:                                1
% 0.64/0.89  fd_pure:                                0
% 0.64/0.89  fd_pseudo:                              0
% 0.64/0.89  fd_cond:                                0
% 0.64/0.89  fd_pseudo_cond:                         0
% 0.64/0.89  ac_symbols:                             0
% 0.64/0.89  
% 0.64/0.89  ------ Propositional Solver
% 0.64/0.89  
% 0.64/0.89  prop_solver_calls:                      25
% 0.64/0.89  prop_fast_solver_calls:                 131
% 0.64/0.89  smt_solver_calls:                       0
% 0.64/0.89  smt_fast_solver_calls:                  0
% 0.64/0.89  prop_num_of_clauses:                    180
% 0.64/0.89  prop_preprocess_simplified:             854
% 0.64/0.89  prop_fo_subsumed:                       0
% 0.64/0.89  prop_solver_time:                       0.
% 0.64/0.89  smt_solver_time:                        0.
% 0.64/0.89  smt_fast_solver_time:                   0.
% 0.64/0.89  prop_fast_solver_time:                  0.
% 0.64/0.89  prop_unsat_core_time:                   0.
% 0.64/0.89  
% 0.64/0.89  ------ QBF
% 0.64/0.89  
% 0.64/0.89  qbf_q_res:                              0
% 0.64/0.89  qbf_num_tautologies:                    0
% 0.64/0.89  qbf_prep_cycles:                        0
% 0.64/0.89  
% 0.64/0.89  ------ BMC1
% 0.64/0.89  
% 0.64/0.89  bmc1_current_bound:                     -1
% 0.64/0.89  bmc1_last_solved_bound:                 -1
% 0.64/0.89  bmc1_unsat_core_size:                   -1
% 0.64/0.89  bmc1_unsat_core_parents_size:           -1
% 0.64/0.89  bmc1_merge_next_fun:                    0
% 0.64/0.89  bmc1_unsat_core_clauses_time:           0.
% 0.64/0.89  
% 0.64/0.89  ------ Instantiation
% 0.64/0.89  
% 0.64/0.89  inst_num_of_clauses:                    61
% 0.64/0.89  inst_num_in_passive:                    16
% 0.64/0.89  inst_num_in_active:                     35
% 0.64/0.89  inst_num_in_unprocessed:                10
% 0.64/0.89  inst_num_of_loops:                      40
% 0.64/0.89  inst_num_of_learning_restarts:          0
% 0.64/0.89  inst_num_moves_active_passive:          3
% 0.64/0.89  inst_lit_activity:                      0
% 0.64/0.89  inst_lit_activity_moves:                0
% 0.64/0.89  inst_num_tautologies:                   0
% 0.64/0.89  inst_num_prop_implied:                  0
% 0.64/0.89  inst_num_existing_simplified:           0
% 0.64/0.89  inst_num_eq_res_simplified:             0
% 0.64/0.89  inst_num_child_elim:                    0
% 0.64/0.89  inst_num_of_dismatching_blockings:      4
% 0.64/0.89  inst_num_of_non_proper_insts:           28
% 0.64/0.89  inst_num_of_duplicates:                 0
% 0.64/0.89  inst_inst_num_from_inst_to_res:         0
% 0.64/0.89  inst_dismatching_checking_time:         0.
% 0.64/0.89  
% 0.64/0.89  ------ Resolution
% 0.64/0.89  
% 0.64/0.89  res_num_of_clauses:                     0
% 0.64/0.89  res_num_in_passive:                     0
% 0.64/0.89  res_num_in_active:                      0
% 0.64/0.89  res_num_of_loops:                       37
% 0.64/0.89  res_forward_subset_subsumed:            6
% 0.64/0.89  res_backward_subset_subsumed:           0
% 0.64/0.89  res_forward_subsumed:                   0
% 0.64/0.89  res_backward_subsumed:                  0
% 0.64/0.89  res_forward_subsumption_resolution:     0
% 0.64/0.89  res_backward_subsumption_resolution:    0
% 0.64/0.89  res_clause_to_clause_subsumption:       14
% 0.64/0.89  res_orphan_elimination:                 0
% 0.64/0.89  res_tautology_del:                      2
% 0.64/0.89  res_num_eq_res_simplified:              0
% 0.64/0.89  res_num_sel_changes:                    0
% 0.64/0.89  res_moves_from_active_to_pass:          0
% 0.64/0.89  
% 0.64/0.89  ------ Superposition
% 0.64/0.89  
% 0.64/0.89  sup_time_total:                         0.
% 0.64/0.89  sup_time_generating:                    0.
% 0.64/0.89  sup_time_sim_full:                      0.
% 0.64/0.89  sup_time_sim_immed:                     0.
% 0.64/0.89  
% 0.64/0.89  sup_num_of_clauses:                     10
% 0.64/0.89  sup_num_in_active:                      7
% 0.64/0.89  sup_num_in_passive:                     3
% 0.64/0.89  sup_num_of_loops:                       6
% 0.64/0.89  sup_fw_superposition:                   4
% 0.64/0.89  sup_bw_superposition:                   1
% 0.64/0.89  sup_immediate_simplified:               0
% 0.64/0.89  sup_given_eliminated:                   0
% 0.64/0.89  comparisons_done:                       0
% 0.64/0.89  comparisons_avoided:                    0
% 0.64/0.89  
% 0.64/0.89  ------ Simplifications
% 0.64/0.89  
% 0.64/0.89  
% 0.64/0.89  sim_fw_subset_subsumed:                 0
% 0.64/0.89  sim_bw_subset_subsumed:                 0
% 0.64/0.89  sim_fw_subsumed:                        0
% 0.64/0.89  sim_bw_subsumed:                        0
% 0.64/0.89  sim_fw_subsumption_res:                 0
% 0.64/0.89  sim_bw_subsumption_res:                 0
% 0.64/0.89  sim_tautology_del:                      0
% 0.64/0.89  sim_eq_tautology_del:                   0
% 0.64/0.89  sim_eq_res_simp:                        0
% 0.64/0.89  sim_fw_demodulated:                     1
% 0.64/0.89  sim_bw_demodulated:                     0
% 0.64/0.89  sim_light_normalised:                   0
% 0.64/0.89  sim_joinable_taut:                      0
% 0.64/0.89  sim_joinable_simp:                      0
% 0.64/0.89  sim_ac_normalised:                      0
% 0.64/0.89  sim_smt_subsumption:                    0
% 0.64/0.89  
%------------------------------------------------------------------------------
