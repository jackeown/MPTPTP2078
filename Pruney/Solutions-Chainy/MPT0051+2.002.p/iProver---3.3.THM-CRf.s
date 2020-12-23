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
% DateTime   : Thu Dec  3 11:22:41 EST 2020

% Result     : Theorem 15.77s
% Output     : CNFRefutation 15.77s
% Verified   : 
% Statistics : Number of formulae       :   45 (  65 expanded)
%              Number of clauses        :   24 (  30 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :   11
%              Number of atoms          :   63 (  95 expanded)
%              Number of equality atoms :   31 (  44 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
       => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
   => ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
      & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f20,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f21,plain,(
    ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_156,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_160,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f16])).

cnf(c_159,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_985,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_160,c_159])).

cnf(c_49276,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(X0,sK2)) = k2_xboole_0(X0,sK2) ),
    inference(superposition,[status(thm)],[c_156,c_985])).

cnf(c_5,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_158,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_655,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_158,c_159])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_481,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_4,c_3])).

cnf(c_16094,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_655,c_481])).

cnf(c_16191,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(demodulation,[status(thm)],[c_16094,c_3])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_16851,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
    inference(superposition,[status(thm)],[c_16191,c_0])).

cnf(c_52376,plain,
    ( k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) = k2_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_49276,c_16851])).

cnf(c_286,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_158])).

cnf(c_52723,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_52376,c_286])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_9,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_52723,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:01:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.77/2.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.77/2.48  
% 15.77/2.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.77/2.48  
% 15.77/2.48  ------  iProver source info
% 15.77/2.48  
% 15.77/2.48  git: date: 2020-06-30 10:37:57 +0100
% 15.77/2.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.77/2.48  git: non_committed_changes: false
% 15.77/2.48  git: last_make_outside_of_git: false
% 15.77/2.48  
% 15.77/2.48  ------ 
% 15.77/2.48  
% 15.77/2.48  ------ Input Options
% 15.77/2.48  
% 15.77/2.48  --out_options                           all
% 15.77/2.48  --tptp_safe_out                         true
% 15.77/2.48  --problem_path                          ""
% 15.77/2.48  --include_path                          ""
% 15.77/2.48  --clausifier                            res/vclausify_rel
% 15.77/2.48  --clausifier_options                    ""
% 15.77/2.48  --stdin                                 false
% 15.77/2.48  --stats_out                             all
% 15.77/2.48  
% 15.77/2.48  ------ General Options
% 15.77/2.48  
% 15.77/2.48  --fof                                   false
% 15.77/2.48  --time_out_real                         305.
% 15.77/2.48  --time_out_virtual                      -1.
% 15.77/2.48  --symbol_type_check                     false
% 15.77/2.48  --clausify_out                          false
% 15.77/2.48  --sig_cnt_out                           false
% 15.77/2.48  --trig_cnt_out                          false
% 15.77/2.48  --trig_cnt_out_tolerance                1.
% 15.77/2.48  --trig_cnt_out_sk_spl                   false
% 15.77/2.48  --abstr_cl_out                          false
% 15.77/2.48  
% 15.77/2.48  ------ Global Options
% 15.77/2.48  
% 15.77/2.48  --schedule                              default
% 15.77/2.48  --add_important_lit                     false
% 15.77/2.48  --prop_solver_per_cl                    1000
% 15.77/2.48  --min_unsat_core                        false
% 15.77/2.48  --soft_assumptions                      false
% 15.77/2.48  --soft_lemma_size                       3
% 15.77/2.48  --prop_impl_unit_size                   0
% 15.77/2.48  --prop_impl_unit                        []
% 15.77/2.48  --share_sel_clauses                     true
% 15.77/2.48  --reset_solvers                         false
% 15.77/2.48  --bc_imp_inh                            [conj_cone]
% 15.77/2.48  --conj_cone_tolerance                   3.
% 15.77/2.48  --extra_neg_conj                        none
% 15.77/2.48  --large_theory_mode                     true
% 15.77/2.48  --prolific_symb_bound                   200
% 15.77/2.48  --lt_threshold                          2000
% 15.77/2.48  --clause_weak_htbl                      true
% 15.77/2.48  --gc_record_bc_elim                     false
% 15.77/2.48  
% 15.77/2.48  ------ Preprocessing Options
% 15.77/2.48  
% 15.77/2.48  --preprocessing_flag                    true
% 15.77/2.48  --time_out_prep_mult                    0.1
% 15.77/2.48  --splitting_mode                        input
% 15.77/2.48  --splitting_grd                         true
% 15.77/2.48  --splitting_cvd                         false
% 15.77/2.48  --splitting_cvd_svl                     false
% 15.77/2.48  --splitting_nvd                         32
% 15.77/2.48  --sub_typing                            true
% 15.77/2.48  --prep_gs_sim                           true
% 15.77/2.48  --prep_unflatten                        true
% 15.77/2.48  --prep_res_sim                          true
% 15.77/2.48  --prep_upred                            true
% 15.77/2.48  --prep_sem_filter                       exhaustive
% 15.77/2.48  --prep_sem_filter_out                   false
% 15.77/2.48  --pred_elim                             true
% 15.77/2.48  --res_sim_input                         true
% 15.77/2.48  --eq_ax_congr_red                       true
% 15.77/2.48  --pure_diseq_elim                       true
% 15.77/2.48  --brand_transform                       false
% 15.77/2.48  --non_eq_to_eq                          false
% 15.77/2.48  --prep_def_merge                        true
% 15.77/2.48  --prep_def_merge_prop_impl              false
% 15.77/2.48  --prep_def_merge_mbd                    true
% 15.77/2.48  --prep_def_merge_tr_red                 false
% 15.77/2.48  --prep_def_merge_tr_cl                  false
% 15.77/2.48  --smt_preprocessing                     true
% 15.77/2.48  --smt_ac_axioms                         fast
% 15.77/2.48  --preprocessed_out                      false
% 15.77/2.48  --preprocessed_stats                    false
% 15.77/2.48  
% 15.77/2.48  ------ Abstraction refinement Options
% 15.77/2.48  
% 15.77/2.48  --abstr_ref                             []
% 15.77/2.48  --abstr_ref_prep                        false
% 15.77/2.48  --abstr_ref_until_sat                   false
% 15.77/2.48  --abstr_ref_sig_restrict                funpre
% 15.77/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.77/2.48  --abstr_ref_under                       []
% 15.77/2.48  
% 15.77/2.48  ------ SAT Options
% 15.77/2.48  
% 15.77/2.48  --sat_mode                              false
% 15.77/2.48  --sat_fm_restart_options                ""
% 15.77/2.48  --sat_gr_def                            false
% 15.77/2.48  --sat_epr_types                         true
% 15.77/2.48  --sat_non_cyclic_types                  false
% 15.77/2.48  --sat_finite_models                     false
% 15.77/2.48  --sat_fm_lemmas                         false
% 15.77/2.48  --sat_fm_prep                           false
% 15.77/2.48  --sat_fm_uc_incr                        true
% 15.77/2.48  --sat_out_model                         small
% 15.77/2.48  --sat_out_clauses                       false
% 15.77/2.48  
% 15.77/2.48  ------ QBF Options
% 15.77/2.48  
% 15.77/2.48  --qbf_mode                              false
% 15.77/2.48  --qbf_elim_univ                         false
% 15.77/2.48  --qbf_dom_inst                          none
% 15.77/2.48  --qbf_dom_pre_inst                      false
% 15.77/2.48  --qbf_sk_in                             false
% 15.77/2.48  --qbf_pred_elim                         true
% 15.77/2.48  --qbf_split                             512
% 15.77/2.48  
% 15.77/2.48  ------ BMC1 Options
% 15.77/2.48  
% 15.77/2.48  --bmc1_incremental                      false
% 15.77/2.48  --bmc1_axioms                           reachable_all
% 15.77/2.48  --bmc1_min_bound                        0
% 15.77/2.48  --bmc1_max_bound                        -1
% 15.77/2.48  --bmc1_max_bound_default                -1
% 15.77/2.48  --bmc1_symbol_reachability              true
% 15.77/2.48  --bmc1_property_lemmas                  false
% 15.77/2.48  --bmc1_k_induction                      false
% 15.77/2.48  --bmc1_non_equiv_states                 false
% 15.77/2.48  --bmc1_deadlock                         false
% 15.77/2.48  --bmc1_ucm                              false
% 15.77/2.48  --bmc1_add_unsat_core                   none
% 15.77/2.48  --bmc1_unsat_core_children              false
% 15.77/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.77/2.48  --bmc1_out_stat                         full
% 15.77/2.48  --bmc1_ground_init                      false
% 15.77/2.48  --bmc1_pre_inst_next_state              false
% 15.77/2.48  --bmc1_pre_inst_state                   false
% 15.77/2.48  --bmc1_pre_inst_reach_state             false
% 15.77/2.48  --bmc1_out_unsat_core                   false
% 15.77/2.48  --bmc1_aig_witness_out                  false
% 15.77/2.48  --bmc1_verbose                          false
% 15.77/2.48  --bmc1_dump_clauses_tptp                false
% 15.77/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.77/2.48  --bmc1_dump_file                        -
% 15.77/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.77/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.77/2.48  --bmc1_ucm_extend_mode                  1
% 15.77/2.48  --bmc1_ucm_init_mode                    2
% 15.77/2.48  --bmc1_ucm_cone_mode                    none
% 15.77/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.77/2.48  --bmc1_ucm_relax_model                  4
% 15.77/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.77/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.77/2.48  --bmc1_ucm_layered_model                none
% 15.77/2.48  --bmc1_ucm_max_lemma_size               10
% 15.77/2.48  
% 15.77/2.48  ------ AIG Options
% 15.77/2.48  
% 15.77/2.48  --aig_mode                              false
% 15.77/2.48  
% 15.77/2.48  ------ Instantiation Options
% 15.77/2.48  
% 15.77/2.48  --instantiation_flag                    true
% 15.77/2.48  --inst_sos_flag                         true
% 15.77/2.48  --inst_sos_phase                        true
% 15.77/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.77/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.77/2.48  --inst_lit_sel_side                     num_symb
% 15.77/2.48  --inst_solver_per_active                1400
% 15.77/2.48  --inst_solver_calls_frac                1.
% 15.77/2.48  --inst_passive_queue_type               priority_queues
% 15.77/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.77/2.48  --inst_passive_queues_freq              [25;2]
% 15.77/2.48  --inst_dismatching                      true
% 15.77/2.48  --inst_eager_unprocessed_to_passive     true
% 15.77/2.48  --inst_prop_sim_given                   true
% 15.77/2.48  --inst_prop_sim_new                     false
% 15.77/2.48  --inst_subs_new                         false
% 15.77/2.48  --inst_eq_res_simp                      false
% 15.77/2.48  --inst_subs_given                       false
% 15.77/2.48  --inst_orphan_elimination               true
% 15.77/2.48  --inst_learning_loop_flag               true
% 15.77/2.48  --inst_learning_start                   3000
% 15.77/2.48  --inst_learning_factor                  2
% 15.77/2.48  --inst_start_prop_sim_after_learn       3
% 15.77/2.48  --inst_sel_renew                        solver
% 15.77/2.48  --inst_lit_activity_flag                true
% 15.77/2.48  --inst_restr_to_given                   false
% 15.77/2.48  --inst_activity_threshold               500
% 15.77/2.48  --inst_out_proof                        true
% 15.77/2.48  
% 15.77/2.48  ------ Resolution Options
% 15.77/2.48  
% 15.77/2.48  --resolution_flag                       true
% 15.77/2.48  --res_lit_sel                           adaptive
% 15.77/2.48  --res_lit_sel_side                      none
% 15.77/2.48  --res_ordering                          kbo
% 15.77/2.48  --res_to_prop_solver                    active
% 15.77/2.48  --res_prop_simpl_new                    false
% 15.77/2.48  --res_prop_simpl_given                  true
% 15.77/2.48  --res_passive_queue_type                priority_queues
% 15.77/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.77/2.48  --res_passive_queues_freq               [15;5]
% 15.77/2.48  --res_forward_subs                      full
% 15.77/2.48  --res_backward_subs                     full
% 15.77/2.48  --res_forward_subs_resolution           true
% 15.77/2.48  --res_backward_subs_resolution          true
% 15.77/2.48  --res_orphan_elimination                true
% 15.77/2.48  --res_time_limit                        2.
% 15.77/2.48  --res_out_proof                         true
% 15.77/2.48  
% 15.77/2.48  ------ Superposition Options
% 15.77/2.48  
% 15.77/2.48  --superposition_flag                    true
% 15.77/2.48  --sup_passive_queue_type                priority_queues
% 15.77/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.77/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.77/2.48  --demod_completeness_check              fast
% 15.77/2.48  --demod_use_ground                      true
% 15.77/2.48  --sup_to_prop_solver                    passive
% 15.77/2.48  --sup_prop_simpl_new                    true
% 15.77/2.48  --sup_prop_simpl_given                  true
% 15.77/2.48  --sup_fun_splitting                     true
% 15.77/2.48  --sup_smt_interval                      50000
% 15.77/2.48  
% 15.77/2.48  ------ Superposition Simplification Setup
% 15.77/2.48  
% 15.77/2.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.77/2.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.77/2.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.77/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.77/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.77/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.77/2.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.77/2.48  --sup_immed_triv                        [TrivRules]
% 15.77/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.77/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.77/2.48  --sup_immed_bw_main                     []
% 15.77/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.77/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.77/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.77/2.48  --sup_input_bw                          []
% 15.77/2.48  
% 15.77/2.48  ------ Combination Options
% 15.77/2.48  
% 15.77/2.48  --comb_res_mult                         3
% 15.77/2.48  --comb_sup_mult                         2
% 15.77/2.48  --comb_inst_mult                        10
% 15.77/2.48  
% 15.77/2.48  ------ Debug Options
% 15.77/2.48  
% 15.77/2.48  --dbg_backtrace                         false
% 15.77/2.48  --dbg_dump_prop_clauses                 false
% 15.77/2.48  --dbg_dump_prop_clauses_file            -
% 15.77/2.48  --dbg_out_stat                          false
% 15.77/2.48  ------ Parsing...
% 15.77/2.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.77/2.48  
% 15.77/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.77/2.48  
% 15.77/2.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.77/2.48  
% 15.77/2.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.77/2.48  ------ Proving...
% 15.77/2.48  ------ Problem Properties 
% 15.77/2.48  
% 15.77/2.48  
% 15.77/2.48  clauses                                 8
% 15.77/2.48  conjectures                             2
% 15.77/2.48  EPR                                     0
% 15.77/2.48  Horn                                    8
% 15.77/2.48  unary                                   6
% 15.77/2.48  binary                                  2
% 15.77/2.48  lits                                    10
% 15.77/2.48  lits eq                                 4
% 15.77/2.48  fd_pure                                 0
% 15.77/2.48  fd_pseudo                               0
% 15.77/2.48  fd_cond                                 0
% 15.77/2.48  fd_pseudo_cond                          0
% 15.77/2.48  AC symbols                              0
% 15.77/2.48  
% 15.77/2.48  ------ Schedule dynamic 5 is on 
% 15.77/2.48  
% 15.77/2.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.77/2.48  
% 15.77/2.48  
% 15.77/2.48  ------ 
% 15.77/2.48  Current options:
% 15.77/2.48  ------ 
% 15.77/2.48  
% 15.77/2.48  ------ Input Options
% 15.77/2.48  
% 15.77/2.48  --out_options                           all
% 15.77/2.48  --tptp_safe_out                         true
% 15.77/2.48  --problem_path                          ""
% 15.77/2.48  --include_path                          ""
% 15.77/2.48  --clausifier                            res/vclausify_rel
% 15.77/2.48  --clausifier_options                    ""
% 15.77/2.48  --stdin                                 false
% 15.77/2.48  --stats_out                             all
% 15.77/2.48  
% 15.77/2.48  ------ General Options
% 15.77/2.48  
% 15.77/2.48  --fof                                   false
% 15.77/2.48  --time_out_real                         305.
% 15.77/2.48  --time_out_virtual                      -1.
% 15.77/2.48  --symbol_type_check                     false
% 15.77/2.48  --clausify_out                          false
% 15.77/2.48  --sig_cnt_out                           false
% 15.77/2.48  --trig_cnt_out                          false
% 15.77/2.48  --trig_cnt_out_tolerance                1.
% 15.77/2.48  --trig_cnt_out_sk_spl                   false
% 15.77/2.48  --abstr_cl_out                          false
% 15.77/2.48  
% 15.77/2.48  ------ Global Options
% 15.77/2.48  
% 15.77/2.48  --schedule                              default
% 15.77/2.48  --add_important_lit                     false
% 15.77/2.48  --prop_solver_per_cl                    1000
% 15.77/2.48  --min_unsat_core                        false
% 15.77/2.48  --soft_assumptions                      false
% 15.77/2.48  --soft_lemma_size                       3
% 15.77/2.48  --prop_impl_unit_size                   0
% 15.77/2.48  --prop_impl_unit                        []
% 15.77/2.48  --share_sel_clauses                     true
% 15.77/2.48  --reset_solvers                         false
% 15.77/2.48  --bc_imp_inh                            [conj_cone]
% 15.77/2.48  --conj_cone_tolerance                   3.
% 15.77/2.48  --extra_neg_conj                        none
% 15.77/2.48  --large_theory_mode                     true
% 15.77/2.48  --prolific_symb_bound                   200
% 15.77/2.48  --lt_threshold                          2000
% 15.77/2.48  --clause_weak_htbl                      true
% 15.77/2.48  --gc_record_bc_elim                     false
% 15.77/2.48  
% 15.77/2.48  ------ Preprocessing Options
% 15.77/2.48  
% 15.77/2.48  --preprocessing_flag                    true
% 15.77/2.48  --time_out_prep_mult                    0.1
% 15.77/2.48  --splitting_mode                        input
% 15.77/2.48  --splitting_grd                         true
% 15.77/2.48  --splitting_cvd                         false
% 15.77/2.48  --splitting_cvd_svl                     false
% 15.77/2.48  --splitting_nvd                         32
% 15.77/2.48  --sub_typing                            true
% 15.77/2.48  --prep_gs_sim                           true
% 15.77/2.48  --prep_unflatten                        true
% 15.77/2.48  --prep_res_sim                          true
% 15.77/2.48  --prep_upred                            true
% 15.77/2.48  --prep_sem_filter                       exhaustive
% 15.77/2.48  --prep_sem_filter_out                   false
% 15.77/2.48  --pred_elim                             true
% 15.77/2.48  --res_sim_input                         true
% 15.77/2.48  --eq_ax_congr_red                       true
% 15.77/2.48  --pure_diseq_elim                       true
% 15.77/2.48  --brand_transform                       false
% 15.77/2.48  --non_eq_to_eq                          false
% 15.77/2.48  --prep_def_merge                        true
% 15.77/2.48  --prep_def_merge_prop_impl              false
% 15.77/2.48  --prep_def_merge_mbd                    true
% 15.77/2.48  --prep_def_merge_tr_red                 false
% 15.77/2.48  --prep_def_merge_tr_cl                  false
% 15.77/2.48  --smt_preprocessing                     true
% 15.77/2.48  --smt_ac_axioms                         fast
% 15.77/2.48  --preprocessed_out                      false
% 15.77/2.48  --preprocessed_stats                    false
% 15.77/2.48  
% 15.77/2.48  ------ Abstraction refinement Options
% 15.77/2.48  
% 15.77/2.48  --abstr_ref                             []
% 15.77/2.48  --abstr_ref_prep                        false
% 15.77/2.48  --abstr_ref_until_sat                   false
% 15.77/2.48  --abstr_ref_sig_restrict                funpre
% 15.77/2.48  --abstr_ref_af_restrict_to_split_sk     false
% 15.77/2.48  --abstr_ref_under                       []
% 15.77/2.48  
% 15.77/2.48  ------ SAT Options
% 15.77/2.48  
% 15.77/2.48  --sat_mode                              false
% 15.77/2.48  --sat_fm_restart_options                ""
% 15.77/2.48  --sat_gr_def                            false
% 15.77/2.48  --sat_epr_types                         true
% 15.77/2.48  --sat_non_cyclic_types                  false
% 15.77/2.48  --sat_finite_models                     false
% 15.77/2.48  --sat_fm_lemmas                         false
% 15.77/2.48  --sat_fm_prep                           false
% 15.77/2.48  --sat_fm_uc_incr                        true
% 15.77/2.48  --sat_out_model                         small
% 15.77/2.48  --sat_out_clauses                       false
% 15.77/2.48  
% 15.77/2.48  ------ QBF Options
% 15.77/2.48  
% 15.77/2.48  --qbf_mode                              false
% 15.77/2.48  --qbf_elim_univ                         false
% 15.77/2.48  --qbf_dom_inst                          none
% 15.77/2.48  --qbf_dom_pre_inst                      false
% 15.77/2.48  --qbf_sk_in                             false
% 15.77/2.48  --qbf_pred_elim                         true
% 15.77/2.48  --qbf_split                             512
% 15.77/2.48  
% 15.77/2.48  ------ BMC1 Options
% 15.77/2.48  
% 15.77/2.48  --bmc1_incremental                      false
% 15.77/2.48  --bmc1_axioms                           reachable_all
% 15.77/2.48  --bmc1_min_bound                        0
% 15.77/2.48  --bmc1_max_bound                        -1
% 15.77/2.48  --bmc1_max_bound_default                -1
% 15.77/2.48  --bmc1_symbol_reachability              true
% 15.77/2.48  --bmc1_property_lemmas                  false
% 15.77/2.48  --bmc1_k_induction                      false
% 15.77/2.48  --bmc1_non_equiv_states                 false
% 15.77/2.48  --bmc1_deadlock                         false
% 15.77/2.48  --bmc1_ucm                              false
% 15.77/2.48  --bmc1_add_unsat_core                   none
% 15.77/2.48  --bmc1_unsat_core_children              false
% 15.77/2.48  --bmc1_unsat_core_extrapolate_axioms    false
% 15.77/2.48  --bmc1_out_stat                         full
% 15.77/2.48  --bmc1_ground_init                      false
% 15.77/2.48  --bmc1_pre_inst_next_state              false
% 15.77/2.48  --bmc1_pre_inst_state                   false
% 15.77/2.48  --bmc1_pre_inst_reach_state             false
% 15.77/2.48  --bmc1_out_unsat_core                   false
% 15.77/2.48  --bmc1_aig_witness_out                  false
% 15.77/2.48  --bmc1_verbose                          false
% 15.77/2.48  --bmc1_dump_clauses_tptp                false
% 15.77/2.48  --bmc1_dump_unsat_core_tptp             false
% 15.77/2.48  --bmc1_dump_file                        -
% 15.77/2.48  --bmc1_ucm_expand_uc_limit              128
% 15.77/2.48  --bmc1_ucm_n_expand_iterations          6
% 15.77/2.48  --bmc1_ucm_extend_mode                  1
% 15.77/2.48  --bmc1_ucm_init_mode                    2
% 15.77/2.48  --bmc1_ucm_cone_mode                    none
% 15.77/2.48  --bmc1_ucm_reduced_relation_type        0
% 15.77/2.48  --bmc1_ucm_relax_model                  4
% 15.77/2.48  --bmc1_ucm_full_tr_after_sat            true
% 15.77/2.48  --bmc1_ucm_expand_neg_assumptions       false
% 15.77/2.48  --bmc1_ucm_layered_model                none
% 15.77/2.48  --bmc1_ucm_max_lemma_size               10
% 15.77/2.48  
% 15.77/2.48  ------ AIG Options
% 15.77/2.48  
% 15.77/2.48  --aig_mode                              false
% 15.77/2.48  
% 15.77/2.48  ------ Instantiation Options
% 15.77/2.48  
% 15.77/2.48  --instantiation_flag                    true
% 15.77/2.48  --inst_sos_flag                         true
% 15.77/2.48  --inst_sos_phase                        true
% 15.77/2.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.77/2.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.77/2.48  --inst_lit_sel_side                     none
% 15.77/2.48  --inst_solver_per_active                1400
% 15.77/2.48  --inst_solver_calls_frac                1.
% 15.77/2.48  --inst_passive_queue_type               priority_queues
% 15.77/2.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.77/2.48  --inst_passive_queues_freq              [25;2]
% 15.77/2.48  --inst_dismatching                      true
% 15.77/2.48  --inst_eager_unprocessed_to_passive     true
% 15.77/2.48  --inst_prop_sim_given                   true
% 15.77/2.48  --inst_prop_sim_new                     false
% 15.77/2.48  --inst_subs_new                         false
% 15.77/2.48  --inst_eq_res_simp                      false
% 15.77/2.48  --inst_subs_given                       false
% 15.77/2.48  --inst_orphan_elimination               true
% 15.77/2.48  --inst_learning_loop_flag               true
% 15.77/2.48  --inst_learning_start                   3000
% 15.77/2.48  --inst_learning_factor                  2
% 15.77/2.48  --inst_start_prop_sim_after_learn       3
% 15.77/2.48  --inst_sel_renew                        solver
% 15.77/2.48  --inst_lit_activity_flag                true
% 15.77/2.48  --inst_restr_to_given                   false
% 15.77/2.48  --inst_activity_threshold               500
% 15.77/2.48  --inst_out_proof                        true
% 15.77/2.48  
% 15.77/2.48  ------ Resolution Options
% 15.77/2.48  
% 15.77/2.48  --resolution_flag                       false
% 15.77/2.48  --res_lit_sel                           adaptive
% 15.77/2.48  --res_lit_sel_side                      none
% 15.77/2.48  --res_ordering                          kbo
% 15.77/2.48  --res_to_prop_solver                    active
% 15.77/2.48  --res_prop_simpl_new                    false
% 15.77/2.48  --res_prop_simpl_given                  true
% 15.77/2.48  --res_passive_queue_type                priority_queues
% 15.77/2.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.77/2.48  --res_passive_queues_freq               [15;5]
% 15.77/2.48  --res_forward_subs                      full
% 15.77/2.48  --res_backward_subs                     full
% 15.77/2.48  --res_forward_subs_resolution           true
% 15.77/2.48  --res_backward_subs_resolution          true
% 15.77/2.48  --res_orphan_elimination                true
% 15.77/2.48  --res_time_limit                        2.
% 15.77/2.48  --res_out_proof                         true
% 15.77/2.48  
% 15.77/2.48  ------ Superposition Options
% 15.77/2.48  
% 15.77/2.48  --superposition_flag                    true
% 15.77/2.48  --sup_passive_queue_type                priority_queues
% 15.77/2.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.77/2.48  --sup_passive_queues_freq               [8;1;4]
% 15.77/2.48  --demod_completeness_check              fast
% 15.77/2.48  --demod_use_ground                      true
% 15.77/2.48  --sup_to_prop_solver                    passive
% 15.77/2.48  --sup_prop_simpl_new                    true
% 15.77/2.48  --sup_prop_simpl_given                  true
% 15.77/2.48  --sup_fun_splitting                     true
% 15.77/2.48  --sup_smt_interval                      50000
% 15.77/2.48  
% 15.77/2.48  ------ Superposition Simplification Setup
% 15.77/2.48  
% 15.77/2.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.77/2.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.77/2.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.77/2.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.77/2.48  --sup_full_triv                         [TrivRules;PropSubs]
% 15.77/2.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.77/2.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.77/2.48  --sup_immed_triv                        [TrivRules]
% 15.77/2.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.77/2.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.77/2.48  --sup_immed_bw_main                     []
% 15.77/2.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.77/2.48  --sup_input_triv                        [Unflattening;TrivRules]
% 15.77/2.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.77/2.48  --sup_input_bw                          []
% 15.77/2.48  
% 15.77/2.48  ------ Combination Options
% 15.77/2.48  
% 15.77/2.48  --comb_res_mult                         3
% 15.77/2.48  --comb_sup_mult                         2
% 15.77/2.48  --comb_inst_mult                        10
% 15.77/2.48  
% 15.77/2.48  ------ Debug Options
% 15.77/2.48  
% 15.77/2.48  --dbg_backtrace                         false
% 15.77/2.48  --dbg_dump_prop_clauses                 false
% 15.77/2.48  --dbg_dump_prop_clauses_file            -
% 15.77/2.48  --dbg_out_stat                          false
% 15.77/2.48  
% 15.77/2.48  
% 15.77/2.48  
% 15.77/2.48  
% 15.77/2.48  ------ Proving...
% 15.77/2.48  
% 15.77/2.48  
% 15.77/2.48  % SZS status Theorem for theBenchmark.p
% 15.77/2.48  
% 15.77/2.48  % SZS output start CNFRefutation for theBenchmark.p
% 15.77/2.48  
% 15.77/2.48  fof(f7,conjecture,(
% 15.77/2.48    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 15.77/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.77/2.48  
% 15.77/2.48  fof(f8,negated_conjecture,(
% 15.77/2.48    ~! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 15.77/2.48    inference(negated_conjecture,[],[f7])).
% 15.77/2.48  
% 15.77/2.48  fof(f11,plain,(
% 15.77/2.48    ? [X0,X1,X2] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) & r1_tarski(k4_xboole_0(X0,X1),X2))),
% 15.77/2.48    inference(ennf_transformation,[],[f8])).
% 15.77/2.48  
% 15.77/2.48  fof(f12,plain,(
% 15.77/2.48    ? [X0,X1,X2] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) & r1_tarski(k4_xboole_0(X0,X1),X2)) => (~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) & r1_tarski(k4_xboole_0(sK0,sK1),sK2))),
% 15.77/2.48    introduced(choice_axiom,[])).
% 15.77/2.48  
% 15.77/2.48  fof(f13,plain,(
% 15.77/2.48    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) & r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 15.77/2.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 15.77/2.48  
% 15.77/2.48  fof(f20,plain,(
% 15.77/2.48    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 15.77/2.48    inference(cnf_transformation,[],[f13])).
% 15.77/2.48  
% 15.77/2.48  fof(f2,axiom,(
% 15.77/2.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 15.77/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.77/2.48  
% 15.77/2.48  fof(f9,plain,(
% 15.77/2.48    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 15.77/2.48    inference(ennf_transformation,[],[f2])).
% 15.77/2.48  
% 15.77/2.48  fof(f15,plain,(
% 15.77/2.48    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 15.77/2.48    inference(cnf_transformation,[],[f9])).
% 15.77/2.48  
% 15.77/2.48  fof(f3,axiom,(
% 15.77/2.48    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 15.77/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.77/2.48  
% 15.77/2.48  fof(f10,plain,(
% 15.77/2.48    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 15.77/2.48    inference(ennf_transformation,[],[f3])).
% 15.77/2.48  
% 15.77/2.48  fof(f16,plain,(
% 15.77/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 15.77/2.48    inference(cnf_transformation,[],[f10])).
% 15.77/2.48  
% 15.77/2.48  fof(f6,axiom,(
% 15.77/2.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 15.77/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.77/2.48  
% 15.77/2.48  fof(f19,plain,(
% 15.77/2.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 15.77/2.48    inference(cnf_transformation,[],[f6])).
% 15.77/2.48  
% 15.77/2.48  fof(f5,axiom,(
% 15.77/2.48    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 15.77/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.77/2.48  
% 15.77/2.48  fof(f18,plain,(
% 15.77/2.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 15.77/2.48    inference(cnf_transformation,[],[f5])).
% 15.77/2.48  
% 15.77/2.48  fof(f4,axiom,(
% 15.77/2.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 15.77/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.77/2.48  
% 15.77/2.48  fof(f17,plain,(
% 15.77/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 15.77/2.48    inference(cnf_transformation,[],[f4])).
% 15.77/2.48  
% 15.77/2.48  fof(f1,axiom,(
% 15.77/2.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.77/2.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.77/2.48  
% 15.77/2.48  fof(f14,plain,(
% 15.77/2.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.77/2.48    inference(cnf_transformation,[],[f1])).
% 15.77/2.48  
% 15.77/2.48  fof(f21,plain,(
% 15.77/2.48    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 15.77/2.48    inference(cnf_transformation,[],[f13])).
% 15.77/2.48  
% 15.77/2.48  cnf(c_7,negated_conjecture,
% 15.77/2.48      ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
% 15.77/2.48      inference(cnf_transformation,[],[f20]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_156,plain,
% 15.77/2.48      ( r1_tarski(k4_xboole_0(sK0,sK1),sK2) = iProver_top ),
% 15.77/2.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_1,plain,
% 15.77/2.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 15.77/2.48      inference(cnf_transformation,[],[f15]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_160,plain,
% 15.77/2.48      ( r1_tarski(X0,X1) != iProver_top
% 15.77/2.48      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 15.77/2.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_2,plain,
% 15.77/2.48      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 15.77/2.48      inference(cnf_transformation,[],[f16]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_159,plain,
% 15.77/2.48      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 15.77/2.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_985,plain,
% 15.77/2.48      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,X2)
% 15.77/2.48      | r1_tarski(X0,X2) != iProver_top ),
% 15.77/2.48      inference(superposition,[status(thm)],[c_160,c_159]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_49276,plain,
% 15.77/2.48      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(X0,sK2)) = k2_xboole_0(X0,sK2) ),
% 15.77/2.48      inference(superposition,[status(thm)],[c_156,c_985]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_5,plain,
% 15.77/2.48      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 15.77/2.48      inference(cnf_transformation,[],[f19]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_158,plain,
% 15.77/2.48      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 15.77/2.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_655,plain,
% 15.77/2.48      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 15.77/2.48      inference(superposition,[status(thm)],[c_158,c_159]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_4,plain,
% 15.77/2.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 15.77/2.48      inference(cnf_transformation,[],[f18]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_3,plain,
% 15.77/2.48      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 15.77/2.48      inference(cnf_transformation,[],[f17]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_481,plain,
% 15.77/2.48      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 15.77/2.48      inference(superposition,[status(thm)],[c_4,c_3]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_16094,plain,
% 15.77/2.48      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,k2_xboole_0(X0,X1))) = k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) ),
% 15.77/2.48      inference(superposition,[status(thm)],[c_655,c_481]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_16191,plain,
% 15.77/2.48      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
% 15.77/2.48      inference(demodulation,[status(thm)],[c_16094,c_3]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_0,plain,
% 15.77/2.48      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 15.77/2.48      inference(cnf_transformation,[],[f14]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_16851,plain,
% 15.77/2.48      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X1,X2),X0) ),
% 15.77/2.48      inference(superposition,[status(thm)],[c_16191,c_0]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_52376,plain,
% 15.77/2.48      ( k2_xboole_0(k2_xboole_0(sK1,sK2),sK0) = k2_xboole_0(sK1,sK2) ),
% 15.77/2.48      inference(superposition,[status(thm)],[c_49276,c_16851]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_286,plain,
% 15.77/2.48      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 15.77/2.48      inference(superposition,[status(thm)],[c_0,c_158]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_52723,plain,
% 15.77/2.48      ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) = iProver_top ),
% 15.77/2.48      inference(superposition,[status(thm)],[c_52376,c_286]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_6,negated_conjecture,
% 15.77/2.48      ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
% 15.77/2.48      inference(cnf_transformation,[],[f21]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(c_9,plain,
% 15.77/2.48      ( r1_tarski(sK0,k2_xboole_0(sK1,sK2)) != iProver_top ),
% 15.77/2.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.77/2.48  
% 15.77/2.48  cnf(contradiction,plain,
% 15.77/2.48      ( $false ),
% 15.77/2.48      inference(minisat,[status(thm)],[c_52723,c_9]) ).
% 15.77/2.48  
% 15.77/2.48  
% 15.77/2.48  % SZS output end CNFRefutation for theBenchmark.p
% 15.77/2.48  
% 15.77/2.48  ------                               Statistics
% 15.77/2.48  
% 15.77/2.48  ------ General
% 15.77/2.48  
% 15.77/2.48  abstr_ref_over_cycles:                  0
% 15.77/2.48  abstr_ref_under_cycles:                 0
% 15.77/2.48  gc_basic_clause_elim:                   0
% 15.77/2.48  forced_gc_time:                         0
% 15.77/2.48  parsing_time:                           0.013
% 15.77/2.48  unif_index_cands_time:                  0.
% 15.77/2.48  unif_index_add_time:                    0.
% 15.77/2.48  orderings_time:                         0.
% 15.77/2.48  out_proof_time:                         0.008
% 15.77/2.48  total_time:                             1.799
% 15.77/2.48  num_of_symbols:                         37
% 15.77/2.48  num_of_terms:                           83064
% 15.77/2.48  
% 15.77/2.48  ------ Preprocessing
% 15.77/2.48  
% 15.77/2.48  num_of_splits:                          0
% 15.77/2.48  num_of_split_atoms:                     0
% 15.77/2.48  num_of_reused_defs:                     0
% 15.77/2.48  num_eq_ax_congr_red:                    0
% 15.77/2.48  num_of_sem_filtered_clauses:            1
% 15.77/2.48  num_of_subtypes:                        1
% 15.77/2.48  monotx_restored_types:                  0
% 15.77/2.48  sat_num_of_epr_types:                   0
% 15.77/2.48  sat_num_of_non_cyclic_types:            0
% 15.77/2.48  sat_guarded_non_collapsed_types:        1
% 15.77/2.48  num_pure_diseq_elim:                    0
% 15.77/2.48  simp_replaced_by:                       0
% 15.77/2.48  res_preprocessed:                       35
% 15.77/2.48  prep_upred:                             0
% 15.77/2.48  prep_unflattend:                        0
% 15.77/2.48  smt_new_axioms:                         0
% 15.77/2.48  pred_elim_cands:                        1
% 15.77/2.48  pred_elim:                              0
% 15.77/2.48  pred_elim_cl:                           0
% 15.77/2.48  pred_elim_cycles:                       1
% 15.77/2.48  merged_defs:                            0
% 15.77/2.48  merged_defs_ncl:                        0
% 15.77/2.48  bin_hyper_res:                          0
% 15.77/2.48  prep_cycles:                            3
% 15.77/2.48  pred_elim_time:                         0.
% 15.77/2.48  splitting_time:                         0.
% 15.77/2.48  sem_filter_time:                        0.
% 15.77/2.48  monotx_time:                            0.
% 15.77/2.48  subtype_inf_time:                       0.
% 15.77/2.48  
% 15.77/2.48  ------ Problem properties
% 15.77/2.48  
% 15.77/2.48  clauses:                                8
% 15.77/2.48  conjectures:                            2
% 15.77/2.48  epr:                                    0
% 15.77/2.48  horn:                                   8
% 15.77/2.48  ground:                                 2
% 15.77/2.48  unary:                                  6
% 15.77/2.48  binary:                                 2
% 15.77/2.48  lits:                                   10
% 15.77/2.48  lits_eq:                                4
% 15.77/2.48  fd_pure:                                0
% 15.77/2.48  fd_pseudo:                              0
% 15.77/2.48  fd_cond:                                0
% 15.77/2.48  fd_pseudo_cond:                         0
% 15.77/2.48  ac_symbols:                             0
% 15.77/2.48  
% 15.77/2.48  ------ Propositional Solver
% 15.77/2.48  
% 15.77/2.48  prop_solver_calls:                      33
% 15.77/2.48  prop_fast_solver_calls:                 390
% 15.77/2.48  smt_solver_calls:                       0
% 15.77/2.48  smt_fast_solver_calls:                  0
% 15.77/2.48  prop_num_of_clauses:                    18871
% 15.77/2.48  prop_preprocess_simplified:             16653
% 15.77/2.48  prop_fo_subsumed:                       0
% 15.77/2.48  prop_solver_time:                       0.
% 15.77/2.48  smt_solver_time:                        0.
% 15.77/2.48  smt_fast_solver_time:                   0.
% 15.77/2.48  prop_fast_solver_time:                  0.
% 15.77/2.48  prop_unsat_core_time:                   0.001
% 15.77/2.48  
% 15.77/2.48  ------ QBF
% 15.77/2.48  
% 15.77/2.48  qbf_q_res:                              0
% 15.77/2.48  qbf_num_tautologies:                    0
% 15.77/2.48  qbf_prep_cycles:                        0
% 15.77/2.48  
% 15.77/2.48  ------ BMC1
% 15.77/2.48  
% 15.77/2.48  bmc1_current_bound:                     -1
% 15.77/2.48  bmc1_last_solved_bound:                 -1
% 15.77/2.48  bmc1_unsat_core_size:                   -1
% 15.77/2.48  bmc1_unsat_core_parents_size:           -1
% 15.77/2.48  bmc1_merge_next_fun:                    0
% 15.77/2.48  bmc1_unsat_core_clauses_time:           0.
% 15.77/2.48  
% 15.77/2.48  ------ Instantiation
% 15.77/2.48  
% 15.77/2.48  inst_num_of_clauses:                    3311
% 15.77/2.48  inst_num_in_passive:                    2055
% 15.77/2.48  inst_num_in_active:                     1230
% 15.77/2.48  inst_num_in_unprocessed:                26
% 15.77/2.48  inst_num_of_loops:                      1290
% 15.77/2.48  inst_num_of_learning_restarts:          0
% 15.77/2.48  inst_num_moves_active_passive:          53
% 15.77/2.48  inst_lit_activity:                      0
% 15.77/2.48  inst_lit_activity_moves:                0
% 15.77/2.48  inst_num_tautologies:                   0
% 15.77/2.48  inst_num_prop_implied:                  0
% 15.77/2.48  inst_num_existing_simplified:           0
% 15.77/2.48  inst_num_eq_res_simplified:             0
% 15.77/2.48  inst_num_child_elim:                    0
% 15.77/2.48  inst_num_of_dismatching_blockings:      1436
% 15.77/2.48  inst_num_of_non_proper_insts:           3851
% 15.77/2.48  inst_num_of_duplicates:                 0
% 15.77/2.48  inst_inst_num_from_inst_to_res:         0
% 15.77/2.48  inst_dismatching_checking_time:         0.
% 15.77/2.48  
% 15.77/2.48  ------ Resolution
% 15.77/2.48  
% 15.77/2.48  res_num_of_clauses:                     0
% 15.77/2.48  res_num_in_passive:                     0
% 15.77/2.48  res_num_in_active:                      0
% 15.77/2.48  res_num_of_loops:                       38
% 15.77/2.48  res_forward_subset_subsumed:            936
% 15.77/2.48  res_backward_subset_subsumed:           10
% 15.77/2.48  res_forward_subsumed:                   0
% 15.77/2.48  res_backward_subsumed:                  0
% 15.77/2.48  res_forward_subsumption_resolution:     0
% 15.77/2.48  res_backward_subsumption_resolution:    0
% 15.77/2.48  res_clause_to_clause_subsumption:       110261
% 15.77/2.48  res_orphan_elimination:                 0
% 15.77/2.48  res_tautology_del:                      223
% 15.77/2.48  res_num_eq_res_simplified:              0
% 15.77/2.48  res_num_sel_changes:                    0
% 15.77/2.48  res_moves_from_active_to_pass:          0
% 15.77/2.48  
% 15.77/2.48  ------ Superposition
% 15.77/2.48  
% 15.77/2.48  sup_time_total:                         0.
% 15.77/2.48  sup_time_generating:                    0.
% 15.77/2.48  sup_time_sim_full:                      0.
% 15.77/2.48  sup_time_sim_immed:                     0.
% 15.77/2.48  
% 15.77/2.48  sup_num_of_clauses:                     4662
% 15.77/2.48  sup_num_in_active:                      222
% 15.77/2.48  sup_num_in_passive:                     4440
% 15.77/2.48  sup_num_of_loops:                       257
% 15.77/2.48  sup_fw_superposition:                   8904
% 15.77/2.48  sup_bw_superposition:                   6648
% 15.77/2.48  sup_immediate_simplified:               9215
% 15.77/2.48  sup_given_eliminated:                   1
% 15.77/2.48  comparisons_done:                       0
% 15.77/2.48  comparisons_avoided:                    0
% 15.77/2.48  
% 15.77/2.48  ------ Simplifications
% 15.77/2.48  
% 15.77/2.48  
% 15.77/2.48  sim_fw_subset_subsumed:                 0
% 15.77/2.48  sim_bw_subset_subsumed:                 0
% 15.77/2.48  sim_fw_subsumed:                        979
% 15.77/2.48  sim_bw_subsumed:                        35
% 15.77/2.48  sim_fw_subsumption_res:                 0
% 15.77/2.48  sim_bw_subsumption_res:                 0
% 15.77/2.48  sim_tautology_del:                      59
% 15.77/2.48  sim_eq_tautology_del:                   1054
% 15.77/2.48  sim_eq_res_simp:                        0
% 15.77/2.48  sim_fw_demodulated:                     9574
% 15.77/2.48  sim_bw_demodulated:                     222
% 15.77/2.48  sim_light_normalised:                   4338
% 15.77/2.48  sim_joinable_taut:                      0
% 15.77/2.48  sim_joinable_simp:                      0
% 15.77/2.48  sim_ac_normalised:                      0
% 15.77/2.48  sim_smt_subsumption:                    0
% 15.77/2.48  
%------------------------------------------------------------------------------
