%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:03 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   48 (  71 expanded)
%              Number of clauses        :   23 (  28 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :   13
%              Number of atoms          :   69 ( 119 expanded)
%              Number of equality atoms :   43 (  58 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f21])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f16,f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

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

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k4_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k4_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).

fof(f22,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_130,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_6,c_2])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_42,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_81,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_8])).

cnf(c_82,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_81])).

cnf(c_5,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_121,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,X0),sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK1)) ),
    inference(superposition,[status(thm)],[c_82,c_5])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_108,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_126,plain,
    ( k4_xboole_0(k2_xboole_0(sK0,X0),sK1) = k4_xboole_0(X0,sK1) ),
    inference(demodulation,[status(thm)],[c_121,c_108])).

cnf(c_195,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),sK1) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_130,c_126])).

cnf(c_203,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,X0),sK1) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_195,c_82])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_40,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_76,plain,
    ( k4_xboole_0(X0,X1) != k1_xboole_0
    | k4_xboole_0(sK0,sK2) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_7])).

cnf(c_77,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_76])).

cnf(c_204,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_203,c_77])).

cnf(c_216,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_204])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:18:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.41/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.06  
% 2.41/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.41/1.06  
% 2.41/1.06  ------  iProver source info
% 2.41/1.06  
% 2.41/1.06  git: date: 2020-06-30 10:37:57 +0100
% 2.41/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.41/1.06  git: non_committed_changes: false
% 2.41/1.06  git: last_make_outside_of_git: false
% 2.41/1.06  
% 2.41/1.06  ------ 
% 2.41/1.06  
% 2.41/1.06  ------ Input Options
% 2.41/1.06  
% 2.41/1.06  --out_options                           all
% 2.41/1.06  --tptp_safe_out                         true
% 2.41/1.06  --problem_path                          ""
% 2.41/1.06  --include_path                          ""
% 2.41/1.06  --clausifier                            res/vclausify_rel
% 2.41/1.06  --clausifier_options                    --mode clausify
% 2.41/1.06  --stdin                                 false
% 2.41/1.06  --stats_out                             all
% 2.41/1.06  
% 2.41/1.06  ------ General Options
% 2.41/1.06  
% 2.41/1.06  --fof                                   false
% 2.41/1.06  --time_out_real                         305.
% 2.41/1.06  --time_out_virtual                      -1.
% 2.41/1.06  --symbol_type_check                     false
% 2.41/1.06  --clausify_out                          false
% 2.41/1.06  --sig_cnt_out                           false
% 2.41/1.06  --trig_cnt_out                          false
% 2.41/1.06  --trig_cnt_out_tolerance                1.
% 2.41/1.06  --trig_cnt_out_sk_spl                   false
% 2.41/1.06  --abstr_cl_out                          false
% 2.41/1.06  
% 2.41/1.06  ------ Global Options
% 2.41/1.06  
% 2.41/1.06  --schedule                              default
% 2.41/1.06  --add_important_lit                     false
% 2.41/1.06  --prop_solver_per_cl                    1000
% 2.41/1.06  --min_unsat_core                        false
% 2.41/1.06  --soft_assumptions                      false
% 2.41/1.06  --soft_lemma_size                       3
% 2.41/1.06  --prop_impl_unit_size                   0
% 2.41/1.06  --prop_impl_unit                        []
% 2.41/1.06  --share_sel_clauses                     true
% 2.41/1.06  --reset_solvers                         false
% 2.41/1.06  --bc_imp_inh                            [conj_cone]
% 2.41/1.06  --conj_cone_tolerance                   3.
% 2.41/1.06  --extra_neg_conj                        none
% 2.41/1.06  --large_theory_mode                     true
% 2.41/1.06  --prolific_symb_bound                   200
% 2.41/1.06  --lt_threshold                          2000
% 2.41/1.06  --clause_weak_htbl                      true
% 2.41/1.06  --gc_record_bc_elim                     false
% 2.41/1.06  
% 2.41/1.06  ------ Preprocessing Options
% 2.41/1.06  
% 2.41/1.06  --preprocessing_flag                    true
% 2.41/1.06  --time_out_prep_mult                    0.1
% 2.41/1.06  --splitting_mode                        input
% 2.41/1.06  --splitting_grd                         true
% 2.41/1.06  --splitting_cvd                         false
% 2.41/1.06  --splitting_cvd_svl                     false
% 2.41/1.06  --splitting_nvd                         32
% 2.41/1.06  --sub_typing                            true
% 2.41/1.06  --prep_gs_sim                           true
% 2.41/1.06  --prep_unflatten                        true
% 2.41/1.06  --prep_res_sim                          true
% 2.41/1.06  --prep_upred                            true
% 2.41/1.06  --prep_sem_filter                       exhaustive
% 2.41/1.06  --prep_sem_filter_out                   false
% 2.41/1.06  --pred_elim                             true
% 2.41/1.06  --res_sim_input                         true
% 2.41/1.06  --eq_ax_congr_red                       true
% 2.41/1.06  --pure_diseq_elim                       true
% 2.41/1.06  --brand_transform                       false
% 2.41/1.06  --non_eq_to_eq                          false
% 2.41/1.06  --prep_def_merge                        true
% 2.41/1.06  --prep_def_merge_prop_impl              false
% 2.41/1.06  --prep_def_merge_mbd                    true
% 2.41/1.06  --prep_def_merge_tr_red                 false
% 2.41/1.06  --prep_def_merge_tr_cl                  false
% 2.41/1.06  --smt_preprocessing                     true
% 2.41/1.06  --smt_ac_axioms                         fast
% 2.41/1.06  --preprocessed_out                      false
% 2.41/1.06  --preprocessed_stats                    false
% 2.41/1.06  
% 2.41/1.06  ------ Abstraction refinement Options
% 2.41/1.06  
% 2.41/1.06  --abstr_ref                             []
% 2.41/1.06  --abstr_ref_prep                        false
% 2.41/1.06  --abstr_ref_until_sat                   false
% 2.41/1.06  --abstr_ref_sig_restrict                funpre
% 2.41/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/1.06  --abstr_ref_under                       []
% 2.41/1.06  
% 2.41/1.06  ------ SAT Options
% 2.41/1.06  
% 2.41/1.06  --sat_mode                              false
% 2.41/1.06  --sat_fm_restart_options                ""
% 2.41/1.06  --sat_gr_def                            false
% 2.41/1.06  --sat_epr_types                         true
% 2.41/1.06  --sat_non_cyclic_types                  false
% 2.41/1.06  --sat_finite_models                     false
% 2.41/1.06  --sat_fm_lemmas                         false
% 2.41/1.06  --sat_fm_prep                           false
% 2.41/1.06  --sat_fm_uc_incr                        true
% 2.41/1.06  --sat_out_model                         small
% 2.41/1.06  --sat_out_clauses                       false
% 2.41/1.06  
% 2.41/1.06  ------ QBF Options
% 2.41/1.06  
% 2.41/1.06  --qbf_mode                              false
% 2.41/1.06  --qbf_elim_univ                         false
% 2.41/1.06  --qbf_dom_inst                          none
% 2.41/1.06  --qbf_dom_pre_inst                      false
% 2.41/1.06  --qbf_sk_in                             false
% 2.41/1.06  --qbf_pred_elim                         true
% 2.41/1.06  --qbf_split                             512
% 2.41/1.06  
% 2.41/1.06  ------ BMC1 Options
% 2.41/1.06  
% 2.41/1.06  --bmc1_incremental                      false
% 2.41/1.06  --bmc1_axioms                           reachable_all
% 2.41/1.06  --bmc1_min_bound                        0
% 2.41/1.06  --bmc1_max_bound                        -1
% 2.41/1.06  --bmc1_max_bound_default                -1
% 2.41/1.06  --bmc1_symbol_reachability              true
% 2.41/1.06  --bmc1_property_lemmas                  false
% 2.41/1.06  --bmc1_k_induction                      false
% 2.41/1.06  --bmc1_non_equiv_states                 false
% 2.41/1.06  --bmc1_deadlock                         false
% 2.41/1.06  --bmc1_ucm                              false
% 2.41/1.06  --bmc1_add_unsat_core                   none
% 2.41/1.06  --bmc1_unsat_core_children              false
% 2.41/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/1.06  --bmc1_out_stat                         full
% 2.41/1.06  --bmc1_ground_init                      false
% 2.41/1.06  --bmc1_pre_inst_next_state              false
% 2.41/1.06  --bmc1_pre_inst_state                   false
% 2.41/1.06  --bmc1_pre_inst_reach_state             false
% 2.41/1.06  --bmc1_out_unsat_core                   false
% 2.41/1.06  --bmc1_aig_witness_out                  false
% 2.41/1.06  --bmc1_verbose                          false
% 2.41/1.06  --bmc1_dump_clauses_tptp                false
% 2.41/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.41/1.06  --bmc1_dump_file                        -
% 2.41/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.41/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.41/1.06  --bmc1_ucm_extend_mode                  1
% 2.41/1.06  --bmc1_ucm_init_mode                    2
% 2.41/1.06  --bmc1_ucm_cone_mode                    none
% 2.41/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.41/1.06  --bmc1_ucm_relax_model                  4
% 2.41/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.41/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/1.06  --bmc1_ucm_layered_model                none
% 2.41/1.06  --bmc1_ucm_max_lemma_size               10
% 2.41/1.06  
% 2.41/1.06  ------ AIG Options
% 2.41/1.06  
% 2.41/1.06  --aig_mode                              false
% 2.41/1.06  
% 2.41/1.06  ------ Instantiation Options
% 2.41/1.06  
% 2.41/1.06  --instantiation_flag                    true
% 2.41/1.06  --inst_sos_flag                         false
% 2.41/1.06  --inst_sos_phase                        true
% 2.41/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/1.06  --inst_lit_sel_side                     num_symb
% 2.41/1.06  --inst_solver_per_active                1400
% 2.41/1.06  --inst_solver_calls_frac                1.
% 2.41/1.06  --inst_passive_queue_type               priority_queues
% 2.41/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/1.06  --inst_passive_queues_freq              [25;2]
% 2.41/1.06  --inst_dismatching                      true
% 2.41/1.06  --inst_eager_unprocessed_to_passive     true
% 2.41/1.06  --inst_prop_sim_given                   true
% 2.41/1.06  --inst_prop_sim_new                     false
% 2.41/1.06  --inst_subs_new                         false
% 2.41/1.06  --inst_eq_res_simp                      false
% 2.41/1.06  --inst_subs_given                       false
% 2.41/1.06  --inst_orphan_elimination               true
% 2.41/1.06  --inst_learning_loop_flag               true
% 2.41/1.06  --inst_learning_start                   3000
% 2.41/1.06  --inst_learning_factor                  2
% 2.41/1.06  --inst_start_prop_sim_after_learn       3
% 2.41/1.06  --inst_sel_renew                        solver
% 2.41/1.06  --inst_lit_activity_flag                true
% 2.41/1.06  --inst_restr_to_given                   false
% 2.41/1.06  --inst_activity_threshold               500
% 2.41/1.06  --inst_out_proof                        true
% 2.41/1.06  
% 2.41/1.06  ------ Resolution Options
% 2.41/1.06  
% 2.41/1.06  --resolution_flag                       true
% 2.41/1.06  --res_lit_sel                           adaptive
% 2.41/1.06  --res_lit_sel_side                      none
% 2.41/1.06  --res_ordering                          kbo
% 2.41/1.06  --res_to_prop_solver                    active
% 2.41/1.06  --res_prop_simpl_new                    false
% 2.41/1.06  --res_prop_simpl_given                  true
% 2.41/1.06  --res_passive_queue_type                priority_queues
% 2.41/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/1.06  --res_passive_queues_freq               [15;5]
% 2.41/1.06  --res_forward_subs                      full
% 2.41/1.06  --res_backward_subs                     full
% 2.41/1.06  --res_forward_subs_resolution           true
% 2.41/1.06  --res_backward_subs_resolution          true
% 2.41/1.06  --res_orphan_elimination                true
% 2.41/1.06  --res_time_limit                        2.
% 2.41/1.06  --res_out_proof                         true
% 2.41/1.06  
% 2.41/1.06  ------ Superposition Options
% 2.41/1.06  
% 2.41/1.06  --superposition_flag                    true
% 2.41/1.06  --sup_passive_queue_type                priority_queues
% 2.41/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.41/1.06  --demod_completeness_check              fast
% 2.41/1.06  --demod_use_ground                      true
% 2.41/1.06  --sup_to_prop_solver                    passive
% 2.41/1.06  --sup_prop_simpl_new                    true
% 2.41/1.06  --sup_prop_simpl_given                  true
% 2.41/1.06  --sup_fun_splitting                     false
% 2.41/1.06  --sup_smt_interval                      50000
% 2.41/1.06  
% 2.41/1.06  ------ Superposition Simplification Setup
% 2.41/1.06  
% 2.41/1.06  --sup_indices_passive                   []
% 2.41/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.06  --sup_full_bw                           [BwDemod]
% 2.41/1.06  --sup_immed_triv                        [TrivRules]
% 2.41/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.06  --sup_immed_bw_main                     []
% 2.41/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.06  
% 2.41/1.06  ------ Combination Options
% 2.41/1.06  
% 2.41/1.06  --comb_res_mult                         3
% 2.41/1.06  --comb_sup_mult                         2
% 2.41/1.06  --comb_inst_mult                        10
% 2.41/1.06  
% 2.41/1.06  ------ Debug Options
% 2.41/1.06  
% 2.41/1.06  --dbg_backtrace                         false
% 2.41/1.06  --dbg_dump_prop_clauses                 false
% 2.41/1.06  --dbg_dump_prop_clauses_file            -
% 2.41/1.06  --dbg_out_stat                          false
% 2.41/1.06  ------ Parsing...
% 2.41/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.41/1.06  
% 2.41/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.41/1.06  
% 2.41/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.41/1.06  
% 2.41/1.06  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.41/1.06  ------ Proving...
% 2.41/1.06  ------ Problem Properties 
% 2.41/1.06  
% 2.41/1.06  
% 2.41/1.06  clauses                                 8
% 2.41/1.06  conjectures                             0
% 2.41/1.06  EPR                                     0
% 2.41/1.06  Horn                                    8
% 2.41/1.06  unary                                   8
% 2.41/1.06  binary                                  0
% 2.41/1.06  lits                                    8
% 2.41/1.06  lits eq                                 8
% 2.41/1.06  fd_pure                                 0
% 2.41/1.06  fd_pseudo                               0
% 2.41/1.06  fd_cond                                 0
% 2.41/1.06  fd_pseudo_cond                          0
% 2.41/1.06  AC symbols                              0
% 2.41/1.06  
% 2.41/1.06  ------ Schedule UEQ
% 2.41/1.06  
% 2.41/1.06  ------ pure equality problem: resolution off 
% 2.41/1.06  
% 2.41/1.06  ------ Option_UEQ Time Limit: Unbounded
% 2.41/1.06  
% 2.41/1.06  
% 2.41/1.06  ------ 
% 2.41/1.06  Current options:
% 2.41/1.06  ------ 
% 2.41/1.06  
% 2.41/1.06  ------ Input Options
% 2.41/1.06  
% 2.41/1.06  --out_options                           all
% 2.41/1.06  --tptp_safe_out                         true
% 2.41/1.06  --problem_path                          ""
% 2.41/1.06  --include_path                          ""
% 2.41/1.06  --clausifier                            res/vclausify_rel
% 2.41/1.06  --clausifier_options                    --mode clausify
% 2.41/1.06  --stdin                                 false
% 2.41/1.06  --stats_out                             all
% 2.41/1.06  
% 2.41/1.06  ------ General Options
% 2.41/1.06  
% 2.41/1.06  --fof                                   false
% 2.41/1.06  --time_out_real                         305.
% 2.41/1.06  --time_out_virtual                      -1.
% 2.41/1.06  --symbol_type_check                     false
% 2.41/1.06  --clausify_out                          false
% 2.41/1.06  --sig_cnt_out                           false
% 2.41/1.06  --trig_cnt_out                          false
% 2.41/1.06  --trig_cnt_out_tolerance                1.
% 2.41/1.06  --trig_cnt_out_sk_spl                   false
% 2.41/1.06  --abstr_cl_out                          false
% 2.41/1.06  
% 2.41/1.06  ------ Global Options
% 2.41/1.06  
% 2.41/1.06  --schedule                              default
% 2.41/1.06  --add_important_lit                     false
% 2.41/1.06  --prop_solver_per_cl                    1000
% 2.41/1.06  --min_unsat_core                        false
% 2.41/1.06  --soft_assumptions                      false
% 2.41/1.06  --soft_lemma_size                       3
% 2.41/1.06  --prop_impl_unit_size                   0
% 2.41/1.06  --prop_impl_unit                        []
% 2.41/1.06  --share_sel_clauses                     true
% 2.41/1.06  --reset_solvers                         false
% 2.41/1.06  --bc_imp_inh                            [conj_cone]
% 2.41/1.06  --conj_cone_tolerance                   3.
% 2.41/1.06  --extra_neg_conj                        none
% 2.41/1.06  --large_theory_mode                     true
% 2.41/1.06  --prolific_symb_bound                   200
% 2.41/1.06  --lt_threshold                          2000
% 2.41/1.06  --clause_weak_htbl                      true
% 2.41/1.06  --gc_record_bc_elim                     false
% 2.41/1.06  
% 2.41/1.06  ------ Preprocessing Options
% 2.41/1.06  
% 2.41/1.06  --preprocessing_flag                    true
% 2.41/1.06  --time_out_prep_mult                    0.1
% 2.41/1.06  --splitting_mode                        input
% 2.41/1.06  --splitting_grd                         true
% 2.41/1.06  --splitting_cvd                         false
% 2.41/1.06  --splitting_cvd_svl                     false
% 2.41/1.06  --splitting_nvd                         32
% 2.41/1.06  --sub_typing                            true
% 2.41/1.06  --prep_gs_sim                           true
% 2.41/1.06  --prep_unflatten                        true
% 2.41/1.06  --prep_res_sim                          true
% 2.41/1.06  --prep_upred                            true
% 2.41/1.06  --prep_sem_filter                       exhaustive
% 2.41/1.06  --prep_sem_filter_out                   false
% 2.41/1.06  --pred_elim                             true
% 2.41/1.06  --res_sim_input                         true
% 2.41/1.06  --eq_ax_congr_red                       true
% 2.41/1.06  --pure_diseq_elim                       true
% 2.41/1.06  --brand_transform                       false
% 2.41/1.06  --non_eq_to_eq                          false
% 2.41/1.06  --prep_def_merge                        true
% 2.41/1.06  --prep_def_merge_prop_impl              false
% 2.41/1.06  --prep_def_merge_mbd                    true
% 2.41/1.06  --prep_def_merge_tr_red                 false
% 2.41/1.06  --prep_def_merge_tr_cl                  false
% 2.41/1.06  --smt_preprocessing                     true
% 2.41/1.06  --smt_ac_axioms                         fast
% 2.41/1.06  --preprocessed_out                      false
% 2.41/1.06  --preprocessed_stats                    false
% 2.41/1.06  
% 2.41/1.06  ------ Abstraction refinement Options
% 2.41/1.06  
% 2.41/1.06  --abstr_ref                             []
% 2.41/1.06  --abstr_ref_prep                        false
% 2.41/1.06  --abstr_ref_until_sat                   false
% 2.41/1.06  --abstr_ref_sig_restrict                funpre
% 2.41/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/1.06  --abstr_ref_under                       []
% 2.41/1.06  
% 2.41/1.06  ------ SAT Options
% 2.41/1.06  
% 2.41/1.06  --sat_mode                              false
% 2.41/1.06  --sat_fm_restart_options                ""
% 2.41/1.06  --sat_gr_def                            false
% 2.41/1.06  --sat_epr_types                         true
% 2.41/1.06  --sat_non_cyclic_types                  false
% 2.41/1.06  --sat_finite_models                     false
% 2.41/1.06  --sat_fm_lemmas                         false
% 2.41/1.06  --sat_fm_prep                           false
% 2.41/1.06  --sat_fm_uc_incr                        true
% 2.41/1.06  --sat_out_model                         small
% 2.41/1.06  --sat_out_clauses                       false
% 2.41/1.06  
% 2.41/1.06  ------ QBF Options
% 2.41/1.06  
% 2.41/1.06  --qbf_mode                              false
% 2.41/1.06  --qbf_elim_univ                         false
% 2.41/1.06  --qbf_dom_inst                          none
% 2.41/1.06  --qbf_dom_pre_inst                      false
% 2.41/1.06  --qbf_sk_in                             false
% 2.41/1.06  --qbf_pred_elim                         true
% 2.41/1.06  --qbf_split                             512
% 2.41/1.06  
% 2.41/1.06  ------ BMC1 Options
% 2.41/1.06  
% 2.41/1.06  --bmc1_incremental                      false
% 2.41/1.06  --bmc1_axioms                           reachable_all
% 2.41/1.06  --bmc1_min_bound                        0
% 2.41/1.06  --bmc1_max_bound                        -1
% 2.41/1.06  --bmc1_max_bound_default                -1
% 2.41/1.06  --bmc1_symbol_reachability              true
% 2.41/1.06  --bmc1_property_lemmas                  false
% 2.41/1.06  --bmc1_k_induction                      false
% 2.41/1.06  --bmc1_non_equiv_states                 false
% 2.41/1.06  --bmc1_deadlock                         false
% 2.41/1.06  --bmc1_ucm                              false
% 2.41/1.06  --bmc1_add_unsat_core                   none
% 2.41/1.06  --bmc1_unsat_core_children              false
% 2.41/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/1.06  --bmc1_out_stat                         full
% 2.41/1.06  --bmc1_ground_init                      false
% 2.41/1.06  --bmc1_pre_inst_next_state              false
% 2.41/1.06  --bmc1_pre_inst_state                   false
% 2.41/1.06  --bmc1_pre_inst_reach_state             false
% 2.41/1.06  --bmc1_out_unsat_core                   false
% 2.41/1.06  --bmc1_aig_witness_out                  false
% 2.41/1.06  --bmc1_verbose                          false
% 2.41/1.06  --bmc1_dump_clauses_tptp                false
% 2.41/1.06  --bmc1_dump_unsat_core_tptp             false
% 2.41/1.06  --bmc1_dump_file                        -
% 2.41/1.06  --bmc1_ucm_expand_uc_limit              128
% 2.41/1.06  --bmc1_ucm_n_expand_iterations          6
% 2.41/1.06  --bmc1_ucm_extend_mode                  1
% 2.41/1.06  --bmc1_ucm_init_mode                    2
% 2.41/1.06  --bmc1_ucm_cone_mode                    none
% 2.41/1.06  --bmc1_ucm_reduced_relation_type        0
% 2.41/1.06  --bmc1_ucm_relax_model                  4
% 2.41/1.06  --bmc1_ucm_full_tr_after_sat            true
% 2.41/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/1.06  --bmc1_ucm_layered_model                none
% 2.41/1.06  --bmc1_ucm_max_lemma_size               10
% 2.41/1.06  
% 2.41/1.06  ------ AIG Options
% 2.41/1.06  
% 2.41/1.06  --aig_mode                              false
% 2.41/1.06  
% 2.41/1.06  ------ Instantiation Options
% 2.41/1.06  
% 2.41/1.06  --instantiation_flag                    false
% 2.41/1.06  --inst_sos_flag                         false
% 2.41/1.06  --inst_sos_phase                        true
% 2.41/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/1.06  --inst_lit_sel_side                     num_symb
% 2.41/1.06  --inst_solver_per_active                1400
% 2.41/1.06  --inst_solver_calls_frac                1.
% 2.41/1.06  --inst_passive_queue_type               priority_queues
% 2.41/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/1.06  --inst_passive_queues_freq              [25;2]
% 2.41/1.06  --inst_dismatching                      true
% 2.41/1.06  --inst_eager_unprocessed_to_passive     true
% 2.41/1.06  --inst_prop_sim_given                   true
% 2.41/1.06  --inst_prop_sim_new                     false
% 2.41/1.06  --inst_subs_new                         false
% 2.41/1.06  --inst_eq_res_simp                      false
% 2.41/1.06  --inst_subs_given                       false
% 2.41/1.06  --inst_orphan_elimination               true
% 2.41/1.06  --inst_learning_loop_flag               true
% 2.41/1.06  --inst_learning_start                   3000
% 2.41/1.06  --inst_learning_factor                  2
% 2.41/1.06  --inst_start_prop_sim_after_learn       3
% 2.41/1.06  --inst_sel_renew                        solver
% 2.41/1.06  --inst_lit_activity_flag                true
% 2.41/1.06  --inst_restr_to_given                   false
% 2.41/1.06  --inst_activity_threshold               500
% 2.41/1.06  --inst_out_proof                        true
% 2.41/1.06  
% 2.41/1.06  ------ Resolution Options
% 2.41/1.06  
% 2.41/1.06  --resolution_flag                       false
% 2.41/1.06  --res_lit_sel                           adaptive
% 2.41/1.06  --res_lit_sel_side                      none
% 2.41/1.06  --res_ordering                          kbo
% 2.41/1.06  --res_to_prop_solver                    active
% 2.41/1.06  --res_prop_simpl_new                    false
% 2.41/1.06  --res_prop_simpl_given                  true
% 2.41/1.06  --res_passive_queue_type                priority_queues
% 2.41/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/1.06  --res_passive_queues_freq               [15;5]
% 2.41/1.06  --res_forward_subs                      full
% 2.41/1.06  --res_backward_subs                     full
% 2.41/1.06  --res_forward_subs_resolution           true
% 2.41/1.06  --res_backward_subs_resolution          true
% 2.41/1.06  --res_orphan_elimination                true
% 2.41/1.06  --res_time_limit                        2.
% 2.41/1.06  --res_out_proof                         true
% 2.41/1.06  
% 2.41/1.06  ------ Superposition Options
% 2.41/1.06  
% 2.41/1.06  --superposition_flag                    true
% 2.41/1.06  --sup_passive_queue_type                priority_queues
% 2.41/1.06  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/1.06  --sup_passive_queues_freq               [8;1;4]
% 2.41/1.06  --demod_completeness_check              fast
% 2.41/1.06  --demod_use_ground                      true
% 2.41/1.06  --sup_to_prop_solver                    active
% 2.41/1.06  --sup_prop_simpl_new                    false
% 2.41/1.06  --sup_prop_simpl_given                  false
% 2.41/1.06  --sup_fun_splitting                     true
% 2.41/1.06  --sup_smt_interval                      10000
% 2.41/1.06  
% 2.41/1.06  ------ Superposition Simplification Setup
% 2.41/1.06  
% 2.41/1.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.41/1.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.41/1.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.06  --sup_full_triv                         [TrivRules]
% 2.41/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.41/1.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.41/1.06  --sup_immed_triv                        [TrivRules]
% 2.41/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.06  --sup_immed_bw_main                     []
% 2.41/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.41/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.06  --sup_input_bw                          [BwDemod;BwSubsumption]
% 2.41/1.06  
% 2.41/1.06  ------ Combination Options
% 2.41/1.06  
% 2.41/1.06  --comb_res_mult                         1
% 2.41/1.06  --comb_sup_mult                         1
% 2.41/1.06  --comb_inst_mult                        1000000
% 2.41/1.06  
% 2.41/1.06  ------ Debug Options
% 2.41/1.06  
% 2.41/1.06  --dbg_backtrace                         false
% 2.41/1.06  --dbg_dump_prop_clauses                 false
% 2.41/1.06  --dbg_dump_prop_clauses_file            -
% 2.41/1.06  --dbg_out_stat                          false
% 2.41/1.06  
% 2.41/1.06  
% 2.41/1.06  
% 2.41/1.06  
% 2.41/1.06  ------ Proving...
% 2.41/1.06  
% 2.41/1.06  
% 2.41/1.06  % SZS status Theorem for theBenchmark.p
% 2.41/1.06  
% 2.41/1.06   Resolution empty clause
% 2.41/1.06  
% 2.41/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 2.41/1.06  
% 2.41/1.06  fof(f6,axiom,(
% 2.41/1.06    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.41/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.06  
% 2.41/1.06  fof(f20,plain,(
% 2.41/1.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.41/1.06    inference(cnf_transformation,[],[f6])).
% 2.41/1.06  
% 2.41/1.06  fof(f7,axiom,(
% 2.41/1.06    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.41/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.06  
% 2.41/1.06  fof(f21,plain,(
% 2.41/1.06    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.41/1.06    inference(cnf_transformation,[],[f7])).
% 2.41/1.06  
% 2.41/1.06  fof(f25,plain,(
% 2.41/1.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.41/1.06    inference(definition_unfolding,[],[f20,f21])).
% 2.41/1.06  
% 2.41/1.06  fof(f3,axiom,(
% 2.41/1.06    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.41/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.06  
% 2.41/1.06  fof(f16,plain,(
% 2.41/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.41/1.06    inference(cnf_transformation,[],[f3])).
% 2.41/1.06  
% 2.41/1.06  fof(f24,plain,(
% 2.41/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 2.41/1.06    inference(definition_unfolding,[],[f16,f21])).
% 2.41/1.06  
% 2.41/1.06  fof(f4,axiom,(
% 2.41/1.06    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 2.41/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.06  
% 2.41/1.06  fof(f11,plain,(
% 2.41/1.06    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 2.41/1.06    inference(nnf_transformation,[],[f4])).
% 2.41/1.06  
% 2.41/1.06  fof(f18,plain,(
% 2.41/1.06    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 2.41/1.06    inference(cnf_transformation,[],[f11])).
% 2.41/1.06  
% 2.41/1.06  fof(f8,conjecture,(
% 2.41/1.06    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 2.41/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.06  
% 2.41/1.06  fof(f9,negated_conjecture,(
% 2.41/1.06    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 2.41/1.06    inference(negated_conjecture,[],[f8])).
% 2.41/1.06  
% 2.41/1.06  fof(f10,plain,(
% 2.41/1.06    ? [X0,X1,X2] : (~r1_tarski(k4_xboole_0(X0,X2),X1) & r1_tarski(X0,X1))),
% 2.41/1.06    inference(ennf_transformation,[],[f9])).
% 2.41/1.06  
% 2.41/1.06  fof(f12,plain,(
% 2.41/1.06    ? [X0,X1,X2] : (~r1_tarski(k4_xboole_0(X0,X2),X1) & r1_tarski(X0,X1)) => (~r1_tarski(k4_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1))),
% 2.41/1.06    introduced(choice_axiom,[])).
% 2.41/1.06  
% 2.41/1.06  fof(f13,plain,(
% 2.41/1.06    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1)),
% 2.41/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).
% 2.41/1.06  
% 2.41/1.06  fof(f22,plain,(
% 2.41/1.06    r1_tarski(sK0,sK1)),
% 2.41/1.06    inference(cnf_transformation,[],[f13])).
% 2.41/1.06  
% 2.41/1.06  fof(f5,axiom,(
% 2.41/1.06    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)),
% 2.41/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.06  
% 2.41/1.06  fof(f19,plain,(
% 2.41/1.06    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 2.41/1.06    inference(cnf_transformation,[],[f5])).
% 2.41/1.06  
% 2.41/1.06  fof(f2,axiom,(
% 2.41/1.06    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.41/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.06  
% 2.41/1.06  fof(f15,plain,(
% 2.41/1.06    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.41/1.06    inference(cnf_transformation,[],[f2])).
% 2.41/1.06  
% 2.41/1.06  fof(f1,axiom,(
% 2.41/1.06    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.41/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.41/1.06  
% 2.41/1.06  fof(f14,plain,(
% 2.41/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.41/1.06    inference(cnf_transformation,[],[f1])).
% 2.41/1.06  
% 2.41/1.06  fof(f17,plain,(
% 2.41/1.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 2.41/1.06    inference(cnf_transformation,[],[f11])).
% 2.41/1.06  
% 2.41/1.06  fof(f23,plain,(
% 2.41/1.06    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 2.41/1.06    inference(cnf_transformation,[],[f13])).
% 2.41/1.06  
% 2.41/1.06  cnf(c_6,plain,
% 2.41/1.06      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 2.41/1.06      inference(cnf_transformation,[],[f25]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_2,plain,
% 2.41/1.06      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 2.41/1.06      inference(cnf_transformation,[],[f24]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_130,plain,
% 2.41/1.06      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 2.41/1.06      inference(superposition,[status(thm)],[c_6,c_2]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_3,plain,
% 2.41/1.06      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.41/1.06      inference(cnf_transformation,[],[f18]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_42,plain,
% 2.41/1.06      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.41/1.06      inference(prop_impl,[status(thm)],[c_3]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_8,negated_conjecture,
% 2.41/1.06      ( r1_tarski(sK0,sK1) ),
% 2.41/1.06      inference(cnf_transformation,[],[f22]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_81,plain,
% 2.41/1.06      ( k4_xboole_0(X0,X1) = k1_xboole_0 | sK1 != X1 | sK0 != X0 ),
% 2.41/1.06      inference(resolution_lifted,[status(thm)],[c_42,c_8]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_82,plain,
% 2.41/1.06      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 2.41/1.06      inference(unflattening,[status(thm)],[c_81]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_5,plain,
% 2.41/1.06      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X2,X1)) = k4_xboole_0(k2_xboole_0(X0,X2),X1) ),
% 2.41/1.06      inference(cnf_transformation,[],[f19]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_121,plain,
% 2.41/1.06      ( k4_xboole_0(k2_xboole_0(sK0,X0),sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK1)) ),
% 2.41/1.06      inference(superposition,[status(thm)],[c_82,c_5]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_1,plain,
% 2.41/1.06      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.41/1.06      inference(cnf_transformation,[],[f15]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_0,plain,
% 2.41/1.06      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 2.41/1.06      inference(cnf_transformation,[],[f14]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_108,plain,
% 2.41/1.06      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 2.41/1.06      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_126,plain,
% 2.41/1.06      ( k4_xboole_0(k2_xboole_0(sK0,X0),sK1) = k4_xboole_0(X0,sK1) ),
% 2.41/1.06      inference(demodulation,[status(thm)],[c_121,c_108]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_195,plain,
% 2.41/1.06      ( k4_xboole_0(k4_xboole_0(sK0,X0),sK1) = k4_xboole_0(sK0,sK1) ),
% 2.41/1.06      inference(superposition,[status(thm)],[c_130,c_126]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_203,plain,
% 2.41/1.06      ( k4_xboole_0(k4_xboole_0(sK0,X0),sK1) = k1_xboole_0 ),
% 2.41/1.06      inference(light_normalisation,[status(thm)],[c_195,c_82]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_4,plain,
% 2.41/1.06      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.41/1.06      inference(cnf_transformation,[],[f17]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_40,plain,
% 2.41/1.06      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.41/1.06      inference(prop_impl,[status(thm)],[c_4]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_7,negated_conjecture,
% 2.41/1.06      ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
% 2.41/1.06      inference(cnf_transformation,[],[f23]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_76,plain,
% 2.41/1.06      ( k4_xboole_0(X0,X1) != k1_xboole_0
% 2.41/1.06      | k4_xboole_0(sK0,sK2) != X0
% 2.41/1.06      | sK1 != X1 ),
% 2.41/1.06      inference(resolution_lifted,[status(thm)],[c_40,c_7]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_77,plain,
% 2.41/1.06      ( k4_xboole_0(k4_xboole_0(sK0,sK2),sK1) != k1_xboole_0 ),
% 2.41/1.06      inference(unflattening,[status(thm)],[c_76]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_204,plain,
% 2.41/1.06      ( k1_xboole_0 != k1_xboole_0 ),
% 2.41/1.06      inference(demodulation,[status(thm)],[c_203,c_77]) ).
% 2.41/1.06  
% 2.41/1.06  cnf(c_216,plain,
% 2.41/1.06      ( $false ),
% 2.41/1.06      inference(equality_resolution_simp,[status(thm)],[c_204]) ).
% 2.41/1.06  
% 2.41/1.06  
% 2.41/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 2.41/1.06  
% 2.41/1.06  ------                               Statistics
% 2.41/1.06  
% 2.41/1.06  ------ General
% 2.41/1.06  
% 2.41/1.06  abstr_ref_over_cycles:                  0
% 2.41/1.06  abstr_ref_under_cycles:                 0
% 2.41/1.06  gc_basic_clause_elim:                   0
% 2.41/1.06  forced_gc_time:                         0
% 2.41/1.06  parsing_time:                           0.02
% 2.41/1.06  unif_index_cands_time:                  0.
% 2.41/1.06  unif_index_add_time:                    0.
% 2.41/1.06  orderings_time:                         0.
% 2.41/1.06  out_proof_time:                         0.009
% 2.41/1.06  total_time:                             0.068
% 2.41/1.06  num_of_symbols:                         38
% 2.41/1.06  num_of_terms:                           360
% 2.41/1.06  
% 2.41/1.06  ------ Preprocessing
% 2.41/1.06  
% 2.41/1.06  num_of_splits:                          0
% 2.41/1.06  num_of_split_atoms:                     0
% 2.41/1.06  num_of_reused_defs:                     0
% 2.41/1.06  num_eq_ax_congr_red:                    0
% 2.41/1.06  num_of_sem_filtered_clauses:            0
% 2.41/1.06  num_of_subtypes:                        0
% 2.41/1.06  monotx_restored_types:                  0
% 2.41/1.06  sat_num_of_epr_types:                   0
% 2.41/1.06  sat_num_of_non_cyclic_types:            0
% 2.41/1.06  sat_guarded_non_collapsed_types:        0
% 2.41/1.06  num_pure_diseq_elim:                    0
% 2.41/1.06  simp_replaced_by:                       0
% 2.41/1.06  res_preprocessed:                       29
% 2.41/1.06  prep_upred:                             0
% 2.41/1.06  prep_unflattend:                        4
% 2.41/1.06  smt_new_axioms:                         0
% 2.41/1.06  pred_elim_cands:                        0
% 2.41/1.06  pred_elim:                              1
% 2.41/1.06  pred_elim_cl:                           1
% 2.41/1.06  pred_elim_cycles:                       2
% 2.41/1.06  merged_defs:                            2
% 2.41/1.06  merged_defs_ncl:                        0
% 2.41/1.06  bin_hyper_res:                          2
% 2.41/1.06  prep_cycles:                            3
% 2.41/1.06  pred_elim_time:                         0.
% 2.41/1.06  splitting_time:                         0.
% 2.41/1.06  sem_filter_time:                        0.
% 2.41/1.06  monotx_time:                            0.
% 2.41/1.06  subtype_inf_time:                       0.
% 2.41/1.06  
% 2.41/1.06  ------ Problem properties
% 2.41/1.06  
% 2.41/1.06  clauses:                                8
% 2.41/1.06  conjectures:                            0
% 2.41/1.06  epr:                                    0
% 2.41/1.06  horn:                                   8
% 2.41/1.06  ground:                                 3
% 2.41/1.06  unary:                                  8
% 2.41/1.06  binary:                                 0
% 2.41/1.06  lits:                                   8
% 2.41/1.06  lits_eq:                                8
% 2.41/1.06  fd_pure:                                0
% 2.41/1.06  fd_pseudo:                              0
% 2.41/1.06  fd_cond:                                0
% 2.41/1.06  fd_pseudo_cond:                         0
% 2.41/1.06  ac_symbols:                             0
% 2.41/1.06  
% 2.41/1.06  ------ Propositional Solver
% 2.41/1.06  
% 2.41/1.06  prop_solver_calls:                      17
% 2.41/1.06  prop_fast_solver_calls:                 78
% 2.41/1.06  smt_solver_calls:                       0
% 2.41/1.06  smt_fast_solver_calls:                  0
% 2.41/1.06  prop_num_of_clauses:                    47
% 2.41/1.06  prop_preprocess_simplified:             400
% 2.41/1.06  prop_fo_subsumed:                       0
% 2.41/1.06  prop_solver_time:                       0.
% 2.41/1.06  smt_solver_time:                        0.
% 2.41/1.06  smt_fast_solver_time:                   0.
% 2.41/1.06  prop_fast_solver_time:                  0.
% 2.41/1.06  prop_unsat_core_time:                   0.
% 2.41/1.06  
% 2.41/1.06  ------ QBF
% 2.41/1.06  
% 2.41/1.06  qbf_q_res:                              0
% 2.41/1.06  qbf_num_tautologies:                    0
% 2.41/1.06  qbf_prep_cycles:                        0
% 2.41/1.06  
% 2.41/1.06  ------ BMC1
% 2.41/1.06  
% 2.41/1.06  bmc1_current_bound:                     -1
% 2.41/1.06  bmc1_last_solved_bound:                 -1
% 2.41/1.06  bmc1_unsat_core_size:                   -1
% 2.41/1.06  bmc1_unsat_core_parents_size:           -1
% 2.41/1.06  bmc1_merge_next_fun:                    0
% 2.41/1.06  bmc1_unsat_core_clauses_time:           0.
% 2.41/1.06  
% 2.41/1.06  ------ Instantiation
% 2.41/1.06  
% 2.41/1.06  inst_num_of_clauses:                    0
% 2.41/1.06  inst_num_in_passive:                    0
% 2.41/1.06  inst_num_in_active:                     0
% 2.41/1.06  inst_num_in_unprocessed:                0
% 2.41/1.06  inst_num_of_loops:                      0
% 2.41/1.06  inst_num_of_learning_restarts:          0
% 2.41/1.06  inst_num_moves_active_passive:          0
% 2.41/1.06  inst_lit_activity:                      0
% 2.41/1.06  inst_lit_activity_moves:                0
% 2.41/1.06  inst_num_tautologies:                   0
% 2.41/1.06  inst_num_prop_implied:                  0
% 2.41/1.06  inst_num_existing_simplified:           0
% 2.41/1.06  inst_num_eq_res_simplified:             0
% 2.41/1.06  inst_num_child_elim:                    0
% 2.41/1.06  inst_num_of_dismatching_blockings:      0
% 2.41/1.06  inst_num_of_non_proper_insts:           0
% 2.41/1.06  inst_num_of_duplicates:                 0
% 2.41/1.06  inst_inst_num_from_inst_to_res:         0
% 2.41/1.06  inst_dismatching_checking_time:         0.
% 2.41/1.06  
% 2.41/1.06  ------ Resolution
% 2.41/1.06  
% 2.41/1.06  res_num_of_clauses:                     0
% 2.41/1.06  res_num_in_passive:                     0
% 2.41/1.06  res_num_in_active:                      0
% 2.41/1.06  res_num_of_loops:                       32
% 2.41/1.06  res_forward_subset_subsumed:            0
% 2.41/1.06  res_backward_subset_subsumed:           0
% 2.41/1.06  res_forward_subsumed:                   0
% 2.41/1.06  res_backward_subsumed:                  0
% 2.41/1.06  res_forward_subsumption_resolution:     0
% 2.41/1.06  res_backward_subsumption_resolution:    0
% 2.41/1.06  res_clause_to_clause_subsumption:       95
% 2.41/1.06  res_orphan_elimination:                 0
% 2.41/1.06  res_tautology_del:                      5
% 2.41/1.06  res_num_eq_res_simplified:              1
% 2.41/1.06  res_num_sel_changes:                    0
% 2.41/1.06  res_moves_from_active_to_pass:          0
% 2.41/1.06  
% 2.41/1.06  ------ Superposition
% 2.41/1.06  
% 2.41/1.06  sup_time_total:                         0.
% 2.41/1.06  sup_time_generating:                    0.
% 2.41/1.06  sup_time_sim_full:                      0.
% 2.41/1.06  sup_time_sim_immed:                     0.
% 2.41/1.06  
% 2.41/1.06  sup_num_of_clauses:                     30
% 2.41/1.06  sup_num_in_active:                      13
% 2.41/1.06  sup_num_in_passive:                     17
% 2.41/1.06  sup_num_of_loops:                       17
% 2.41/1.06  sup_fw_superposition:                   30
% 2.41/1.06  sup_bw_superposition:                   43
% 2.41/1.06  sup_immediate_simplified:               32
% 2.41/1.06  sup_given_eliminated:                   1
% 2.41/1.06  comparisons_done:                       0
% 2.41/1.06  comparisons_avoided:                    0
% 2.41/1.06  
% 2.41/1.06  ------ Simplifications
% 2.41/1.06  
% 2.41/1.06  
% 2.41/1.06  sim_fw_subset_subsumed:                 0
% 2.41/1.06  sim_bw_subset_subsumed:                 0
% 2.41/1.06  sim_fw_subsumed:                        10
% 2.41/1.06  sim_bw_subsumed:                        3
% 2.41/1.06  sim_fw_subsumption_res:                 0
% 2.41/1.06  sim_bw_subsumption_res:                 0
% 2.41/1.06  sim_tautology_del:                      0
% 2.41/1.06  sim_eq_tautology_del:                   4
% 2.41/1.06  sim_eq_res_simp:                        0
% 2.41/1.06  sim_fw_demodulated:                     20
% 2.41/1.06  sim_bw_demodulated:                     2
% 2.41/1.06  sim_light_normalised:                   7
% 2.41/1.06  sim_joinable_taut:                      0
% 2.41/1.06  sim_joinable_simp:                      0
% 2.41/1.06  sim_ac_normalised:                      0
% 2.41/1.06  sim_smt_subsumption:                    0
% 2.41/1.06  
%------------------------------------------------------------------------------
