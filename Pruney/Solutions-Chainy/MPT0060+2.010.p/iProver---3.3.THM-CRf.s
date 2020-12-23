%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:00 EST 2020

% Result     : Theorem 11.55s
% Output     : CNFRefutation 11.55s
% Verified   : 
% Statistics : Number of formulae       :   43 (  50 expanded)
%              Number of clauses        :   19 (  20 expanded)
%              Number of leaves         :   10 (  13 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 (  66 expanded)
%              Number of equality atoms :   42 (  49 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f24,f23,f23])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f9,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f9])).

fof(f12,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f10])).

fof(f14,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f25,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
    inference(definition_unfolding,[],[f25,f23])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_52,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_115,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X3
    | k4_xboole_0(X3,X1) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_52,c_4])).

cnf(c_116,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_115])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_507,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),X2) ),
    inference(superposition,[status(thm)],[c_116,c_7])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_97,plain,
    ( X0 != X1
    | k2_xboole_0(X2,X1) = X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_98,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_97])).

cnf(c_555,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_507,c_6,c_98])).

cnf(c_8,negated_conjecture,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_152,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))))) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_8,c_6])).

cnf(c_49722,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(demodulation,[status(thm)],[c_555,c_152])).

cnf(c_127,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_167,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_127])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_49722,c_167])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:03:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.55/2.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.55/2.05  
% 11.55/2.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.55/2.05  
% 11.55/2.05  ------  iProver source info
% 11.55/2.05  
% 11.55/2.05  git: date: 2020-06-30 10:37:57 +0100
% 11.55/2.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.55/2.05  git: non_committed_changes: false
% 11.55/2.05  git: last_make_outside_of_git: false
% 11.55/2.05  
% 11.55/2.05  ------ 
% 11.55/2.05  
% 11.55/2.05  ------ Input Options
% 11.55/2.05  
% 11.55/2.05  --out_options                           all
% 11.55/2.05  --tptp_safe_out                         true
% 11.55/2.05  --problem_path                          ""
% 11.55/2.05  --include_path                          ""
% 11.55/2.05  --clausifier                            res/vclausify_rel
% 11.55/2.05  --clausifier_options                    --mode clausify
% 11.55/2.05  --stdin                                 false
% 11.55/2.05  --stats_out                             all
% 11.55/2.05  
% 11.55/2.05  ------ General Options
% 11.55/2.05  
% 11.55/2.05  --fof                                   false
% 11.55/2.05  --time_out_real                         305.
% 11.55/2.05  --time_out_virtual                      -1.
% 11.55/2.05  --symbol_type_check                     false
% 11.55/2.05  --clausify_out                          false
% 11.55/2.05  --sig_cnt_out                           false
% 11.55/2.05  --trig_cnt_out                          false
% 11.55/2.05  --trig_cnt_out_tolerance                1.
% 11.55/2.05  --trig_cnt_out_sk_spl                   false
% 11.55/2.05  --abstr_cl_out                          false
% 11.55/2.05  
% 11.55/2.05  ------ Global Options
% 11.55/2.05  
% 11.55/2.05  --schedule                              default
% 11.55/2.05  --add_important_lit                     false
% 11.55/2.05  --prop_solver_per_cl                    1000
% 11.55/2.05  --min_unsat_core                        false
% 11.55/2.05  --soft_assumptions                      false
% 11.55/2.05  --soft_lemma_size                       3
% 11.55/2.05  --prop_impl_unit_size                   0
% 11.55/2.05  --prop_impl_unit                        []
% 11.55/2.05  --share_sel_clauses                     true
% 11.55/2.05  --reset_solvers                         false
% 11.55/2.05  --bc_imp_inh                            [conj_cone]
% 11.55/2.05  --conj_cone_tolerance                   3.
% 11.55/2.05  --extra_neg_conj                        none
% 11.55/2.05  --large_theory_mode                     true
% 11.55/2.05  --prolific_symb_bound                   200
% 11.55/2.05  --lt_threshold                          2000
% 11.55/2.05  --clause_weak_htbl                      true
% 11.55/2.05  --gc_record_bc_elim                     false
% 11.55/2.05  
% 11.55/2.05  ------ Preprocessing Options
% 11.55/2.05  
% 11.55/2.05  --preprocessing_flag                    true
% 11.55/2.05  --time_out_prep_mult                    0.1
% 11.55/2.05  --splitting_mode                        input
% 11.55/2.05  --splitting_grd                         true
% 11.55/2.05  --splitting_cvd                         false
% 11.55/2.05  --splitting_cvd_svl                     false
% 11.55/2.05  --splitting_nvd                         32
% 11.55/2.05  --sub_typing                            true
% 11.55/2.05  --prep_gs_sim                           true
% 11.55/2.05  --prep_unflatten                        true
% 11.55/2.05  --prep_res_sim                          true
% 11.55/2.05  --prep_upred                            true
% 11.55/2.05  --prep_sem_filter                       exhaustive
% 11.55/2.05  --prep_sem_filter_out                   false
% 11.55/2.05  --pred_elim                             true
% 11.55/2.05  --res_sim_input                         true
% 11.55/2.05  --eq_ax_congr_red                       true
% 11.55/2.05  --pure_diseq_elim                       true
% 11.55/2.05  --brand_transform                       false
% 11.55/2.05  --non_eq_to_eq                          false
% 11.55/2.05  --prep_def_merge                        true
% 11.55/2.05  --prep_def_merge_prop_impl              false
% 11.55/2.05  --prep_def_merge_mbd                    true
% 11.55/2.05  --prep_def_merge_tr_red                 false
% 11.55/2.05  --prep_def_merge_tr_cl                  false
% 11.55/2.05  --smt_preprocessing                     true
% 11.55/2.05  --smt_ac_axioms                         fast
% 11.55/2.05  --preprocessed_out                      false
% 11.55/2.05  --preprocessed_stats                    false
% 11.55/2.05  
% 11.55/2.05  ------ Abstraction refinement Options
% 11.55/2.05  
% 11.55/2.05  --abstr_ref                             []
% 11.55/2.05  --abstr_ref_prep                        false
% 11.55/2.05  --abstr_ref_until_sat                   false
% 11.55/2.05  --abstr_ref_sig_restrict                funpre
% 11.55/2.05  --abstr_ref_af_restrict_to_split_sk     false
% 11.55/2.05  --abstr_ref_under                       []
% 11.55/2.05  
% 11.55/2.05  ------ SAT Options
% 11.55/2.05  
% 11.55/2.05  --sat_mode                              false
% 11.55/2.05  --sat_fm_restart_options                ""
% 11.55/2.05  --sat_gr_def                            false
% 11.55/2.05  --sat_epr_types                         true
% 11.55/2.05  --sat_non_cyclic_types                  false
% 11.55/2.05  --sat_finite_models                     false
% 11.55/2.05  --sat_fm_lemmas                         false
% 11.55/2.05  --sat_fm_prep                           false
% 11.55/2.05  --sat_fm_uc_incr                        true
% 11.55/2.05  --sat_out_model                         small
% 11.55/2.05  --sat_out_clauses                       false
% 11.55/2.05  
% 11.55/2.05  ------ QBF Options
% 11.55/2.05  
% 11.55/2.05  --qbf_mode                              false
% 11.55/2.05  --qbf_elim_univ                         false
% 11.55/2.05  --qbf_dom_inst                          none
% 11.55/2.05  --qbf_dom_pre_inst                      false
% 11.55/2.05  --qbf_sk_in                             false
% 11.55/2.05  --qbf_pred_elim                         true
% 11.55/2.05  --qbf_split                             512
% 11.55/2.05  
% 11.55/2.05  ------ BMC1 Options
% 11.55/2.05  
% 11.55/2.05  --bmc1_incremental                      false
% 11.55/2.05  --bmc1_axioms                           reachable_all
% 11.55/2.05  --bmc1_min_bound                        0
% 11.55/2.05  --bmc1_max_bound                        -1
% 11.55/2.05  --bmc1_max_bound_default                -1
% 11.55/2.05  --bmc1_symbol_reachability              true
% 11.55/2.05  --bmc1_property_lemmas                  false
% 11.55/2.05  --bmc1_k_induction                      false
% 11.55/2.05  --bmc1_non_equiv_states                 false
% 11.55/2.05  --bmc1_deadlock                         false
% 11.55/2.05  --bmc1_ucm                              false
% 11.55/2.05  --bmc1_add_unsat_core                   none
% 11.55/2.05  --bmc1_unsat_core_children              false
% 11.55/2.05  --bmc1_unsat_core_extrapolate_axioms    false
% 11.55/2.05  --bmc1_out_stat                         full
% 11.55/2.05  --bmc1_ground_init                      false
% 11.55/2.05  --bmc1_pre_inst_next_state              false
% 11.55/2.05  --bmc1_pre_inst_state                   false
% 11.55/2.05  --bmc1_pre_inst_reach_state             false
% 11.55/2.05  --bmc1_out_unsat_core                   false
% 11.55/2.05  --bmc1_aig_witness_out                  false
% 11.55/2.05  --bmc1_verbose                          false
% 11.55/2.05  --bmc1_dump_clauses_tptp                false
% 11.55/2.05  --bmc1_dump_unsat_core_tptp             false
% 11.55/2.05  --bmc1_dump_file                        -
% 11.55/2.05  --bmc1_ucm_expand_uc_limit              128
% 11.55/2.05  --bmc1_ucm_n_expand_iterations          6
% 11.55/2.05  --bmc1_ucm_extend_mode                  1
% 11.55/2.05  --bmc1_ucm_init_mode                    2
% 11.55/2.05  --bmc1_ucm_cone_mode                    none
% 11.55/2.05  --bmc1_ucm_reduced_relation_type        0
% 11.55/2.05  --bmc1_ucm_relax_model                  4
% 11.55/2.05  --bmc1_ucm_full_tr_after_sat            true
% 11.55/2.05  --bmc1_ucm_expand_neg_assumptions       false
% 11.55/2.05  --bmc1_ucm_layered_model                none
% 11.55/2.05  --bmc1_ucm_max_lemma_size               10
% 11.55/2.05  
% 11.55/2.05  ------ AIG Options
% 11.55/2.05  
% 11.55/2.05  --aig_mode                              false
% 11.55/2.05  
% 11.55/2.05  ------ Instantiation Options
% 11.55/2.05  
% 11.55/2.05  --instantiation_flag                    true
% 11.55/2.05  --inst_sos_flag                         false
% 11.55/2.05  --inst_sos_phase                        true
% 11.55/2.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.55/2.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.55/2.05  --inst_lit_sel_side                     num_symb
% 11.55/2.05  --inst_solver_per_active                1400
% 11.55/2.05  --inst_solver_calls_frac                1.
% 11.55/2.05  --inst_passive_queue_type               priority_queues
% 11.55/2.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.55/2.05  --inst_passive_queues_freq              [25;2]
% 11.55/2.05  --inst_dismatching                      true
% 11.55/2.05  --inst_eager_unprocessed_to_passive     true
% 11.55/2.05  --inst_prop_sim_given                   true
% 11.55/2.05  --inst_prop_sim_new                     false
% 11.55/2.05  --inst_subs_new                         false
% 11.55/2.05  --inst_eq_res_simp                      false
% 11.55/2.05  --inst_subs_given                       false
% 11.55/2.05  --inst_orphan_elimination               true
% 11.55/2.05  --inst_learning_loop_flag               true
% 11.55/2.05  --inst_learning_start                   3000
% 11.55/2.05  --inst_learning_factor                  2
% 11.55/2.05  --inst_start_prop_sim_after_learn       3
% 11.55/2.05  --inst_sel_renew                        solver
% 11.55/2.05  --inst_lit_activity_flag                true
% 11.55/2.05  --inst_restr_to_given                   false
% 11.55/2.05  --inst_activity_threshold               500
% 11.55/2.05  --inst_out_proof                        true
% 11.55/2.05  
% 11.55/2.05  ------ Resolution Options
% 11.55/2.05  
% 11.55/2.05  --resolution_flag                       true
% 11.55/2.05  --res_lit_sel                           adaptive
% 11.55/2.05  --res_lit_sel_side                      none
% 11.55/2.05  --res_ordering                          kbo
% 11.55/2.05  --res_to_prop_solver                    active
% 11.55/2.05  --res_prop_simpl_new                    false
% 11.55/2.05  --res_prop_simpl_given                  true
% 11.55/2.05  --res_passive_queue_type                priority_queues
% 11.55/2.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.55/2.05  --res_passive_queues_freq               [15;5]
% 11.55/2.05  --res_forward_subs                      full
% 11.55/2.05  --res_backward_subs                     full
% 11.55/2.05  --res_forward_subs_resolution           true
% 11.55/2.05  --res_backward_subs_resolution          true
% 11.55/2.05  --res_orphan_elimination                true
% 11.55/2.05  --res_time_limit                        2.
% 11.55/2.05  --res_out_proof                         true
% 11.55/2.05  
% 11.55/2.05  ------ Superposition Options
% 11.55/2.05  
% 11.55/2.05  --superposition_flag                    true
% 11.55/2.05  --sup_passive_queue_type                priority_queues
% 11.55/2.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.55/2.05  --sup_passive_queues_freq               [8;1;4]
% 11.55/2.05  --demod_completeness_check              fast
% 11.55/2.05  --demod_use_ground                      true
% 11.55/2.05  --sup_to_prop_solver                    passive
% 11.55/2.05  --sup_prop_simpl_new                    true
% 11.55/2.05  --sup_prop_simpl_given                  true
% 11.55/2.05  --sup_fun_splitting                     false
% 11.55/2.05  --sup_smt_interval                      50000
% 11.55/2.05  
% 11.55/2.05  ------ Superposition Simplification Setup
% 11.55/2.05  
% 11.55/2.05  --sup_indices_passive                   []
% 11.55/2.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.55/2.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.55/2.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.55/2.05  --sup_full_triv                         [TrivRules;PropSubs]
% 11.55/2.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.55/2.05  --sup_full_bw                           [BwDemod]
% 11.55/2.05  --sup_immed_triv                        [TrivRules]
% 11.55/2.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.55/2.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.55/2.05  --sup_immed_bw_main                     []
% 11.55/2.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.55/2.05  --sup_input_triv                        [Unflattening;TrivRules]
% 11.55/2.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.55/2.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.55/2.05  
% 11.55/2.05  ------ Combination Options
% 11.55/2.05  
% 11.55/2.05  --comb_res_mult                         3
% 11.55/2.05  --comb_sup_mult                         2
% 11.55/2.05  --comb_inst_mult                        10
% 11.55/2.05  
% 11.55/2.05  ------ Debug Options
% 11.55/2.05  
% 11.55/2.05  --dbg_backtrace                         false
% 11.55/2.05  --dbg_dump_prop_clauses                 false
% 11.55/2.05  --dbg_dump_prop_clauses_file            -
% 11.55/2.05  --dbg_out_stat                          false
% 11.55/2.05  ------ Parsing...
% 11.55/2.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.55/2.05  
% 11.55/2.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 11.55/2.05  
% 11.55/2.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.55/2.05  
% 11.55/2.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 11.55/2.05  ------ Proving...
% 11.55/2.05  ------ Problem Properties 
% 11.55/2.05  
% 11.55/2.05  
% 11.55/2.05  clauses                                 9
% 11.55/2.05  conjectures                             1
% 11.55/2.05  EPR                                     0
% 11.55/2.05  Horn                                    9
% 11.55/2.05  unary                                   8
% 11.55/2.05  binary                                  1
% 11.55/2.05  lits                                    10
% 11.55/2.05  lits eq                                 10
% 11.55/2.05  fd_pure                                 0
% 11.55/2.05  fd_pseudo                               0
% 11.55/2.05  fd_cond                                 0
% 11.55/2.05  fd_pseudo_cond                          0
% 11.55/2.05  AC symbols                              0
% 11.55/2.05  
% 11.55/2.05  ------ Schedule dynamic 5 is on 
% 11.55/2.05  
% 11.55/2.05  ------ pure equality problem: resolution off 
% 11.55/2.05  
% 11.55/2.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.55/2.05  
% 11.55/2.05  
% 11.55/2.05  ------ 
% 11.55/2.05  Current options:
% 11.55/2.05  ------ 
% 11.55/2.05  
% 11.55/2.05  ------ Input Options
% 11.55/2.05  
% 11.55/2.05  --out_options                           all
% 11.55/2.05  --tptp_safe_out                         true
% 11.55/2.05  --problem_path                          ""
% 11.55/2.05  --include_path                          ""
% 11.55/2.05  --clausifier                            res/vclausify_rel
% 11.55/2.05  --clausifier_options                    --mode clausify
% 11.55/2.05  --stdin                                 false
% 11.55/2.05  --stats_out                             all
% 11.55/2.05  
% 11.55/2.05  ------ General Options
% 11.55/2.05  
% 11.55/2.05  --fof                                   false
% 11.55/2.05  --time_out_real                         305.
% 11.55/2.05  --time_out_virtual                      -1.
% 11.55/2.05  --symbol_type_check                     false
% 11.55/2.05  --clausify_out                          false
% 11.55/2.05  --sig_cnt_out                           false
% 11.55/2.05  --trig_cnt_out                          false
% 11.55/2.05  --trig_cnt_out_tolerance                1.
% 11.55/2.05  --trig_cnt_out_sk_spl                   false
% 11.55/2.05  --abstr_cl_out                          false
% 11.55/2.05  
% 11.55/2.05  ------ Global Options
% 11.55/2.05  
% 11.55/2.05  --schedule                              default
% 11.55/2.05  --add_important_lit                     false
% 11.55/2.05  --prop_solver_per_cl                    1000
% 11.55/2.05  --min_unsat_core                        false
% 11.55/2.05  --soft_assumptions                      false
% 11.55/2.05  --soft_lemma_size                       3
% 11.55/2.05  --prop_impl_unit_size                   0
% 11.55/2.05  --prop_impl_unit                        []
% 11.55/2.05  --share_sel_clauses                     true
% 11.55/2.05  --reset_solvers                         false
% 11.55/2.05  --bc_imp_inh                            [conj_cone]
% 11.55/2.05  --conj_cone_tolerance                   3.
% 11.55/2.05  --extra_neg_conj                        none
% 11.55/2.05  --large_theory_mode                     true
% 11.55/2.05  --prolific_symb_bound                   200
% 11.55/2.05  --lt_threshold                          2000
% 11.55/2.05  --clause_weak_htbl                      true
% 11.55/2.05  --gc_record_bc_elim                     false
% 11.55/2.05  
% 11.55/2.05  ------ Preprocessing Options
% 11.55/2.05  
% 11.55/2.05  --preprocessing_flag                    true
% 11.55/2.05  --time_out_prep_mult                    0.1
% 11.55/2.05  --splitting_mode                        input
% 11.55/2.05  --splitting_grd                         true
% 11.55/2.05  --splitting_cvd                         false
% 11.55/2.05  --splitting_cvd_svl                     false
% 11.55/2.05  --splitting_nvd                         32
% 11.55/2.05  --sub_typing                            true
% 11.55/2.05  --prep_gs_sim                           true
% 11.55/2.05  --prep_unflatten                        true
% 11.55/2.05  --prep_res_sim                          true
% 11.55/2.05  --prep_upred                            true
% 11.55/2.05  --prep_sem_filter                       exhaustive
% 11.55/2.05  --prep_sem_filter_out                   false
% 11.55/2.05  --pred_elim                             true
% 11.55/2.05  --res_sim_input                         true
% 11.55/2.05  --eq_ax_congr_red                       true
% 11.55/2.05  --pure_diseq_elim                       true
% 11.55/2.05  --brand_transform                       false
% 11.55/2.05  --non_eq_to_eq                          false
% 11.55/2.05  --prep_def_merge                        true
% 11.55/2.05  --prep_def_merge_prop_impl              false
% 11.55/2.05  --prep_def_merge_mbd                    true
% 11.55/2.05  --prep_def_merge_tr_red                 false
% 11.55/2.05  --prep_def_merge_tr_cl                  false
% 11.55/2.05  --smt_preprocessing                     true
% 11.55/2.05  --smt_ac_axioms                         fast
% 11.55/2.05  --preprocessed_out                      false
% 11.55/2.05  --preprocessed_stats                    false
% 11.55/2.05  
% 11.55/2.05  ------ Abstraction refinement Options
% 11.55/2.05  
% 11.55/2.05  --abstr_ref                             []
% 11.55/2.05  --abstr_ref_prep                        false
% 11.55/2.05  --abstr_ref_until_sat                   false
% 11.55/2.05  --abstr_ref_sig_restrict                funpre
% 11.55/2.05  --abstr_ref_af_restrict_to_split_sk     false
% 11.55/2.05  --abstr_ref_under                       []
% 11.55/2.05  
% 11.55/2.05  ------ SAT Options
% 11.55/2.05  
% 11.55/2.05  --sat_mode                              false
% 11.55/2.05  --sat_fm_restart_options                ""
% 11.55/2.05  --sat_gr_def                            false
% 11.55/2.05  --sat_epr_types                         true
% 11.55/2.05  --sat_non_cyclic_types                  false
% 11.55/2.05  --sat_finite_models                     false
% 11.55/2.05  --sat_fm_lemmas                         false
% 11.55/2.05  --sat_fm_prep                           false
% 11.55/2.05  --sat_fm_uc_incr                        true
% 11.55/2.05  --sat_out_model                         small
% 11.55/2.05  --sat_out_clauses                       false
% 11.55/2.05  
% 11.55/2.05  ------ QBF Options
% 11.55/2.05  
% 11.55/2.05  --qbf_mode                              false
% 11.55/2.05  --qbf_elim_univ                         false
% 11.55/2.05  --qbf_dom_inst                          none
% 11.55/2.05  --qbf_dom_pre_inst                      false
% 11.55/2.05  --qbf_sk_in                             false
% 11.55/2.05  --qbf_pred_elim                         true
% 11.55/2.05  --qbf_split                             512
% 11.55/2.05  
% 11.55/2.05  ------ BMC1 Options
% 11.55/2.05  
% 11.55/2.05  --bmc1_incremental                      false
% 11.55/2.05  --bmc1_axioms                           reachable_all
% 11.55/2.05  --bmc1_min_bound                        0
% 11.55/2.05  --bmc1_max_bound                        -1
% 11.55/2.05  --bmc1_max_bound_default                -1
% 11.55/2.05  --bmc1_symbol_reachability              true
% 11.55/2.05  --bmc1_property_lemmas                  false
% 11.55/2.05  --bmc1_k_induction                      false
% 11.55/2.05  --bmc1_non_equiv_states                 false
% 11.55/2.05  --bmc1_deadlock                         false
% 11.55/2.05  --bmc1_ucm                              false
% 11.55/2.05  --bmc1_add_unsat_core                   none
% 11.55/2.05  --bmc1_unsat_core_children              false
% 11.55/2.05  --bmc1_unsat_core_extrapolate_axioms    false
% 11.55/2.05  --bmc1_out_stat                         full
% 11.55/2.05  --bmc1_ground_init                      false
% 11.55/2.05  --bmc1_pre_inst_next_state              false
% 11.55/2.05  --bmc1_pre_inst_state                   false
% 11.55/2.05  --bmc1_pre_inst_reach_state             false
% 11.55/2.05  --bmc1_out_unsat_core                   false
% 11.55/2.05  --bmc1_aig_witness_out                  false
% 11.55/2.05  --bmc1_verbose                          false
% 11.55/2.05  --bmc1_dump_clauses_tptp                false
% 11.55/2.05  --bmc1_dump_unsat_core_tptp             false
% 11.55/2.05  --bmc1_dump_file                        -
% 11.55/2.05  --bmc1_ucm_expand_uc_limit              128
% 11.55/2.05  --bmc1_ucm_n_expand_iterations          6
% 11.55/2.05  --bmc1_ucm_extend_mode                  1
% 11.55/2.05  --bmc1_ucm_init_mode                    2
% 11.55/2.05  --bmc1_ucm_cone_mode                    none
% 11.55/2.05  --bmc1_ucm_reduced_relation_type        0
% 11.55/2.05  --bmc1_ucm_relax_model                  4
% 11.55/2.05  --bmc1_ucm_full_tr_after_sat            true
% 11.55/2.05  --bmc1_ucm_expand_neg_assumptions       false
% 11.55/2.05  --bmc1_ucm_layered_model                none
% 11.55/2.05  --bmc1_ucm_max_lemma_size               10
% 11.55/2.05  
% 11.55/2.05  ------ AIG Options
% 11.55/2.05  
% 11.55/2.05  --aig_mode                              false
% 11.55/2.05  
% 11.55/2.05  ------ Instantiation Options
% 11.55/2.05  
% 11.55/2.05  --instantiation_flag                    true
% 11.55/2.05  --inst_sos_flag                         false
% 11.55/2.05  --inst_sos_phase                        true
% 11.55/2.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.55/2.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.55/2.05  --inst_lit_sel_side                     none
% 11.55/2.05  --inst_solver_per_active                1400
% 11.55/2.05  --inst_solver_calls_frac                1.
% 11.55/2.05  --inst_passive_queue_type               priority_queues
% 11.55/2.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.55/2.05  --inst_passive_queues_freq              [25;2]
% 11.55/2.05  --inst_dismatching                      true
% 11.55/2.05  --inst_eager_unprocessed_to_passive     true
% 11.55/2.05  --inst_prop_sim_given                   true
% 11.55/2.05  --inst_prop_sim_new                     false
% 11.55/2.05  --inst_subs_new                         false
% 11.55/2.05  --inst_eq_res_simp                      false
% 11.55/2.05  --inst_subs_given                       false
% 11.55/2.05  --inst_orphan_elimination               true
% 11.55/2.05  --inst_learning_loop_flag               true
% 11.55/2.05  --inst_learning_start                   3000
% 11.55/2.05  --inst_learning_factor                  2
% 11.55/2.05  --inst_start_prop_sim_after_learn       3
% 11.55/2.05  --inst_sel_renew                        solver
% 11.55/2.05  --inst_lit_activity_flag                true
% 11.55/2.05  --inst_restr_to_given                   false
% 11.55/2.05  --inst_activity_threshold               500
% 11.55/2.05  --inst_out_proof                        true
% 11.55/2.05  
% 11.55/2.05  ------ Resolution Options
% 11.55/2.05  
% 11.55/2.05  --resolution_flag                       false
% 11.55/2.05  --res_lit_sel                           adaptive
% 11.55/2.05  --res_lit_sel_side                      none
% 11.55/2.05  --res_ordering                          kbo
% 11.55/2.05  --res_to_prop_solver                    active
% 11.55/2.05  --res_prop_simpl_new                    false
% 11.55/2.05  --res_prop_simpl_given                  true
% 11.55/2.05  --res_passive_queue_type                priority_queues
% 11.55/2.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.55/2.05  --res_passive_queues_freq               [15;5]
% 11.55/2.05  --res_forward_subs                      full
% 11.55/2.05  --res_backward_subs                     full
% 11.55/2.05  --res_forward_subs_resolution           true
% 11.55/2.05  --res_backward_subs_resolution          true
% 11.55/2.05  --res_orphan_elimination                true
% 11.55/2.05  --res_time_limit                        2.
% 11.55/2.05  --res_out_proof                         true
% 11.55/2.05  
% 11.55/2.05  ------ Superposition Options
% 11.55/2.05  
% 11.55/2.05  --superposition_flag                    true
% 11.55/2.05  --sup_passive_queue_type                priority_queues
% 11.55/2.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.55/2.05  --sup_passive_queues_freq               [8;1;4]
% 11.55/2.05  --demod_completeness_check              fast
% 11.55/2.05  --demod_use_ground                      true
% 11.55/2.05  --sup_to_prop_solver                    passive
% 11.55/2.05  --sup_prop_simpl_new                    true
% 11.55/2.05  --sup_prop_simpl_given                  true
% 11.55/2.05  --sup_fun_splitting                     false
% 11.55/2.05  --sup_smt_interval                      50000
% 11.55/2.05  
% 11.55/2.05  ------ Superposition Simplification Setup
% 11.55/2.05  
% 11.55/2.05  --sup_indices_passive                   []
% 11.55/2.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.55/2.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.55/2.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.55/2.05  --sup_full_triv                         [TrivRules;PropSubs]
% 11.55/2.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.55/2.05  --sup_full_bw                           [BwDemod]
% 11.55/2.05  --sup_immed_triv                        [TrivRules]
% 11.55/2.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.55/2.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.55/2.05  --sup_immed_bw_main                     []
% 11.55/2.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.55/2.05  --sup_input_triv                        [Unflattening;TrivRules]
% 11.55/2.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.55/2.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.55/2.05  
% 11.55/2.05  ------ Combination Options
% 11.55/2.05  
% 11.55/2.05  --comb_res_mult                         3
% 11.55/2.05  --comb_sup_mult                         2
% 11.55/2.05  --comb_inst_mult                        10
% 11.55/2.05  
% 11.55/2.05  ------ Debug Options
% 11.55/2.05  
% 11.55/2.05  --dbg_backtrace                         false
% 11.55/2.05  --dbg_dump_prop_clauses                 false
% 11.55/2.05  --dbg_dump_prop_clauses_file            -
% 11.55/2.05  --dbg_out_stat                          false
% 11.55/2.05  
% 11.55/2.05  
% 11.55/2.05  
% 11.55/2.05  
% 11.55/2.05  ------ Proving...
% 11.55/2.05  
% 11.55/2.05  
% 11.55/2.05  % SZS status Theorem for theBenchmark.p
% 11.55/2.05  
% 11.55/2.05  % SZS output start CNFRefutation for theBenchmark.p
% 11.55/2.05  
% 11.55/2.05  fof(f1,axiom,(
% 11.55/2.05    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.55/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.05  
% 11.55/2.05  fof(f13,plain,(
% 11.55/2.05    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 11.55/2.05    inference(nnf_transformation,[],[f1])).
% 11.55/2.05  
% 11.55/2.05  fof(f17,plain,(
% 11.55/2.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.55/2.05    inference(cnf_transformation,[],[f13])).
% 11.55/2.05  
% 11.55/2.05  fof(f4,axiom,(
% 11.55/2.05    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.55/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.05  
% 11.55/2.05  fof(f20,plain,(
% 11.55/2.05    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.55/2.05    inference(cnf_transformation,[],[f4])).
% 11.55/2.05  
% 11.55/2.05  fof(f8,axiom,(
% 11.55/2.05    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))),
% 11.55/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.05  
% 11.55/2.05  fof(f24,plain,(
% 11.55/2.05    ( ! [X2,X0,X1] : (k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 11.55/2.05    inference(cnf_transformation,[],[f8])).
% 11.55/2.05  
% 11.55/2.05  fof(f7,axiom,(
% 11.55/2.05    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 11.55/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.05  
% 11.55/2.05  fof(f23,plain,(
% 11.55/2.05    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 11.55/2.05    inference(cnf_transformation,[],[f7])).
% 11.55/2.05  
% 11.55/2.05  fof(f26,plain,(
% 11.55/2.05    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 11.55/2.05    inference(definition_unfolding,[],[f24,f23,f23])).
% 11.55/2.05  
% 11.55/2.05  fof(f6,axiom,(
% 11.55/2.05    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 11.55/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.05  
% 11.55/2.05  fof(f22,plain,(
% 11.55/2.05    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 11.55/2.05    inference(cnf_transformation,[],[f6])).
% 11.55/2.05  
% 11.55/2.05  fof(f2,axiom,(
% 11.55/2.05    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.55/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.05  
% 11.55/2.05  fof(f11,plain,(
% 11.55/2.05    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.55/2.05    inference(ennf_transformation,[],[f2])).
% 11.55/2.05  
% 11.55/2.05  fof(f18,plain,(
% 11.55/2.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.55/2.05    inference(cnf_transformation,[],[f11])).
% 11.55/2.05  
% 11.55/2.05  fof(f3,axiom,(
% 11.55/2.05    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 11.55/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.05  
% 11.55/2.05  fof(f19,plain,(
% 11.55/2.05    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.55/2.05    inference(cnf_transformation,[],[f3])).
% 11.55/2.05  
% 11.55/2.05  fof(f9,conjecture,(
% 11.55/2.05    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 11.55/2.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.55/2.05  
% 11.55/2.05  fof(f10,negated_conjecture,(
% 11.55/2.05    ~! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 11.55/2.05    inference(negated_conjecture,[],[f9])).
% 11.55/2.05  
% 11.55/2.05  fof(f12,plain,(
% 11.55/2.05    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 11.55/2.05    inference(ennf_transformation,[],[f10])).
% 11.55/2.05  
% 11.55/2.05  fof(f14,plain,(
% 11.55/2.05    ? [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) != k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) => k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 11.55/2.05    introduced(choice_axiom,[])).
% 11.55/2.05  
% 11.55/2.05  fof(f15,plain,(
% 11.55/2.05    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 11.55/2.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 11.55/2.05  
% 11.55/2.05  fof(f25,plain,(
% 11.55/2.05    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))),
% 11.55/2.05    inference(cnf_transformation,[],[f15])).
% 11.55/2.05  
% 11.55/2.05  fof(f27,plain,(
% 11.55/2.05    k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2)))),
% 11.55/2.05    inference(definition_unfolding,[],[f25,f23])).
% 11.55/2.05  
% 11.55/2.05  cnf(c_0,plain,
% 11.55/2.05      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.55/2.05      inference(cnf_transformation,[],[f17]) ).
% 11.55/2.05  
% 11.55/2.05  cnf(c_52,plain,
% 11.55/2.05      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.55/2.05      inference(prop_impl,[status(thm)],[c_0]) ).
% 11.55/2.05  
% 11.55/2.05  cnf(c_4,plain,
% 11.55/2.05      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 11.55/2.05      inference(cnf_transformation,[],[f20]) ).
% 11.55/2.05  
% 11.55/2.05  cnf(c_115,plain,
% 11.55/2.05      ( X0 != X1
% 11.55/2.05      | k4_xboole_0(X0,X2) != X3
% 11.55/2.05      | k4_xboole_0(X3,X1) = k1_xboole_0 ),
% 11.55/2.05      inference(resolution_lifted,[status(thm)],[c_52,c_4]) ).
% 11.55/2.05  
% 11.55/2.05  cnf(c_116,plain,
% 11.55/2.05      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 11.55/2.05      inference(unflattening,[status(thm)],[c_115]) ).
% 11.55/2.05  
% 11.55/2.05  cnf(c_7,plain,
% 11.55/2.05      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 11.55/2.05      inference(cnf_transformation,[],[f26]) ).
% 11.55/2.05  
% 11.55/2.05  cnf(c_507,plain,
% 11.55/2.05      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0),X2) ),
% 11.55/2.05      inference(superposition,[status(thm)],[c_116,c_7]) ).
% 11.55/2.05  
% 11.55/2.05  cnf(c_6,plain,
% 11.55/2.05      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.55/2.05      inference(cnf_transformation,[],[f22]) ).
% 11.55/2.05  
% 11.55/2.05  cnf(c_2,plain,
% 11.55/2.05      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.55/2.05      inference(cnf_transformation,[],[f18]) ).
% 11.55/2.05  
% 11.55/2.05  cnf(c_3,plain,
% 11.55/2.05      ( r1_tarski(k1_xboole_0,X0) ),
% 11.55/2.05      inference(cnf_transformation,[],[f19]) ).
% 11.55/2.05  
% 11.55/2.05  cnf(c_97,plain,
% 11.55/2.05      ( X0 != X1 | k2_xboole_0(X2,X1) = X1 | k1_xboole_0 != X2 ),
% 11.55/2.05      inference(resolution_lifted,[status(thm)],[c_2,c_3]) ).
% 11.55/2.05  
% 11.55/2.05  cnf(c_98,plain,
% 11.55/2.05      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 11.55/2.05      inference(unflattening,[status(thm)],[c_97]) ).
% 11.55/2.05  
% 11.55/2.05  cnf(c_555,plain,
% 11.55/2.05      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.55/2.05      inference(demodulation,[status(thm)],[c_507,c_6,c_98]) ).
% 11.55/2.05  
% 11.55/2.05  cnf(c_8,negated_conjecture,
% 11.55/2.05      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK2))) ),
% 11.55/2.05      inference(cnf_transformation,[],[f27]) ).
% 11.55/2.05  
% 11.55/2.05  cnf(c_152,plain,
% 11.55/2.05      ( k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK2))))) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 11.55/2.05      inference(demodulation,[status(thm)],[c_8,c_6]) ).
% 11.55/2.05  
% 11.55/2.05  cnf(c_49722,plain,
% 11.55/2.05      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 11.55/2.05      inference(demodulation,[status(thm)],[c_555,c_152]) ).
% 11.55/2.05  
% 11.55/2.05  cnf(c_127,plain,( X0 = X0 ),theory(equality) ).
% 11.55/2.05  
% 11.55/2.05  cnf(c_167,plain,
% 11.55/2.05      ( k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
% 11.55/2.05      inference(instantiation,[status(thm)],[c_127]) ).
% 11.55/2.05  
% 11.55/2.05  cnf(contradiction,plain,
% 11.55/2.05      ( $false ),
% 11.55/2.05      inference(minisat,[status(thm)],[c_49722,c_167]) ).
% 11.55/2.05  
% 11.55/2.05  
% 11.55/2.05  % SZS output end CNFRefutation for theBenchmark.p
% 11.55/2.05  
% 11.55/2.05  ------                               Statistics
% 11.55/2.05  
% 11.55/2.05  ------ General
% 11.55/2.05  
% 11.55/2.05  abstr_ref_over_cycles:                  0
% 11.55/2.05  abstr_ref_under_cycles:                 0
% 11.55/2.05  gc_basic_clause_elim:                   0
% 11.55/2.05  forced_gc_time:                         0
% 11.55/2.05  parsing_time:                           0.013
% 11.55/2.05  unif_index_cands_time:                  0.
% 11.55/2.05  unif_index_add_time:                    0.
% 11.55/2.05  orderings_time:                         0.
% 11.55/2.05  out_proof_time:                         0.007
% 11.55/2.05  total_time:                             1.249
% 11.55/2.05  num_of_symbols:                         38
% 11.55/2.05  num_of_terms:                           68333
% 11.55/2.05  
% 11.55/2.05  ------ Preprocessing
% 11.55/2.05  
% 11.55/2.05  num_of_splits:                          0
% 11.55/2.05  num_of_split_atoms:                     0
% 11.55/2.05  num_of_reused_defs:                     0
% 11.55/2.05  num_eq_ax_congr_red:                    1
% 11.55/2.05  num_of_sem_filtered_clauses:            0
% 11.55/2.05  num_of_subtypes:                        0
% 11.55/2.05  monotx_restored_types:                  0
% 11.55/2.05  sat_num_of_epr_types:                   0
% 11.55/2.05  sat_num_of_non_cyclic_types:            0
% 11.55/2.05  sat_guarded_non_collapsed_types:        0
% 11.55/2.05  num_pure_diseq_elim:                    0
% 11.55/2.05  simp_replaced_by:                       0
% 11.55/2.05  res_preprocessed:                       22
% 11.55/2.05  prep_upred:                             0
% 11.55/2.05  prep_unflattend:                        8
% 11.55/2.05  smt_new_axioms:                         0
% 11.55/2.05  pred_elim_cands:                        1
% 11.55/2.05  pred_elim:                              1
% 11.55/2.05  pred_elim_cl:                           0
% 11.55/2.05  pred_elim_cycles:                       2
% 11.55/2.05  merged_defs:                            2
% 11.55/2.05  merged_defs_ncl:                        0
% 11.55/2.05  bin_hyper_res:                          2
% 11.55/2.05  prep_cycles:                            2
% 11.55/2.05  pred_elim_time:                         0.001
% 11.55/2.05  splitting_time:                         0.
% 11.55/2.05  sem_filter_time:                        0.
% 11.55/2.05  monotx_time:                            0.001
% 11.55/2.05  subtype_inf_time:                       0.
% 11.55/2.05  
% 11.55/2.05  ------ Problem properties
% 11.55/2.05  
% 11.55/2.05  clauses:                                9
% 11.55/2.05  conjectures:                            1
% 11.55/2.05  epr:                                    0
% 11.55/2.05  horn:                                   9
% 11.55/2.05  ground:                                 1
% 11.55/2.05  unary:                                  8
% 11.55/2.05  binary:                                 1
% 11.55/2.05  lits:                                   10
% 11.55/2.05  lits_eq:                                10
% 11.55/2.05  fd_pure:                                0
% 11.55/2.05  fd_pseudo:                              0
% 11.55/2.05  fd_cond:                                0
% 11.55/2.05  fd_pseudo_cond:                         0
% 11.55/2.05  ac_symbols:                             0
% 11.55/2.05  
% 11.55/2.05  ------ Propositional Solver
% 11.55/2.05  
% 11.55/2.05  prop_solver_calls:                      25
% 11.55/2.05  prop_fast_solver_calls:                 241
% 11.55/2.05  smt_solver_calls:                       0
% 11.55/2.05  smt_fast_solver_calls:                  0
% 11.55/2.05  prop_num_of_clauses:                    8818
% 11.55/2.05  prop_preprocess_simplified:             11153
% 11.55/2.05  prop_fo_subsumed:                       0
% 11.55/2.05  prop_solver_time:                       0.
% 11.55/2.05  smt_solver_time:                        0.
% 11.55/2.05  smt_fast_solver_time:                   0.
% 11.55/2.05  prop_fast_solver_time:                  0.
% 11.55/2.05  prop_unsat_core_time:                   0.001
% 11.55/2.05  
% 11.55/2.05  ------ QBF
% 11.55/2.05  
% 11.55/2.05  qbf_q_res:                              0
% 11.55/2.05  qbf_num_tautologies:                    0
% 11.55/2.05  qbf_prep_cycles:                        0
% 11.55/2.05  
% 11.55/2.05  ------ BMC1
% 11.55/2.05  
% 11.55/2.05  bmc1_current_bound:                     -1
% 11.55/2.05  bmc1_last_solved_bound:                 -1
% 11.55/2.05  bmc1_unsat_core_size:                   -1
% 11.55/2.05  bmc1_unsat_core_parents_size:           -1
% 11.55/2.05  bmc1_merge_next_fun:                    0
% 11.55/2.05  bmc1_unsat_core_clauses_time:           0.
% 11.55/2.05  
% 11.55/2.05  ------ Instantiation
% 11.55/2.05  
% 11.55/2.05  inst_num_of_clauses:                    2821
% 11.55/2.05  inst_num_in_passive:                    1187
% 11.55/2.05  inst_num_in_active:                     746
% 11.55/2.05  inst_num_in_unprocessed:                894
% 11.55/2.05  inst_num_of_loops:                      760
% 11.55/2.05  inst_num_of_learning_restarts:          0
% 11.55/2.05  inst_num_moves_active_passive:          10
% 11.55/2.05  inst_lit_activity:                      0
% 11.55/2.05  inst_lit_activity_moves:                0
% 11.55/2.05  inst_num_tautologies:                   0
% 11.55/2.05  inst_num_prop_implied:                  0
% 11.55/2.05  inst_num_existing_simplified:           0
% 11.55/2.05  inst_num_eq_res_simplified:             0
% 11.55/2.05  inst_num_child_elim:                    0
% 11.55/2.05  inst_num_of_dismatching_blockings:      1728
% 11.55/2.05  inst_num_of_non_proper_insts:           2624
% 11.55/2.05  inst_num_of_duplicates:                 0
% 11.55/2.05  inst_inst_num_from_inst_to_res:         0
% 11.55/2.05  inst_dismatching_checking_time:         0.
% 11.55/2.05  
% 11.55/2.05  ------ Resolution
% 11.55/2.05  
% 11.55/2.05  res_num_of_clauses:                     0
% 11.55/2.05  res_num_in_passive:                     0
% 11.55/2.05  res_num_in_active:                      0
% 11.55/2.05  res_num_of_loops:                       24
% 11.55/2.05  res_forward_subset_subsumed:            456
% 11.55/2.05  res_backward_subset_subsumed:           16
% 11.55/2.05  res_forward_subsumed:                   0
% 11.55/2.05  res_backward_subsumed:                  0
% 11.55/2.05  res_forward_subsumption_resolution:     0
% 11.55/2.05  res_backward_subsumption_resolution:    0
% 11.55/2.05  res_clause_to_clause_subsumption:       65281
% 11.55/2.05  res_orphan_elimination:                 0
% 11.55/2.05  res_tautology_del:                      242
% 11.55/2.05  res_num_eq_res_simplified:              0
% 11.55/2.05  res_num_sel_changes:                    0
% 11.55/2.05  res_moves_from_active_to_pass:          0
% 11.55/2.05  
% 11.55/2.05  ------ Superposition
% 11.55/2.05  
% 11.55/2.05  sup_time_total:                         0.
% 11.55/2.05  sup_time_generating:                    0.
% 11.55/2.05  sup_time_sim_full:                      0.
% 11.55/2.05  sup_time_sim_immed:                     0.
% 11.55/2.05  
% 11.55/2.05  sup_num_of_clauses:                     2718
% 11.55/2.05  sup_num_in_active:                      127
% 11.55/2.05  sup_num_in_passive:                     2591
% 11.55/2.05  sup_num_of_loops:                       150
% 11.55/2.05  sup_fw_superposition:                   9065
% 11.55/2.05  sup_bw_superposition:                   8201
% 11.55/2.05  sup_immediate_simplified:               8166
% 11.55/2.05  sup_given_eliminated:                   3
% 11.55/2.05  comparisons_done:                       0
% 11.55/2.05  comparisons_avoided:                    0
% 11.55/2.05  
% 11.55/2.05  ------ Simplifications
% 11.55/2.05  
% 11.55/2.05  
% 11.55/2.05  sim_fw_subset_subsumed:                 4
% 11.55/2.05  sim_bw_subset_subsumed:                 0
% 11.55/2.05  sim_fw_subsumed:                        2244
% 11.55/2.05  sim_bw_subsumed:                        25
% 11.55/2.05  sim_fw_subsumption_res:                 0
% 11.55/2.05  sim_bw_subsumption_res:                 0
% 11.55/2.05  sim_tautology_del:                      3
% 11.55/2.05  sim_eq_tautology_del:                   1812
% 11.55/2.05  sim_eq_res_simp:                        67
% 11.55/2.05  sim_fw_demodulated:                     4617
% 11.55/2.05  sim_bw_demodulated:                     134
% 11.55/2.05  sim_light_normalised:                   3071
% 11.55/2.05  sim_joinable_taut:                      0
% 11.55/2.05  sim_joinable_simp:                      0
% 11.55/2.05  sim_ac_normalised:                      0
% 11.55/2.05  sim_smt_subsumption:                    0
% 11.55/2.05  
%------------------------------------------------------------------------------
