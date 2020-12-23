%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:04:37 EST 2020

% Result     : Theorem 0.67s
% Output     : CNFRefutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   32 (  46 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    5 (   9 expanded)
%              Depth                    :   15
%              Number of atoms          :   77 ( 129 expanded)
%              Number of equality atoms :   30 (  46 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
     => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k8_relset_1(X0,X1,X3,X2),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_1(X2) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f28,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k8_relset_1(X1,X2,X0,X3),X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_8,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_60,plain,
    ( r1_tarski(k8_relset_1(X0,X1,X2,X3),X0)
    | ~ v1_funct_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_8])).

cnf(c_61,plain,
    ( r1_tarski(k8_relset_1(X0,X1,sK2,X2),X0)
    | ~ v1_funct_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) ),
    inference(unflattening,[status(thm)],[c_60])).

cnf(c_9,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_65,plain,
    ( r1_tarski(k8_relset_1(X0,X1,sK2,X2),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_61,c_9])).

cnf(c_81,plain,
    ( k8_relset_1(X0,X1,sK2,X2) != X3
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
    | k1_xboole_0 != X0
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_65])).

cnf(c_82,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
    | k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X1) ),
    inference(unflattening,[status(thm)],[c_81])).

cnf(c_132,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
    | k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,X0) ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_154,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
    | k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_98,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_131,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) ),
    inference(instantiation,[status(thm)],[c_98])).

cnf(c_7,negated_conjecture,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_154,c_131,c_7])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n008.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 14:53:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 0.67/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.67/1.01  
% 0.67/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.67/1.01  
% 0.67/1.01  ------  iProver source info
% 0.67/1.01  
% 0.67/1.01  git: date: 2020-06-30 10:37:57 +0100
% 0.67/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.67/1.01  git: non_committed_changes: false
% 0.67/1.01  git: last_make_outside_of_git: false
% 0.67/1.01  
% 0.67/1.01  ------ 
% 0.67/1.01  
% 0.67/1.01  ------ Input Options
% 0.67/1.01  
% 0.67/1.01  --out_options                           all
% 0.67/1.01  --tptp_safe_out                         true
% 0.67/1.01  --problem_path                          ""
% 0.67/1.01  --include_path                          ""
% 0.67/1.01  --clausifier                            res/vclausify_rel
% 0.67/1.01  --clausifier_options                    --mode clausify
% 0.67/1.01  --stdin                                 false
% 0.67/1.01  --stats_out                             all
% 0.67/1.01  
% 0.67/1.01  ------ General Options
% 0.67/1.01  
% 0.67/1.01  --fof                                   false
% 0.67/1.01  --time_out_real                         305.
% 0.67/1.01  --time_out_virtual                      -1.
% 0.67/1.01  --symbol_type_check                     false
% 0.67/1.01  --clausify_out                          false
% 0.67/1.01  --sig_cnt_out                           false
% 0.67/1.01  --trig_cnt_out                          false
% 0.67/1.01  --trig_cnt_out_tolerance                1.
% 0.67/1.01  --trig_cnt_out_sk_spl                   false
% 0.67/1.01  --abstr_cl_out                          false
% 0.67/1.01  
% 0.67/1.01  ------ Global Options
% 0.67/1.01  
% 0.67/1.01  --schedule                              default
% 0.67/1.01  --add_important_lit                     false
% 0.67/1.01  --prop_solver_per_cl                    1000
% 0.67/1.01  --min_unsat_core                        false
% 0.67/1.01  --soft_assumptions                      false
% 0.67/1.01  --soft_lemma_size                       3
% 0.67/1.01  --prop_impl_unit_size                   0
% 0.67/1.01  --prop_impl_unit                        []
% 0.67/1.01  --share_sel_clauses                     true
% 0.67/1.01  --reset_solvers                         false
% 0.67/1.01  --bc_imp_inh                            [conj_cone]
% 0.67/1.01  --conj_cone_tolerance                   3.
% 0.67/1.01  --extra_neg_conj                        none
% 0.67/1.01  --large_theory_mode                     true
% 0.67/1.01  --prolific_symb_bound                   200
% 0.67/1.01  --lt_threshold                          2000
% 0.67/1.01  --clause_weak_htbl                      true
% 0.67/1.01  --gc_record_bc_elim                     false
% 0.67/1.01  
% 0.67/1.01  ------ Preprocessing Options
% 0.67/1.01  
% 0.67/1.01  --preprocessing_flag                    true
% 0.67/1.01  --time_out_prep_mult                    0.1
% 0.67/1.01  --splitting_mode                        input
% 0.67/1.01  --splitting_grd                         true
% 0.67/1.01  --splitting_cvd                         false
% 0.67/1.01  --splitting_cvd_svl                     false
% 0.67/1.01  --splitting_nvd                         32
% 0.67/1.01  --sub_typing                            true
% 0.67/1.01  --prep_gs_sim                           true
% 0.67/1.01  --prep_unflatten                        true
% 0.67/1.01  --prep_res_sim                          true
% 0.67/1.01  --prep_upred                            true
% 0.67/1.01  --prep_sem_filter                       exhaustive
% 0.67/1.01  --prep_sem_filter_out                   false
% 0.67/1.01  --pred_elim                             true
% 0.67/1.01  --res_sim_input                         true
% 0.67/1.01  --eq_ax_congr_red                       true
% 0.67/1.01  --pure_diseq_elim                       true
% 0.67/1.01  --brand_transform                       false
% 0.67/1.01  --non_eq_to_eq                          false
% 0.67/1.01  --prep_def_merge                        true
% 0.67/1.01  --prep_def_merge_prop_impl              false
% 0.67/1.01  --prep_def_merge_mbd                    true
% 0.67/1.01  --prep_def_merge_tr_red                 false
% 0.67/1.01  --prep_def_merge_tr_cl                  false
% 0.67/1.01  --smt_preprocessing                     true
% 0.67/1.01  --smt_ac_axioms                         fast
% 0.67/1.01  --preprocessed_out                      false
% 0.67/1.01  --preprocessed_stats                    false
% 0.67/1.01  
% 0.67/1.01  ------ Abstraction refinement Options
% 0.67/1.01  
% 0.67/1.01  --abstr_ref                             []
% 0.67/1.01  --abstr_ref_prep                        false
% 0.67/1.01  --abstr_ref_until_sat                   false
% 0.67/1.01  --abstr_ref_sig_restrict                funpre
% 0.67/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.67/1.01  --abstr_ref_under                       []
% 0.67/1.01  
% 0.67/1.01  ------ SAT Options
% 0.67/1.01  
% 0.67/1.01  --sat_mode                              false
% 0.67/1.01  --sat_fm_restart_options                ""
% 0.67/1.01  --sat_gr_def                            false
% 0.67/1.01  --sat_epr_types                         true
% 0.67/1.01  --sat_non_cyclic_types                  false
% 0.67/1.01  --sat_finite_models                     false
% 0.67/1.01  --sat_fm_lemmas                         false
% 0.67/1.01  --sat_fm_prep                           false
% 0.67/1.01  --sat_fm_uc_incr                        true
% 0.67/1.01  --sat_out_model                         small
% 0.67/1.01  --sat_out_clauses                       false
% 0.67/1.01  
% 0.67/1.01  ------ QBF Options
% 0.67/1.01  
% 0.67/1.01  --qbf_mode                              false
% 0.67/1.01  --qbf_elim_univ                         false
% 0.67/1.01  --qbf_dom_inst                          none
% 0.67/1.01  --qbf_dom_pre_inst                      false
% 0.67/1.01  --qbf_sk_in                             false
% 0.67/1.01  --qbf_pred_elim                         true
% 0.67/1.01  --qbf_split                             512
% 0.67/1.01  
% 0.67/1.01  ------ BMC1 Options
% 0.67/1.01  
% 0.67/1.01  --bmc1_incremental                      false
% 0.67/1.01  --bmc1_axioms                           reachable_all
% 0.67/1.01  --bmc1_min_bound                        0
% 0.67/1.01  --bmc1_max_bound                        -1
% 0.67/1.01  --bmc1_max_bound_default                -1
% 0.67/1.01  --bmc1_symbol_reachability              true
% 0.67/1.01  --bmc1_property_lemmas                  false
% 0.67/1.01  --bmc1_k_induction                      false
% 0.67/1.01  --bmc1_non_equiv_states                 false
% 0.67/1.01  --bmc1_deadlock                         false
% 0.67/1.01  --bmc1_ucm                              false
% 0.67/1.01  --bmc1_add_unsat_core                   none
% 0.67/1.01  --bmc1_unsat_core_children              false
% 0.67/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.67/1.01  --bmc1_out_stat                         full
% 0.67/1.01  --bmc1_ground_init                      false
% 0.67/1.01  --bmc1_pre_inst_next_state              false
% 0.67/1.01  --bmc1_pre_inst_state                   false
% 0.67/1.01  --bmc1_pre_inst_reach_state             false
% 0.67/1.01  --bmc1_out_unsat_core                   false
% 0.67/1.01  --bmc1_aig_witness_out                  false
% 0.67/1.01  --bmc1_verbose                          false
% 0.67/1.01  --bmc1_dump_clauses_tptp                false
% 0.67/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.67/1.01  --bmc1_dump_file                        -
% 0.67/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.67/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.67/1.01  --bmc1_ucm_extend_mode                  1
% 0.67/1.01  --bmc1_ucm_init_mode                    2
% 0.67/1.01  --bmc1_ucm_cone_mode                    none
% 0.67/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.67/1.01  --bmc1_ucm_relax_model                  4
% 0.67/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.67/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.67/1.01  --bmc1_ucm_layered_model                none
% 0.67/1.01  --bmc1_ucm_max_lemma_size               10
% 0.67/1.01  
% 0.67/1.01  ------ AIG Options
% 0.67/1.01  
% 0.67/1.01  --aig_mode                              false
% 0.67/1.01  
% 0.67/1.01  ------ Instantiation Options
% 0.67/1.01  
% 0.67/1.01  --instantiation_flag                    true
% 0.67/1.01  --inst_sos_flag                         false
% 0.67/1.01  --inst_sos_phase                        true
% 0.67/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.67/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.67/1.01  --inst_lit_sel_side                     num_symb
% 0.67/1.01  --inst_solver_per_active                1400
% 0.67/1.01  --inst_solver_calls_frac                1.
% 0.67/1.01  --inst_passive_queue_type               priority_queues
% 0.67/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.67/1.01  --inst_passive_queues_freq              [25;2]
% 0.67/1.01  --inst_dismatching                      true
% 0.67/1.01  --inst_eager_unprocessed_to_passive     true
% 0.67/1.01  --inst_prop_sim_given                   true
% 0.67/1.01  --inst_prop_sim_new                     false
% 0.67/1.01  --inst_subs_new                         false
% 0.67/1.01  --inst_eq_res_simp                      false
% 0.67/1.01  --inst_subs_given                       false
% 0.67/1.01  --inst_orphan_elimination               true
% 0.67/1.01  --inst_learning_loop_flag               true
% 0.67/1.01  --inst_learning_start                   3000
% 0.67/1.01  --inst_learning_factor                  2
% 0.67/1.01  --inst_start_prop_sim_after_learn       3
% 0.67/1.01  --inst_sel_renew                        solver
% 0.67/1.01  --inst_lit_activity_flag                true
% 0.67/1.01  --inst_restr_to_given                   false
% 0.67/1.01  --inst_activity_threshold               500
% 0.67/1.01  --inst_out_proof                        true
% 0.67/1.01  
% 0.67/1.01  ------ Resolution Options
% 0.67/1.01  
% 0.67/1.01  --resolution_flag                       true
% 0.67/1.01  --res_lit_sel                           adaptive
% 0.67/1.01  --res_lit_sel_side                      none
% 0.67/1.01  --res_ordering                          kbo
% 0.67/1.01  --res_to_prop_solver                    active
% 0.67/1.01  --res_prop_simpl_new                    false
% 0.67/1.01  --res_prop_simpl_given                  true
% 0.67/1.01  --res_passive_queue_type                priority_queues
% 0.67/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.67/1.01  --res_passive_queues_freq               [15;5]
% 0.67/1.01  --res_forward_subs                      full
% 0.67/1.01  --res_backward_subs                     full
% 0.67/1.01  --res_forward_subs_resolution           true
% 0.67/1.01  --res_backward_subs_resolution          true
% 0.67/1.01  --res_orphan_elimination                true
% 0.67/1.01  --res_time_limit                        2.
% 0.67/1.01  --res_out_proof                         true
% 0.67/1.01  
% 0.67/1.01  ------ Superposition Options
% 0.67/1.01  
% 0.67/1.01  --superposition_flag                    true
% 0.67/1.01  --sup_passive_queue_type                priority_queues
% 0.67/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.67/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.67/1.01  --demod_completeness_check              fast
% 0.67/1.01  --demod_use_ground                      true
% 0.67/1.01  --sup_to_prop_solver                    passive
% 0.67/1.01  --sup_prop_simpl_new                    true
% 0.67/1.01  --sup_prop_simpl_given                  true
% 0.67/1.01  --sup_fun_splitting                     false
% 0.67/1.01  --sup_smt_interval                      50000
% 0.67/1.01  
% 0.67/1.01  ------ Superposition Simplification Setup
% 0.67/1.01  
% 0.67/1.01  --sup_indices_passive                   []
% 0.67/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.67/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.67/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.67/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.67/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.67/1.01  --sup_full_bw                           [BwDemod]
% 0.67/1.01  --sup_immed_triv                        [TrivRules]
% 0.67/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.67/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.67/1.01  --sup_immed_bw_main                     []
% 0.67/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.67/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.67/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.67/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.67/1.01  
% 0.67/1.01  ------ Combination Options
% 0.67/1.01  
% 0.67/1.01  --comb_res_mult                         3
% 0.67/1.01  --comb_sup_mult                         2
% 0.67/1.01  --comb_inst_mult                        10
% 0.67/1.01  
% 0.67/1.01  ------ Debug Options
% 0.67/1.01  
% 0.67/1.01  --dbg_backtrace                         false
% 0.67/1.01  --dbg_dump_prop_clauses                 false
% 0.67/1.01  --dbg_dump_prop_clauses_file            -
% 0.67/1.01  --dbg_out_stat                          false
% 0.67/1.01  ------ Parsing...
% 0.67/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.67/1.01  
% 0.67/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 0.67/1.01  
% 0.67/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.67/1.01  
% 0.67/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.67/1.01  ------ Proving...
% 0.67/1.01  ------ Problem Properties 
% 0.67/1.01  
% 0.67/1.01  
% 0.67/1.01  clauses                                 7
% 0.67/1.01  conjectures                             1
% 0.67/1.01  EPR                                     0
% 0.67/1.01  Horn                                    6
% 0.67/1.01  unary                                   5
% 0.67/1.01  binary                                  1
% 0.67/1.01  lits                                    11
% 0.67/1.01  lits eq                                 11
% 0.67/1.01  fd_pure                                 0
% 0.67/1.01  fd_pseudo                               0
% 0.67/1.01  fd_cond                                 1
% 0.67/1.01  fd_pseudo_cond                          0
% 0.67/1.01  AC symbols                              0
% 0.67/1.01  
% 0.67/1.01  ------ Schedule dynamic 5 is on 
% 0.67/1.01  
% 0.67/1.01  ------ pure equality problem: resolution off 
% 0.67/1.01  
% 0.67/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.67/1.01  
% 0.67/1.01  
% 0.67/1.01  ------ 
% 0.67/1.01  Current options:
% 0.67/1.01  ------ 
% 0.67/1.01  
% 0.67/1.01  ------ Input Options
% 0.67/1.01  
% 0.67/1.01  --out_options                           all
% 0.67/1.01  --tptp_safe_out                         true
% 0.67/1.01  --problem_path                          ""
% 0.67/1.01  --include_path                          ""
% 0.67/1.01  --clausifier                            res/vclausify_rel
% 0.67/1.01  --clausifier_options                    --mode clausify
% 0.67/1.01  --stdin                                 false
% 0.67/1.01  --stats_out                             all
% 0.67/1.01  
% 0.67/1.01  ------ General Options
% 0.67/1.01  
% 0.67/1.01  --fof                                   false
% 0.67/1.01  --time_out_real                         305.
% 0.67/1.01  --time_out_virtual                      -1.
% 0.67/1.01  --symbol_type_check                     false
% 0.67/1.01  --clausify_out                          false
% 0.67/1.01  --sig_cnt_out                           false
% 0.67/1.01  --trig_cnt_out                          false
% 0.67/1.01  --trig_cnt_out_tolerance                1.
% 0.67/1.01  --trig_cnt_out_sk_spl                   false
% 0.67/1.01  --abstr_cl_out                          false
% 0.67/1.01  
% 0.67/1.01  ------ Global Options
% 0.67/1.01  
% 0.67/1.01  --schedule                              default
% 0.67/1.01  --add_important_lit                     false
% 0.67/1.01  --prop_solver_per_cl                    1000
% 0.67/1.01  --min_unsat_core                        false
% 0.67/1.01  --soft_assumptions                      false
% 0.67/1.01  --soft_lemma_size                       3
% 0.67/1.01  --prop_impl_unit_size                   0
% 0.67/1.01  --prop_impl_unit                        []
% 0.67/1.01  --share_sel_clauses                     true
% 0.67/1.01  --reset_solvers                         false
% 0.67/1.01  --bc_imp_inh                            [conj_cone]
% 0.67/1.01  --conj_cone_tolerance                   3.
% 0.67/1.01  --extra_neg_conj                        none
% 0.67/1.01  --large_theory_mode                     true
% 0.67/1.01  --prolific_symb_bound                   200
% 0.67/1.01  --lt_threshold                          2000
% 0.67/1.01  --clause_weak_htbl                      true
% 0.67/1.01  --gc_record_bc_elim                     false
% 0.67/1.01  
% 0.67/1.01  ------ Preprocessing Options
% 0.67/1.01  
% 0.67/1.01  --preprocessing_flag                    true
% 0.67/1.01  --time_out_prep_mult                    0.1
% 0.67/1.01  --splitting_mode                        input
% 0.67/1.01  --splitting_grd                         true
% 0.67/1.01  --splitting_cvd                         false
% 0.67/1.01  --splitting_cvd_svl                     false
% 0.67/1.01  --splitting_nvd                         32
% 0.67/1.01  --sub_typing                            true
% 0.67/1.01  --prep_gs_sim                           true
% 0.67/1.01  --prep_unflatten                        true
% 0.67/1.01  --prep_res_sim                          true
% 0.67/1.01  --prep_upred                            true
% 0.67/1.01  --prep_sem_filter                       exhaustive
% 0.67/1.01  --prep_sem_filter_out                   false
% 0.67/1.01  --pred_elim                             true
% 0.67/1.01  --res_sim_input                         true
% 0.67/1.01  --eq_ax_congr_red                       true
% 0.67/1.01  --pure_diseq_elim                       true
% 0.67/1.01  --brand_transform                       false
% 0.67/1.01  --non_eq_to_eq                          false
% 0.67/1.01  --prep_def_merge                        true
% 0.67/1.01  --prep_def_merge_prop_impl              false
% 0.67/1.01  --prep_def_merge_mbd                    true
% 0.67/1.01  --prep_def_merge_tr_red                 false
% 0.67/1.01  --prep_def_merge_tr_cl                  false
% 0.67/1.01  --smt_preprocessing                     true
% 0.67/1.01  --smt_ac_axioms                         fast
% 0.67/1.01  --preprocessed_out                      false
% 0.67/1.01  --preprocessed_stats                    false
% 0.67/1.01  
% 0.67/1.01  ------ Abstraction refinement Options
% 0.67/1.01  
% 0.67/1.01  --abstr_ref                             []
% 0.67/1.01  --abstr_ref_prep                        false
% 0.67/1.01  --abstr_ref_until_sat                   false
% 0.67/1.01  --abstr_ref_sig_restrict                funpre
% 0.67/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.67/1.01  --abstr_ref_under                       []
% 0.67/1.01  
% 0.67/1.01  ------ SAT Options
% 0.67/1.01  
% 0.67/1.01  --sat_mode                              false
% 0.67/1.01  --sat_fm_restart_options                ""
% 0.67/1.01  --sat_gr_def                            false
% 0.67/1.01  --sat_epr_types                         true
% 0.67/1.01  --sat_non_cyclic_types                  false
% 0.67/1.01  --sat_finite_models                     false
% 0.67/1.01  --sat_fm_lemmas                         false
% 0.67/1.01  --sat_fm_prep                           false
% 0.67/1.01  --sat_fm_uc_incr                        true
% 0.67/1.01  --sat_out_model                         small
% 0.67/1.01  --sat_out_clauses                       false
% 0.67/1.01  
% 0.67/1.01  ------ QBF Options
% 0.67/1.01  
% 0.67/1.01  --qbf_mode                              false
% 0.67/1.01  --qbf_elim_univ                         false
% 0.67/1.01  --qbf_dom_inst                          none
% 0.67/1.01  --qbf_dom_pre_inst                      false
% 0.67/1.01  --qbf_sk_in                             false
% 0.67/1.01  --qbf_pred_elim                         true
% 0.67/1.01  --qbf_split                             512
% 0.67/1.01  
% 0.67/1.01  ------ BMC1 Options
% 0.67/1.01  
% 0.67/1.01  --bmc1_incremental                      false
% 0.67/1.01  --bmc1_axioms                           reachable_all
% 0.67/1.01  --bmc1_min_bound                        0
% 0.67/1.01  --bmc1_max_bound                        -1
% 0.67/1.01  --bmc1_max_bound_default                -1
% 0.67/1.01  --bmc1_symbol_reachability              true
% 0.67/1.01  --bmc1_property_lemmas                  false
% 0.67/1.01  --bmc1_k_induction                      false
% 0.67/1.01  --bmc1_non_equiv_states                 false
% 0.67/1.01  --bmc1_deadlock                         false
% 0.67/1.01  --bmc1_ucm                              false
% 0.67/1.01  --bmc1_add_unsat_core                   none
% 0.67/1.01  --bmc1_unsat_core_children              false
% 0.67/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.67/1.01  --bmc1_out_stat                         full
% 0.67/1.01  --bmc1_ground_init                      false
% 0.67/1.01  --bmc1_pre_inst_next_state              false
% 0.67/1.01  --bmc1_pre_inst_state                   false
% 0.67/1.01  --bmc1_pre_inst_reach_state             false
% 0.67/1.01  --bmc1_out_unsat_core                   false
% 0.67/1.01  --bmc1_aig_witness_out                  false
% 0.67/1.01  --bmc1_verbose                          false
% 0.67/1.01  --bmc1_dump_clauses_tptp                false
% 0.67/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.67/1.01  --bmc1_dump_file                        -
% 0.67/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.67/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.67/1.01  --bmc1_ucm_extend_mode                  1
% 0.67/1.01  --bmc1_ucm_init_mode                    2
% 0.67/1.01  --bmc1_ucm_cone_mode                    none
% 0.67/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.67/1.01  --bmc1_ucm_relax_model                  4
% 0.67/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.67/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.67/1.01  --bmc1_ucm_layered_model                none
% 0.67/1.01  --bmc1_ucm_max_lemma_size               10
% 0.67/1.01  
% 0.67/1.01  ------ AIG Options
% 0.67/1.01  
% 0.67/1.01  --aig_mode                              false
% 0.67/1.01  
% 0.67/1.01  ------ Instantiation Options
% 0.67/1.01  
% 0.67/1.01  --instantiation_flag                    true
% 0.67/1.01  --inst_sos_flag                         false
% 0.67/1.01  --inst_sos_phase                        true
% 0.67/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.67/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.67/1.01  --inst_lit_sel_side                     none
% 0.67/1.01  --inst_solver_per_active                1400
% 0.67/1.01  --inst_solver_calls_frac                1.
% 0.67/1.01  --inst_passive_queue_type               priority_queues
% 0.67/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.67/1.01  --inst_passive_queues_freq              [25;2]
% 0.67/1.01  --inst_dismatching                      true
% 0.67/1.01  --inst_eager_unprocessed_to_passive     true
% 0.67/1.01  --inst_prop_sim_given                   true
% 0.67/1.01  --inst_prop_sim_new                     false
% 0.67/1.01  --inst_subs_new                         false
% 0.67/1.01  --inst_eq_res_simp                      false
% 0.67/1.01  --inst_subs_given                       false
% 0.67/1.01  --inst_orphan_elimination               true
% 0.67/1.01  --inst_learning_loop_flag               true
% 0.67/1.01  --inst_learning_start                   3000
% 0.67/1.01  --inst_learning_factor                  2
% 0.67/1.01  --inst_start_prop_sim_after_learn       3
% 0.67/1.01  --inst_sel_renew                        solver
% 0.67/1.01  --inst_lit_activity_flag                true
% 0.67/1.01  --inst_restr_to_given                   false
% 0.67/1.01  --inst_activity_threshold               500
% 0.67/1.01  --inst_out_proof                        true
% 0.67/1.01  
% 0.67/1.01  ------ Resolution Options
% 0.67/1.01  
% 0.67/1.01  --resolution_flag                       false
% 0.67/1.01  --res_lit_sel                           adaptive
% 0.67/1.01  --res_lit_sel_side                      none
% 0.67/1.01  --res_ordering                          kbo
% 0.67/1.01  --res_to_prop_solver                    active
% 0.67/1.01  --res_prop_simpl_new                    false
% 0.67/1.01  --res_prop_simpl_given                  true
% 0.67/1.01  --res_passive_queue_type                priority_queues
% 0.67/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.67/1.01  --res_passive_queues_freq               [15;5]
% 0.67/1.01  --res_forward_subs                      full
% 0.67/1.01  --res_backward_subs                     full
% 0.67/1.01  --res_forward_subs_resolution           true
% 0.67/1.01  --res_backward_subs_resolution          true
% 0.67/1.01  --res_orphan_elimination                true
% 0.67/1.01  --res_time_limit                        2.
% 0.67/1.01  --res_out_proof                         true
% 0.67/1.01  
% 0.67/1.01  ------ Superposition Options
% 0.67/1.01  
% 0.67/1.01  --superposition_flag                    true
% 0.67/1.01  --sup_passive_queue_type                priority_queues
% 0.67/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.67/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.67/1.01  --demod_completeness_check              fast
% 0.67/1.01  --demod_use_ground                      true
% 0.67/1.01  --sup_to_prop_solver                    passive
% 0.67/1.01  --sup_prop_simpl_new                    true
% 0.67/1.01  --sup_prop_simpl_given                  true
% 0.67/1.01  --sup_fun_splitting                     false
% 0.67/1.01  --sup_smt_interval                      50000
% 0.67/1.01  
% 0.67/1.01  ------ Superposition Simplification Setup
% 0.67/1.01  
% 0.67/1.01  --sup_indices_passive                   []
% 0.67/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.67/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.67/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.67/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.67/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.67/1.01  --sup_full_bw                           [BwDemod]
% 0.67/1.01  --sup_immed_triv                        [TrivRules]
% 0.67/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.67/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.67/1.01  --sup_immed_bw_main                     []
% 0.67/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.67/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.67/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.67/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.67/1.01  
% 0.67/1.01  ------ Combination Options
% 0.67/1.01  
% 0.67/1.01  --comb_res_mult                         3
% 0.67/1.01  --comb_sup_mult                         2
% 0.67/1.01  --comb_inst_mult                        10
% 0.67/1.01  
% 0.67/1.01  ------ Debug Options
% 0.67/1.01  
% 0.67/1.01  --dbg_backtrace                         false
% 0.67/1.01  --dbg_dump_prop_clauses                 false
% 0.67/1.01  --dbg_dump_prop_clauses_file            -
% 0.67/1.01  --dbg_out_stat                          false
% 0.67/1.01  
% 0.67/1.01  
% 0.67/1.01  
% 0.67/1.01  
% 0.67/1.01  ------ Proving...
% 0.67/1.01  
% 0.67/1.01  
% 0.67/1.01  % SZS status Theorem for theBenchmark.p
% 0.67/1.01  
% 0.67/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 0.67/1.01  
% 0.67/1.01  fof(f1,axiom,(
% 0.67/1.01    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.67/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.01  
% 0.67/1.01  fof(f9,plain,(
% 0.67/1.01    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.67/1.01    inference(ennf_transformation,[],[f1])).
% 0.67/1.01  
% 0.67/1.01  fof(f18,plain,(
% 0.67/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.67/1.01    inference(cnf_transformation,[],[f9])).
% 0.67/1.01  
% 0.67/1.01  fof(f5,axiom,(
% 0.67/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => r1_tarski(k8_relset_1(X0,X1,X3,X2),X0))),
% 0.67/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.01  
% 0.67/1.01  fof(f10,plain,(
% 0.67/1.01    ! [X0,X1,X2,X3] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)))),
% 0.67/1.01    inference(ennf_transformation,[],[f5])).
% 0.67/1.01  
% 0.67/1.01  fof(f11,plain,(
% 0.67/1.01    ! [X0,X1,X2,X3] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))),
% 0.67/1.01    inference(flattening,[],[f10])).
% 0.67/1.01  
% 0.67/1.01  fof(f25,plain,(
% 0.67/1.01    ( ! [X2,X0,X3,X1] : (r1_tarski(k8_relset_1(X0,X1,X3,X2),X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) )),
% 0.67/1.01    inference(cnf_transformation,[],[f11])).
% 0.67/1.01  
% 0.67/1.01  fof(f6,conjecture,(
% 0.67/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.67/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.67/1.01  
% 0.67/1.01  fof(f7,negated_conjecture,(
% 0.67/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.67/1.01    inference(negated_conjecture,[],[f6])).
% 0.67/1.01  
% 0.67/1.01  fof(f8,plain,(
% 0.67/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.67/1.01    inference(pure_predicate_removal,[],[f7])).
% 0.67/1.01  
% 0.67/1.01  fof(f12,plain,(
% 0.67/1.01    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)))),
% 0.67/1.01    inference(ennf_transformation,[],[f8])).
% 0.67/1.01  
% 0.67/1.01  fof(f13,plain,(
% 0.67/1.01    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2))),
% 0.67/1.01    inference(flattening,[],[f12])).
% 0.67/1.01  
% 0.67/1.01  fof(f16,plain,(
% 0.67/1.01    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_1(sK2))),
% 0.67/1.01    introduced(choice_axiom,[])).
% 0.67/1.01  
% 0.67/1.01  fof(f17,plain,(
% 0.67/1.01    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) & v1_funct_1(sK2)),
% 0.67/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16])).
% 0.67/1.01  
% 0.67/1.01  fof(f27,plain,(
% 0.67/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.67/1.01    inference(cnf_transformation,[],[f17])).
% 0.67/1.01  
% 0.67/1.01  fof(f26,plain,(
% 0.67/1.01    v1_funct_1(sK2)),
% 0.67/1.01    inference(cnf_transformation,[],[f17])).
% 0.67/1.01  
% 0.67/1.01  fof(f28,plain,(
% 0.67/1.01    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.67/1.01    inference(cnf_transformation,[],[f17])).
% 0.67/1.01  
% 0.67/1.01  cnf(c_0,plain,
% 0.67/1.01      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 0.67/1.01      inference(cnf_transformation,[],[f18]) ).
% 0.67/1.01  
% 0.67/1.01  cnf(c_6,plain,
% 0.67/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.67/1.01      | r1_tarski(k8_relset_1(X1,X2,X0,X3),X1)
% 0.67/1.01      | ~ v1_funct_1(X0) ),
% 0.67/1.01      inference(cnf_transformation,[],[f25]) ).
% 0.67/1.01  
% 0.67/1.01  cnf(c_8,negated_conjecture,
% 0.67/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
% 0.67/1.01      inference(cnf_transformation,[],[f27]) ).
% 0.67/1.01  
% 0.67/1.01  cnf(c_60,plain,
% 0.67/1.01      ( r1_tarski(k8_relset_1(X0,X1,X2,X3),X0)
% 0.67/1.01      | ~ v1_funct_1(X2)
% 0.67/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
% 0.67/1.01      | sK2 != X2 ),
% 0.67/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_8]) ).
% 0.67/1.01  
% 0.67/1.01  cnf(c_61,plain,
% 0.67/1.01      ( r1_tarski(k8_relset_1(X0,X1,sK2,X2),X0)
% 0.67/1.01      | ~ v1_funct_1(sK2)
% 0.67/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) ),
% 0.67/1.01      inference(unflattening,[status(thm)],[c_60]) ).
% 0.67/1.01  
% 0.67/1.01  cnf(c_9,negated_conjecture,
% 0.67/1.01      ( v1_funct_1(sK2) ),
% 0.67/1.01      inference(cnf_transformation,[],[f26]) ).
% 0.67/1.01  
% 0.67/1.01  cnf(c_65,plain,
% 0.67/1.01      ( r1_tarski(k8_relset_1(X0,X1,sK2,X2),X0)
% 0.67/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) ),
% 0.67/1.01      inference(global_propositional_subsumption,
% 0.67/1.01                [status(thm)],
% 0.67/1.01                [c_61,c_9]) ).
% 0.67/1.01  
% 0.67/1.01  cnf(c_81,plain,
% 0.67/1.01      ( k8_relset_1(X0,X1,sK2,X2) != X3
% 0.67/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
% 0.67/1.01      | k1_xboole_0 != X0
% 0.67/1.01      | k1_xboole_0 = X3 ),
% 0.67/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_65]) ).
% 0.67/1.01  
% 0.67/1.01  cnf(c_82,plain,
% 0.67/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
% 0.67/1.01      | k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,sK2,X1) ),
% 0.67/1.01      inference(unflattening,[status(thm)],[c_81]) ).
% 0.67/1.01  
% 0.67/1.01  cnf(c_132,plain,
% 0.67/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
% 0.67/1.01      | k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,X0) ),
% 0.67/1.01      inference(instantiation,[status(thm)],[c_82]) ).
% 0.67/1.01  
% 0.67/1.01  cnf(c_154,plain,
% 0.67/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))
% 0.67/1.01      | k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
% 0.67/1.01      inference(instantiation,[status(thm)],[c_132]) ).
% 0.67/1.01  
% 0.67/1.01  cnf(c_98,plain,( X0 = X0 ),theory(equality) ).
% 0.67/1.01  
% 0.67/1.01  cnf(c_131,plain,
% 0.67/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)) ),
% 0.67/1.01      inference(instantiation,[status(thm)],[c_98]) ).
% 0.67/1.01  
% 0.67/1.01  cnf(c_7,negated_conjecture,
% 0.67/1.01      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
% 0.67/1.01      inference(cnf_transformation,[],[f28]) ).
% 0.67/1.01  
% 0.67/1.01  cnf(contradiction,plain,
% 0.67/1.01      ( $false ),
% 0.67/1.01      inference(minisat,[status(thm)],[c_154,c_131,c_7]) ).
% 0.67/1.01  
% 0.67/1.01  
% 0.67/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 0.67/1.01  
% 0.67/1.01  ------                               Statistics
% 0.67/1.01  
% 0.67/1.01  ------ General
% 0.67/1.01  
% 0.67/1.01  abstr_ref_over_cycles:                  0
% 0.67/1.01  abstr_ref_under_cycles:                 0
% 0.67/1.01  gc_basic_clause_elim:                   0
% 0.67/1.01  forced_gc_time:                         0
% 0.67/1.01  parsing_time:                           0.009
% 0.67/1.01  unif_index_cands_time:                  0.
% 0.67/1.01  unif_index_add_time:                    0.
% 0.67/1.01  orderings_time:                         0.
% 0.67/1.01  out_proof_time:                         0.006
% 0.67/1.01  total_time:                             0.045
% 0.67/1.01  num_of_symbols:                         42
% 0.67/1.01  num_of_terms:                           320
% 0.67/1.01  
% 0.67/1.01  ------ Preprocessing
% 0.67/1.01  
% 0.67/1.01  num_of_splits:                          0
% 0.67/1.01  num_of_split_atoms:                     0
% 0.67/1.01  num_of_reused_defs:                     0
% 0.67/1.01  num_eq_ax_congr_red:                    0
% 0.67/1.01  num_of_sem_filtered_clauses:            0
% 0.67/1.01  num_of_subtypes:                        0
% 0.67/1.01  monotx_restored_types:                  0
% 0.67/1.01  sat_num_of_epr_types:                   0
% 0.67/1.01  sat_num_of_non_cyclic_types:            0
% 0.67/1.01  sat_guarded_non_collapsed_types:        0
% 0.67/1.01  num_pure_diseq_elim:                    0
% 0.67/1.01  simp_replaced_by:                       0
% 0.67/1.01  res_preprocessed:                       30
% 0.67/1.01  prep_upred:                             0
% 0.67/1.01  prep_unflattend:                        3
% 0.67/1.01  smt_new_axioms:                         0
% 0.67/1.01  pred_elim_cands:                        0
% 0.67/1.01  pred_elim:                              3
% 0.67/1.01  pred_elim_cl:                           3
% 0.67/1.01  pred_elim_cycles:                       4
% 0.67/1.01  merged_defs:                            0
% 0.67/1.01  merged_defs_ncl:                        0
% 0.67/1.01  bin_hyper_res:                          0
% 0.67/1.01  prep_cycles:                            3
% 0.67/1.01  pred_elim_time:                         0.001
% 0.67/1.01  splitting_time:                         0.
% 0.67/1.01  sem_filter_time:                        0.
% 0.67/1.01  monotx_time:                            0.
% 0.67/1.01  subtype_inf_time:                       0.
% 0.67/1.01  
% 0.67/1.01  ------ Problem properties
% 0.67/1.01  
% 0.67/1.01  clauses:                                7
% 0.67/1.01  conjectures:                            1
% 0.67/1.01  epr:                                    0
% 0.67/1.01  horn:                                   6
% 0.67/1.01  ground:                                 1
% 0.67/1.01  unary:                                  5
% 0.67/1.01  binary:                                 1
% 0.67/1.01  lits:                                   11
% 0.67/1.01  lits_eq:                                11
% 0.67/1.01  fd_pure:                                0
% 0.67/1.01  fd_pseudo:                              0
% 0.67/1.01  fd_cond:                                1
% 0.67/1.01  fd_pseudo_cond:                         0
% 0.67/1.01  ac_symbols:                             0
% 0.67/1.01  
% 0.67/1.01  ------ Propositional Solver
% 0.67/1.01  
% 0.67/1.01  prop_solver_calls:                      19
% 0.67/1.01  prop_fast_solver_calls:                 122
% 0.67/1.01  smt_solver_calls:                       0
% 0.67/1.01  smt_fast_solver_calls:                  0
% 0.67/1.01  prop_num_of_clauses:                    60
% 0.67/1.01  prop_preprocess_simplified:             544
% 0.67/1.01  prop_fo_subsumed:                       1
% 0.67/1.01  prop_solver_time:                       0.
% 0.67/1.01  smt_solver_time:                        0.
% 0.67/1.01  smt_fast_solver_time:                   0.
% 0.67/1.01  prop_fast_solver_time:                  0.
% 0.67/1.01  prop_unsat_core_time:                   0.
% 0.67/1.01  
% 0.67/1.01  ------ QBF
% 0.67/1.01  
% 0.67/1.01  qbf_q_res:                              0
% 0.67/1.01  qbf_num_tautologies:                    0
% 0.67/1.01  qbf_prep_cycles:                        0
% 0.67/1.01  
% 0.67/1.01  ------ BMC1
% 0.67/1.01  
% 0.67/1.01  bmc1_current_bound:                     -1
% 0.67/1.01  bmc1_last_solved_bound:                 -1
% 0.67/1.01  bmc1_unsat_core_size:                   -1
% 0.67/1.01  bmc1_unsat_core_parents_size:           -1
% 0.67/1.01  bmc1_merge_next_fun:                    0
% 0.67/1.01  bmc1_unsat_core_clauses_time:           0.
% 0.67/1.01  
% 0.67/1.01  ------ Instantiation
% 0.67/1.01  
% 0.67/1.01  inst_num_of_clauses:                    23
% 0.67/1.01  inst_num_in_passive:                    2
% 0.67/1.01  inst_num_in_active:                     16
% 0.67/1.01  inst_num_in_unprocessed:                4
% 0.67/1.01  inst_num_of_loops:                      18
% 0.67/1.01  inst_num_of_learning_restarts:          0
% 0.67/1.01  inst_num_moves_active_passive:          0
% 0.67/1.01  inst_lit_activity:                      0
% 0.67/1.01  inst_lit_activity_moves:                0
% 0.67/1.01  inst_num_tautologies:                   0
% 0.67/1.01  inst_num_prop_implied:                  0
% 0.67/1.01  inst_num_existing_simplified:           0
% 0.67/1.01  inst_num_eq_res_simplified:             0
% 0.67/1.01  inst_num_child_elim:                    0
% 0.67/1.01  inst_num_of_dismatching_blockings:      0
% 0.67/1.01  inst_num_of_non_proper_insts:           8
% 0.67/1.01  inst_num_of_duplicates:                 0
% 0.67/1.01  inst_inst_num_from_inst_to_res:         0
% 0.67/1.01  inst_dismatching_checking_time:         0.
% 0.67/1.01  
% 0.67/1.01  ------ Resolution
% 0.67/1.01  
% 0.67/1.01  res_num_of_clauses:                     0
% 0.67/1.01  res_num_in_passive:                     0
% 0.67/1.01  res_num_in_active:                      0
% 0.67/1.01  res_num_of_loops:                       33
% 0.67/1.01  res_forward_subset_subsumed:            1
% 0.67/1.01  res_backward_subset_subsumed:           0
% 0.67/1.01  res_forward_subsumed:                   0
% 0.67/1.01  res_backward_subsumed:                  0
% 0.67/1.01  res_forward_subsumption_resolution:     0
% 0.67/1.01  res_backward_subsumption_resolution:    0
% 0.67/1.01  res_clause_to_clause_subsumption:       13
% 0.67/1.01  res_orphan_elimination:                 0
% 0.67/1.01  res_tautology_del:                      0
% 0.67/1.01  res_num_eq_res_simplified:              0
% 0.67/1.01  res_num_sel_changes:                    0
% 0.67/1.01  res_moves_from_active_to_pass:          0
% 0.67/1.01  
% 0.67/1.01  ------ Superposition
% 0.67/1.01  
% 0.67/1.01  sup_time_total:                         0.
% 0.67/1.01  sup_time_generating:                    0.
% 0.67/1.01  sup_time_sim_full:                      0.
% 0.67/1.01  sup_time_sim_immed:                     0.
% 0.67/1.01  
% 0.67/1.01  sup_num_of_clauses:                     8
% 0.67/1.01  sup_num_in_active:                      2
% 0.67/1.01  sup_num_in_passive:                     6
% 0.67/1.01  sup_num_of_loops:                       2
% 0.67/1.01  sup_fw_superposition:                   0
% 0.67/1.01  sup_bw_superposition:                   0
% 0.67/1.01  sup_immediate_simplified:               0
% 0.67/1.01  sup_given_eliminated:                   0
% 0.67/1.01  comparisons_done:                       0
% 0.67/1.01  comparisons_avoided:                    0
% 0.67/1.01  
% 0.67/1.01  ------ Simplifications
% 0.67/1.01  
% 0.67/1.01  
% 0.67/1.01  sim_fw_subset_subsumed:                 0
% 0.67/1.01  sim_bw_subset_subsumed:                 0
% 0.67/1.01  sim_fw_subsumed:                        0
% 0.67/1.01  sim_bw_subsumed:                        0
% 0.67/1.01  sim_fw_subsumption_res:                 0
% 0.67/1.01  sim_bw_subsumption_res:                 0
% 0.67/1.01  sim_tautology_del:                      0
% 0.67/1.01  sim_eq_tautology_del:                   0
% 0.67/1.01  sim_eq_res_simp:                        0
% 0.67/1.01  sim_fw_demodulated:                     0
% 0.67/1.01  sim_bw_demodulated:                     0
% 0.67/1.01  sim_light_normalised:                   0
% 0.67/1.01  sim_joinable_taut:                      0
% 0.67/1.01  sim_joinable_simp:                      0
% 0.67/1.01  sim_ac_normalised:                      0
% 0.67/1.01  sim_smt_subsumption:                    0
% 0.67/1.01  
%------------------------------------------------------------------------------
