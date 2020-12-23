%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:39 EST 2020

% Result     : Theorem 0.83s
% Output     : CNFRefutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   48 (  54 expanded)
%              Number of clauses        :   23 (  23 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :   11
%              Number of atoms          :  103 ( 125 expanded)
%              Number of equality atoms :   67 (  78 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
      <=> k4_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <~> k4_xboole_0(X0,X1) = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k4_xboole_0(X0,X1) != X0
        | ~ r1_xboole_0(X0,X1) )
      & ( k4_xboole_0(X0,X1) = X0
        | r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( ( k4_xboole_0(X0,X1) != X0
          | ~ r1_xboole_0(X0,X1) )
        & ( k4_xboole_0(X0,X1) = X0
          | r1_xboole_0(X0,X1) ) )
   => ( ( k4_xboole_0(sK0,sK1) != sK0
        | ~ r1_xboole_0(sK0,sK1) )
      & ( k4_xboole_0(sK0,sK1) = sK0
        | r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ( k4_xboole_0(sK0,sK1) != sK0
      | ~ r1_xboole_0(sK0,sK1) )
    & ( k4_xboole_0(sK0,sK1) = sK0
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f25,plain,
    ( k4_xboole_0(sK0,sK1) != sK0
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f17,f22])).

fof(f24,plain,
    ( k4_xboole_0(sK0,sK1) = sK0
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_112,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X3
    | k4_xboole_0(X3,X1) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_4])).

cnf(c_113,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_112])).

cnf(c_210,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_113])).

cnf(c_159,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_178,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) != X0
    | k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != X0 ),
    inference(instantiation,[status(thm)],[c_159])).

cnf(c_209,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) != k1_xboole_0
    | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_178])).

cnf(c_3,plain,
    ( X0 = X1
    | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_175,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | k4_xboole_0(sK0,sK1) = sK0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_6,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,sK1) != sK0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_63,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,sK1) != sK0 ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_143,plain,
    ( k4_xboole_0(X0,X1) != sK0
    | k4_xboole_0(sK0,sK1) != sK0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_63])).

cnf(c_144,plain,
    ( k4_xboole_0(X0,sK1) != sK0
    | k4_xboole_0(sK0,sK1) != sK0 ),
    inference(unflattening,[status(thm)],[c_143])).

cnf(c_145,plain,
    ( k4_xboole_0(sK0,sK1) != sK0 ),
    inference(instantiation,[status(thm)],[c_144])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_61,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_7,negated_conjecture,
    ( r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_65,plain,
    ( r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,sK1) = sK0 ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_135,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | k4_xboole_0(sK0,sK1) = sK0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_61,c_65])).

cnf(c_136,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | k4_xboole_0(sK0,sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_135])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_210,c_209,c_175,c_145,c_136])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 21:00:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.83/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.83/1.01  
% 0.83/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.83/1.01  
% 0.83/1.01  ------  iProver source info
% 0.83/1.01  
% 0.83/1.01  git: date: 2020-06-30 10:37:57 +0100
% 0.83/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.83/1.01  git: non_committed_changes: false
% 0.83/1.01  git: last_make_outside_of_git: false
% 0.83/1.01  
% 0.83/1.01  ------ 
% 0.83/1.01  
% 0.83/1.01  ------ Input Options
% 0.83/1.01  
% 0.83/1.01  --out_options                           all
% 0.83/1.01  --tptp_safe_out                         true
% 0.83/1.01  --problem_path                          ""
% 0.83/1.01  --include_path                          ""
% 0.83/1.01  --clausifier                            res/vclausify_rel
% 0.83/1.01  --clausifier_options                    --mode clausify
% 0.83/1.01  --stdin                                 false
% 0.83/1.01  --stats_out                             all
% 0.83/1.01  
% 0.83/1.01  ------ General Options
% 0.83/1.01  
% 0.83/1.01  --fof                                   false
% 0.83/1.01  --time_out_real                         305.
% 0.83/1.01  --time_out_virtual                      -1.
% 0.83/1.01  --symbol_type_check                     false
% 0.83/1.01  --clausify_out                          false
% 0.83/1.01  --sig_cnt_out                           false
% 0.83/1.01  --trig_cnt_out                          false
% 0.83/1.01  --trig_cnt_out_tolerance                1.
% 0.83/1.01  --trig_cnt_out_sk_spl                   false
% 0.83/1.01  --abstr_cl_out                          false
% 0.83/1.01  
% 0.83/1.01  ------ Global Options
% 0.83/1.01  
% 0.83/1.01  --schedule                              default
% 0.83/1.01  --add_important_lit                     false
% 0.83/1.01  --prop_solver_per_cl                    1000
% 0.83/1.01  --min_unsat_core                        false
% 0.83/1.01  --soft_assumptions                      false
% 0.83/1.01  --soft_lemma_size                       3
% 0.83/1.01  --prop_impl_unit_size                   0
% 0.83/1.01  --prop_impl_unit                        []
% 0.83/1.01  --share_sel_clauses                     true
% 0.83/1.01  --reset_solvers                         false
% 0.83/1.01  --bc_imp_inh                            [conj_cone]
% 0.83/1.01  --conj_cone_tolerance                   3.
% 0.83/1.01  --extra_neg_conj                        none
% 0.83/1.01  --large_theory_mode                     true
% 0.83/1.01  --prolific_symb_bound                   200
% 0.83/1.01  --lt_threshold                          2000
% 0.83/1.01  --clause_weak_htbl                      true
% 0.83/1.01  --gc_record_bc_elim                     false
% 0.83/1.01  
% 0.83/1.01  ------ Preprocessing Options
% 0.83/1.01  
% 0.83/1.01  --preprocessing_flag                    true
% 0.83/1.01  --time_out_prep_mult                    0.1
% 0.83/1.01  --splitting_mode                        input
% 0.83/1.01  --splitting_grd                         true
% 0.83/1.01  --splitting_cvd                         false
% 0.83/1.01  --splitting_cvd_svl                     false
% 0.83/1.01  --splitting_nvd                         32
% 0.83/1.01  --sub_typing                            true
% 0.83/1.01  --prep_gs_sim                           true
% 0.83/1.01  --prep_unflatten                        true
% 0.83/1.01  --prep_res_sim                          true
% 0.83/1.01  --prep_upred                            true
% 0.83/1.01  --prep_sem_filter                       exhaustive
% 0.83/1.01  --prep_sem_filter_out                   false
% 0.83/1.01  --pred_elim                             true
% 0.83/1.01  --res_sim_input                         true
% 0.83/1.01  --eq_ax_congr_red                       true
% 0.83/1.01  --pure_diseq_elim                       true
% 0.83/1.01  --brand_transform                       false
% 0.83/1.01  --non_eq_to_eq                          false
% 0.83/1.01  --prep_def_merge                        true
% 0.83/1.01  --prep_def_merge_prop_impl              false
% 0.83/1.01  --prep_def_merge_mbd                    true
% 0.83/1.01  --prep_def_merge_tr_red                 false
% 0.83/1.01  --prep_def_merge_tr_cl                  false
% 0.83/1.01  --smt_preprocessing                     true
% 0.83/1.01  --smt_ac_axioms                         fast
% 0.83/1.01  --preprocessed_out                      false
% 0.83/1.01  --preprocessed_stats                    false
% 0.83/1.01  
% 0.83/1.01  ------ Abstraction refinement Options
% 0.83/1.01  
% 0.83/1.01  --abstr_ref                             []
% 0.83/1.01  --abstr_ref_prep                        false
% 0.83/1.01  --abstr_ref_until_sat                   false
% 0.83/1.01  --abstr_ref_sig_restrict                funpre
% 0.83/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.83/1.01  --abstr_ref_under                       []
% 0.83/1.01  
% 0.83/1.01  ------ SAT Options
% 0.83/1.01  
% 0.83/1.01  --sat_mode                              false
% 0.83/1.01  --sat_fm_restart_options                ""
% 0.83/1.01  --sat_gr_def                            false
% 0.83/1.01  --sat_epr_types                         true
% 0.83/1.01  --sat_non_cyclic_types                  false
% 0.83/1.01  --sat_finite_models                     false
% 0.83/1.01  --sat_fm_lemmas                         false
% 0.83/1.01  --sat_fm_prep                           false
% 0.83/1.01  --sat_fm_uc_incr                        true
% 0.83/1.01  --sat_out_model                         small
% 0.83/1.01  --sat_out_clauses                       false
% 0.83/1.01  
% 0.83/1.01  ------ QBF Options
% 0.83/1.01  
% 0.83/1.01  --qbf_mode                              false
% 0.83/1.01  --qbf_elim_univ                         false
% 0.83/1.01  --qbf_dom_inst                          none
% 0.83/1.01  --qbf_dom_pre_inst                      false
% 0.83/1.01  --qbf_sk_in                             false
% 0.83/1.01  --qbf_pred_elim                         true
% 0.83/1.01  --qbf_split                             512
% 0.83/1.01  
% 0.83/1.01  ------ BMC1 Options
% 0.83/1.01  
% 0.83/1.01  --bmc1_incremental                      false
% 0.83/1.01  --bmc1_axioms                           reachable_all
% 0.83/1.01  --bmc1_min_bound                        0
% 0.83/1.01  --bmc1_max_bound                        -1
% 0.83/1.01  --bmc1_max_bound_default                -1
% 0.83/1.01  --bmc1_symbol_reachability              true
% 0.83/1.01  --bmc1_property_lemmas                  false
% 0.83/1.01  --bmc1_k_induction                      false
% 0.83/1.01  --bmc1_non_equiv_states                 false
% 0.83/1.01  --bmc1_deadlock                         false
% 0.83/1.01  --bmc1_ucm                              false
% 0.83/1.01  --bmc1_add_unsat_core                   none
% 0.83/1.01  --bmc1_unsat_core_children              false
% 0.83/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.83/1.01  --bmc1_out_stat                         full
% 0.83/1.01  --bmc1_ground_init                      false
% 0.83/1.01  --bmc1_pre_inst_next_state              false
% 0.83/1.01  --bmc1_pre_inst_state                   false
% 0.83/1.01  --bmc1_pre_inst_reach_state             false
% 0.83/1.01  --bmc1_out_unsat_core                   false
% 0.83/1.01  --bmc1_aig_witness_out                  false
% 0.83/1.01  --bmc1_verbose                          false
% 0.83/1.01  --bmc1_dump_clauses_tptp                false
% 0.83/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.83/1.01  --bmc1_dump_file                        -
% 0.83/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.83/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.83/1.01  --bmc1_ucm_extend_mode                  1
% 0.83/1.01  --bmc1_ucm_init_mode                    2
% 0.83/1.01  --bmc1_ucm_cone_mode                    none
% 0.83/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.83/1.01  --bmc1_ucm_relax_model                  4
% 0.83/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.83/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.83/1.01  --bmc1_ucm_layered_model                none
% 0.83/1.01  --bmc1_ucm_max_lemma_size               10
% 0.83/1.01  
% 0.83/1.01  ------ AIG Options
% 0.83/1.01  
% 0.83/1.01  --aig_mode                              false
% 0.83/1.01  
% 0.83/1.01  ------ Instantiation Options
% 0.83/1.01  
% 0.83/1.01  --instantiation_flag                    true
% 0.83/1.01  --inst_sos_flag                         false
% 0.83/1.01  --inst_sos_phase                        true
% 0.83/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.83/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.83/1.01  --inst_lit_sel_side                     num_symb
% 0.83/1.01  --inst_solver_per_active                1400
% 0.83/1.01  --inst_solver_calls_frac                1.
% 0.83/1.01  --inst_passive_queue_type               priority_queues
% 0.83/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.83/1.01  --inst_passive_queues_freq              [25;2]
% 0.83/1.01  --inst_dismatching                      true
% 0.83/1.01  --inst_eager_unprocessed_to_passive     true
% 0.83/1.01  --inst_prop_sim_given                   true
% 0.83/1.01  --inst_prop_sim_new                     false
% 0.83/1.01  --inst_subs_new                         false
% 0.83/1.01  --inst_eq_res_simp                      false
% 0.83/1.01  --inst_subs_given                       false
% 0.83/1.01  --inst_orphan_elimination               true
% 0.83/1.01  --inst_learning_loop_flag               true
% 0.83/1.01  --inst_learning_start                   3000
% 0.83/1.01  --inst_learning_factor                  2
% 0.83/1.01  --inst_start_prop_sim_after_learn       3
% 0.83/1.01  --inst_sel_renew                        solver
% 0.83/1.01  --inst_lit_activity_flag                true
% 0.83/1.01  --inst_restr_to_given                   false
% 0.83/1.01  --inst_activity_threshold               500
% 0.83/1.01  --inst_out_proof                        true
% 0.83/1.01  
% 0.83/1.01  ------ Resolution Options
% 0.83/1.01  
% 0.83/1.01  --resolution_flag                       true
% 0.83/1.01  --res_lit_sel                           adaptive
% 0.83/1.01  --res_lit_sel_side                      none
% 0.83/1.01  --res_ordering                          kbo
% 0.83/1.01  --res_to_prop_solver                    active
% 0.83/1.01  --res_prop_simpl_new                    false
% 0.83/1.01  --res_prop_simpl_given                  true
% 0.83/1.01  --res_passive_queue_type                priority_queues
% 0.83/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.83/1.01  --res_passive_queues_freq               [15;5]
% 0.83/1.01  --res_forward_subs                      full
% 0.83/1.01  --res_backward_subs                     full
% 0.83/1.01  --res_forward_subs_resolution           true
% 0.83/1.01  --res_backward_subs_resolution          true
% 0.83/1.01  --res_orphan_elimination                true
% 0.83/1.01  --res_time_limit                        2.
% 0.83/1.01  --res_out_proof                         true
% 0.83/1.01  
% 0.83/1.01  ------ Superposition Options
% 0.83/1.01  
% 0.83/1.01  --superposition_flag                    true
% 0.83/1.01  --sup_passive_queue_type                priority_queues
% 0.83/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.83/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.83/1.01  --demod_completeness_check              fast
% 0.83/1.01  --demod_use_ground                      true
% 0.83/1.01  --sup_to_prop_solver                    passive
% 0.83/1.01  --sup_prop_simpl_new                    true
% 0.83/1.01  --sup_prop_simpl_given                  true
% 0.83/1.01  --sup_fun_splitting                     false
% 0.83/1.01  --sup_smt_interval                      50000
% 0.83/1.01  
% 0.83/1.01  ------ Superposition Simplification Setup
% 0.83/1.01  
% 0.83/1.01  --sup_indices_passive                   []
% 0.83/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.83/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.01  --sup_full_bw                           [BwDemod]
% 0.83/1.01  --sup_immed_triv                        [TrivRules]
% 0.83/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.83/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.01  --sup_immed_bw_main                     []
% 0.83/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.83/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/1.01  
% 0.83/1.01  ------ Combination Options
% 0.83/1.01  
% 0.83/1.01  --comb_res_mult                         3
% 0.83/1.01  --comb_sup_mult                         2
% 0.83/1.01  --comb_inst_mult                        10
% 0.83/1.01  
% 0.83/1.01  ------ Debug Options
% 0.83/1.01  
% 0.83/1.01  --dbg_backtrace                         false
% 0.83/1.01  --dbg_dump_prop_clauses                 false
% 0.83/1.01  --dbg_dump_prop_clauses_file            -
% 0.83/1.01  --dbg_out_stat                          false
% 0.83/1.01  ------ Parsing...
% 0.83/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.83/1.01  
% 0.83/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.83/1.01  
% 0.83/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.83/1.01  
% 0.83/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.83/1.01  ------ Proving...
% 0.83/1.01  ------ Problem Properties 
% 0.83/1.01  
% 0.83/1.01  
% 0.83/1.01  clauses                                 5
% 0.83/1.01  conjectures                             0
% 0.83/1.01  EPR                                     0
% 0.83/1.01  Horn                                    5
% 0.83/1.01  unary                                   4
% 0.83/1.01  binary                                  1
% 0.83/1.01  lits                                    6
% 0.83/1.01  lits eq                                 6
% 0.83/1.01  fd_pure                                 0
% 0.83/1.01  fd_pseudo                               0
% 0.83/1.01  fd_cond                                 0
% 0.83/1.01  fd_pseudo_cond                          1
% 0.83/1.01  AC symbols                              0
% 0.83/1.01  
% 0.83/1.01  ------ Schedule dynamic 5 is on 
% 0.83/1.01  
% 0.83/1.01  ------ no conjectures: strip conj schedule 
% 0.83/1.01  
% 0.83/1.01  ------ pure equality problem: resolution off 
% 0.83/1.01  
% 0.83/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 0.83/1.01  
% 0.83/1.01  
% 0.83/1.01  ------ 
% 0.83/1.01  Current options:
% 0.83/1.01  ------ 
% 0.83/1.01  
% 0.83/1.01  ------ Input Options
% 0.83/1.01  
% 0.83/1.01  --out_options                           all
% 0.83/1.01  --tptp_safe_out                         true
% 0.83/1.01  --problem_path                          ""
% 0.83/1.01  --include_path                          ""
% 0.83/1.01  --clausifier                            res/vclausify_rel
% 0.83/1.01  --clausifier_options                    --mode clausify
% 0.83/1.01  --stdin                                 false
% 0.83/1.01  --stats_out                             all
% 0.83/1.01  
% 0.83/1.01  ------ General Options
% 0.83/1.01  
% 0.83/1.01  --fof                                   false
% 0.83/1.01  --time_out_real                         305.
% 0.83/1.01  --time_out_virtual                      -1.
% 0.83/1.01  --symbol_type_check                     false
% 0.83/1.01  --clausify_out                          false
% 0.83/1.01  --sig_cnt_out                           false
% 0.83/1.01  --trig_cnt_out                          false
% 0.83/1.01  --trig_cnt_out_tolerance                1.
% 0.83/1.01  --trig_cnt_out_sk_spl                   false
% 0.83/1.01  --abstr_cl_out                          false
% 0.83/1.01  
% 0.83/1.01  ------ Global Options
% 0.83/1.01  
% 0.83/1.01  --schedule                              default
% 0.83/1.01  --add_important_lit                     false
% 0.83/1.01  --prop_solver_per_cl                    1000
% 0.83/1.01  --min_unsat_core                        false
% 0.83/1.01  --soft_assumptions                      false
% 0.83/1.01  --soft_lemma_size                       3
% 0.83/1.01  --prop_impl_unit_size                   0
% 0.83/1.01  --prop_impl_unit                        []
% 0.83/1.01  --share_sel_clauses                     true
% 0.83/1.01  --reset_solvers                         false
% 0.83/1.01  --bc_imp_inh                            [conj_cone]
% 0.83/1.01  --conj_cone_tolerance                   3.
% 0.83/1.01  --extra_neg_conj                        none
% 0.83/1.01  --large_theory_mode                     true
% 0.83/1.01  --prolific_symb_bound                   200
% 0.83/1.01  --lt_threshold                          2000
% 0.83/1.01  --clause_weak_htbl                      true
% 0.83/1.01  --gc_record_bc_elim                     false
% 0.83/1.01  
% 0.83/1.01  ------ Preprocessing Options
% 0.83/1.01  
% 0.83/1.01  --preprocessing_flag                    true
% 0.83/1.01  --time_out_prep_mult                    0.1
% 0.83/1.01  --splitting_mode                        input
% 0.83/1.01  --splitting_grd                         true
% 0.83/1.01  --splitting_cvd                         false
% 0.83/1.01  --splitting_cvd_svl                     false
% 0.83/1.01  --splitting_nvd                         32
% 0.83/1.01  --sub_typing                            true
% 0.83/1.01  --prep_gs_sim                           true
% 0.83/1.01  --prep_unflatten                        true
% 0.83/1.01  --prep_res_sim                          true
% 0.83/1.01  --prep_upred                            true
% 0.83/1.01  --prep_sem_filter                       exhaustive
% 0.83/1.01  --prep_sem_filter_out                   false
% 0.83/1.01  --pred_elim                             true
% 0.83/1.01  --res_sim_input                         true
% 0.83/1.01  --eq_ax_congr_red                       true
% 0.83/1.01  --pure_diseq_elim                       true
% 0.83/1.01  --brand_transform                       false
% 0.83/1.01  --non_eq_to_eq                          false
% 0.83/1.01  --prep_def_merge                        true
% 0.83/1.01  --prep_def_merge_prop_impl              false
% 0.83/1.01  --prep_def_merge_mbd                    true
% 0.83/1.01  --prep_def_merge_tr_red                 false
% 0.83/1.01  --prep_def_merge_tr_cl                  false
% 0.83/1.01  --smt_preprocessing                     true
% 0.83/1.01  --smt_ac_axioms                         fast
% 0.83/1.01  --preprocessed_out                      false
% 0.83/1.01  --preprocessed_stats                    false
% 0.83/1.01  
% 0.83/1.01  ------ Abstraction refinement Options
% 0.83/1.01  
% 0.83/1.01  --abstr_ref                             []
% 0.83/1.01  --abstr_ref_prep                        false
% 0.83/1.01  --abstr_ref_until_sat                   false
% 0.83/1.01  --abstr_ref_sig_restrict                funpre
% 0.83/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.83/1.01  --abstr_ref_under                       []
% 0.83/1.01  
% 0.83/1.01  ------ SAT Options
% 0.83/1.01  
% 0.83/1.01  --sat_mode                              false
% 0.83/1.01  --sat_fm_restart_options                ""
% 0.83/1.01  --sat_gr_def                            false
% 0.83/1.01  --sat_epr_types                         true
% 0.83/1.01  --sat_non_cyclic_types                  false
% 0.83/1.01  --sat_finite_models                     false
% 0.83/1.01  --sat_fm_lemmas                         false
% 0.83/1.01  --sat_fm_prep                           false
% 0.83/1.01  --sat_fm_uc_incr                        true
% 0.83/1.01  --sat_out_model                         small
% 0.83/1.01  --sat_out_clauses                       false
% 0.83/1.01  
% 0.83/1.01  ------ QBF Options
% 0.83/1.01  
% 0.83/1.01  --qbf_mode                              false
% 0.83/1.01  --qbf_elim_univ                         false
% 0.83/1.01  --qbf_dom_inst                          none
% 0.83/1.01  --qbf_dom_pre_inst                      false
% 0.83/1.01  --qbf_sk_in                             false
% 0.83/1.01  --qbf_pred_elim                         true
% 0.83/1.01  --qbf_split                             512
% 0.83/1.01  
% 0.83/1.01  ------ BMC1 Options
% 0.83/1.01  
% 0.83/1.01  --bmc1_incremental                      false
% 0.83/1.01  --bmc1_axioms                           reachable_all
% 0.83/1.01  --bmc1_min_bound                        0
% 0.83/1.01  --bmc1_max_bound                        -1
% 0.83/1.01  --bmc1_max_bound_default                -1
% 0.83/1.01  --bmc1_symbol_reachability              true
% 0.83/1.01  --bmc1_property_lemmas                  false
% 0.83/1.01  --bmc1_k_induction                      false
% 0.83/1.01  --bmc1_non_equiv_states                 false
% 0.83/1.01  --bmc1_deadlock                         false
% 0.83/1.01  --bmc1_ucm                              false
% 0.83/1.01  --bmc1_add_unsat_core                   none
% 0.83/1.01  --bmc1_unsat_core_children              false
% 0.83/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.83/1.01  --bmc1_out_stat                         full
% 0.83/1.01  --bmc1_ground_init                      false
% 0.83/1.01  --bmc1_pre_inst_next_state              false
% 0.83/1.01  --bmc1_pre_inst_state                   false
% 0.83/1.01  --bmc1_pre_inst_reach_state             false
% 0.83/1.01  --bmc1_out_unsat_core                   false
% 0.83/1.01  --bmc1_aig_witness_out                  false
% 0.83/1.01  --bmc1_verbose                          false
% 0.83/1.01  --bmc1_dump_clauses_tptp                false
% 0.83/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.83/1.01  --bmc1_dump_file                        -
% 0.83/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.83/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.83/1.01  --bmc1_ucm_extend_mode                  1
% 0.83/1.01  --bmc1_ucm_init_mode                    2
% 0.83/1.01  --bmc1_ucm_cone_mode                    none
% 0.83/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.83/1.01  --bmc1_ucm_relax_model                  4
% 0.83/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.83/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.83/1.01  --bmc1_ucm_layered_model                none
% 0.83/1.01  --bmc1_ucm_max_lemma_size               10
% 0.83/1.01  
% 0.83/1.01  ------ AIG Options
% 0.83/1.01  
% 0.83/1.01  --aig_mode                              false
% 0.83/1.01  
% 0.83/1.01  ------ Instantiation Options
% 0.83/1.01  
% 0.83/1.01  --instantiation_flag                    true
% 0.83/1.01  --inst_sos_flag                         false
% 0.83/1.01  --inst_sos_phase                        true
% 0.83/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.83/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.83/1.01  --inst_lit_sel_side                     none
% 0.83/1.01  --inst_solver_per_active                1400
% 0.83/1.01  --inst_solver_calls_frac                1.
% 0.83/1.01  --inst_passive_queue_type               priority_queues
% 0.83/1.01  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 0.83/1.01  --inst_passive_queues_freq              [25;2]
% 0.83/1.01  --inst_dismatching                      true
% 0.83/1.01  --inst_eager_unprocessed_to_passive     true
% 0.83/1.01  --inst_prop_sim_given                   true
% 0.83/1.01  --inst_prop_sim_new                     false
% 0.83/1.01  --inst_subs_new                         false
% 0.83/1.01  --inst_eq_res_simp                      false
% 0.83/1.01  --inst_subs_given                       false
% 0.83/1.01  --inst_orphan_elimination               true
% 0.83/1.01  --inst_learning_loop_flag               true
% 0.83/1.01  --inst_learning_start                   3000
% 0.83/1.01  --inst_learning_factor                  2
% 0.83/1.01  --inst_start_prop_sim_after_learn       3
% 0.83/1.01  --inst_sel_renew                        solver
% 0.83/1.01  --inst_lit_activity_flag                true
% 0.83/1.01  --inst_restr_to_given                   false
% 0.83/1.01  --inst_activity_threshold               500
% 0.83/1.01  --inst_out_proof                        true
% 0.83/1.01  
% 0.83/1.01  ------ Resolution Options
% 0.83/1.01  
% 0.83/1.01  --resolution_flag                       false
% 0.83/1.01  --res_lit_sel                           adaptive
% 0.83/1.01  --res_lit_sel_side                      none
% 0.83/1.01  --res_ordering                          kbo
% 0.83/1.01  --res_to_prop_solver                    active
% 0.83/1.01  --res_prop_simpl_new                    false
% 0.83/1.01  --res_prop_simpl_given                  true
% 0.83/1.01  --res_passive_queue_type                priority_queues
% 0.83/1.01  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 0.83/1.01  --res_passive_queues_freq               [15;5]
% 0.83/1.01  --res_forward_subs                      full
% 0.83/1.01  --res_backward_subs                     full
% 0.83/1.01  --res_forward_subs_resolution           true
% 0.83/1.01  --res_backward_subs_resolution          true
% 0.83/1.01  --res_orphan_elimination                true
% 0.83/1.01  --res_time_limit                        2.
% 0.83/1.01  --res_out_proof                         true
% 0.83/1.01  
% 0.83/1.01  ------ Superposition Options
% 0.83/1.01  
% 0.83/1.01  --superposition_flag                    true
% 0.83/1.01  --sup_passive_queue_type                priority_queues
% 0.83/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.83/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.83/1.01  --demod_completeness_check              fast
% 0.83/1.01  --demod_use_ground                      true
% 0.83/1.01  --sup_to_prop_solver                    passive
% 0.83/1.01  --sup_prop_simpl_new                    true
% 0.83/1.01  --sup_prop_simpl_given                  true
% 0.83/1.01  --sup_fun_splitting                     false
% 0.83/1.01  --sup_smt_interval                      50000
% 0.83/1.01  
% 0.83/1.01  ------ Superposition Simplification Setup
% 0.83/1.01  
% 0.83/1.01  --sup_indices_passive                   []
% 0.83/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.83/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.83/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.01  --sup_full_bw                           [BwDemod]
% 0.83/1.01  --sup_immed_triv                        [TrivRules]
% 0.83/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.83/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.01  --sup_immed_bw_main                     []
% 0.83/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.83/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.83/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.83/1.01  
% 0.83/1.01  ------ Combination Options
% 0.83/1.01  
% 0.83/1.01  --comb_res_mult                         3
% 0.83/1.01  --comb_sup_mult                         2
% 0.83/1.01  --comb_inst_mult                        10
% 0.83/1.01  
% 0.83/1.01  ------ Debug Options
% 0.83/1.01  
% 0.83/1.01  --dbg_backtrace                         false
% 0.83/1.01  --dbg_dump_prop_clauses                 false
% 0.83/1.01  --dbg_dump_prop_clauses_file            -
% 0.83/1.01  --dbg_out_stat                          false
% 0.83/1.01  
% 0.83/1.01  
% 0.83/1.01  
% 0.83/1.01  
% 0.83/1.01  ------ Proving...
% 0.83/1.01  
% 0.83/1.01  
% 0.83/1.01  % SZS status Theorem for theBenchmark.p
% 0.83/1.01  
% 0.83/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 0.83/1.01  
% 0.83/1.01  fof(f2,axiom,(
% 0.83/1.01    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.83/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.01  
% 0.83/1.01  fof(f9,plain,(
% 0.83/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k1_xboole_0 = k4_xboole_0(X0,X1))),
% 0.83/1.01    inference(unused_predicate_definition_removal,[],[f2])).
% 0.83/1.01  
% 0.83/1.01  fof(f10,plain,(
% 0.83/1.01    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.83/1.01    inference(ennf_transformation,[],[f9])).
% 0.83/1.01  
% 0.83/1.01  fof(f19,plain,(
% 0.83/1.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.83/1.01    inference(cnf_transformation,[],[f10])).
% 0.83/1.01  
% 0.83/1.01  fof(f4,axiom,(
% 0.83/1.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.83/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.01  
% 0.83/1.01  fof(f21,plain,(
% 0.83/1.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.83/1.01    inference(cnf_transformation,[],[f4])).
% 0.83/1.01  
% 0.83/1.01  fof(f3,axiom,(
% 0.83/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 0.83/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.01  
% 0.83/1.01  fof(f11,plain,(
% 0.83/1.01    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 0.83/1.01    inference(ennf_transformation,[],[f3])).
% 0.83/1.01  
% 0.83/1.01  fof(f20,plain,(
% 0.83/1.01    ( ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)) )),
% 0.83/1.01    inference(cnf_transformation,[],[f11])).
% 0.83/1.01  
% 0.83/1.01  fof(f6,axiom,(
% 0.83/1.01    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.83/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.01  
% 0.83/1.01  fof(f23,plain,(
% 0.83/1.01    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.83/1.01    inference(cnf_transformation,[],[f6])).
% 0.83/1.01  
% 0.83/1.01  fof(f7,conjecture,(
% 0.83/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.83/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.01  
% 0.83/1.01  fof(f8,negated_conjecture,(
% 0.83/1.01    ~! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.83/1.01    inference(negated_conjecture,[],[f7])).
% 0.83/1.01  
% 0.83/1.01  fof(f12,plain,(
% 0.83/1.01    ? [X0,X1] : (r1_xboole_0(X0,X1) <~> k4_xboole_0(X0,X1) = X0)),
% 0.83/1.01    inference(ennf_transformation,[],[f8])).
% 0.83/1.01  
% 0.83/1.01  fof(f14,plain,(
% 0.83/1.01    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1)))),
% 0.83/1.01    inference(nnf_transformation,[],[f12])).
% 0.83/1.01  
% 0.83/1.01  fof(f15,plain,(
% 0.83/1.01    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1))) => ((k4_xboole_0(sK0,sK1) != sK0 | ~r1_xboole_0(sK0,sK1)) & (k4_xboole_0(sK0,sK1) = sK0 | r1_xboole_0(sK0,sK1)))),
% 0.83/1.01    introduced(choice_axiom,[])).
% 0.83/1.01  
% 0.83/1.01  fof(f16,plain,(
% 0.83/1.01    (k4_xboole_0(sK0,sK1) != sK0 | ~r1_xboole_0(sK0,sK1)) & (k4_xboole_0(sK0,sK1) = sK0 | r1_xboole_0(sK0,sK1))),
% 0.83/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 0.83/1.01  
% 0.83/1.01  fof(f25,plain,(
% 0.83/1.01    k4_xboole_0(sK0,sK1) != sK0 | ~r1_xboole_0(sK0,sK1)),
% 0.83/1.01    inference(cnf_transformation,[],[f16])).
% 0.83/1.01  
% 0.83/1.01  fof(f1,axiom,(
% 0.83/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.83/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.01  
% 0.83/1.01  fof(f13,plain,(
% 0.83/1.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.83/1.01    inference(nnf_transformation,[],[f1])).
% 0.83/1.01  
% 0.83/1.01  fof(f17,plain,(
% 0.83/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.83/1.01    inference(cnf_transformation,[],[f13])).
% 0.83/1.01  
% 0.83/1.01  fof(f5,axiom,(
% 0.83/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.83/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.83/1.01  
% 0.83/1.01  fof(f22,plain,(
% 0.83/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.83/1.01    inference(cnf_transformation,[],[f5])).
% 0.83/1.01  
% 0.83/1.01  fof(f27,plain,(
% 0.83/1.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.83/1.01    inference(definition_unfolding,[],[f17,f22])).
% 0.83/1.01  
% 0.83/1.01  fof(f24,plain,(
% 0.83/1.01    k4_xboole_0(sK0,sK1) = sK0 | r1_xboole_0(sK0,sK1)),
% 0.83/1.01    inference(cnf_transformation,[],[f16])).
% 0.83/1.01  
% 0.83/1.01  cnf(c_2,plain,
% 0.83/1.01      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 0.83/1.01      inference(cnf_transformation,[],[f19]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_4,plain,
% 0.83/1.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 0.83/1.01      inference(cnf_transformation,[],[f21]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_112,plain,
% 0.83/1.01      ( X0 != X1
% 0.83/1.01      | k4_xboole_0(X0,X2) != X3
% 0.83/1.01      | k4_xboole_0(X3,X1) = k1_xboole_0 ),
% 0.83/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_4]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_113,plain,
% 0.83/1.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 0.83/1.01      inference(unflattening,[status(thm)],[c_112]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_210,plain,
% 0.83/1.01      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k1_xboole_0 ),
% 0.83/1.01      inference(instantiation,[status(thm)],[c_113]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_159,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_178,plain,
% 0.83/1.01      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) != X0
% 0.83/1.01      | k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
% 0.83/1.01      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != X0 ),
% 0.83/1.01      inference(instantiation,[status(thm)],[c_159]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_209,plain,
% 0.83/1.01      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
% 0.83/1.01      | k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) != k1_xboole_0
% 0.83/1.01      | k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k1_xboole_0 ),
% 0.83/1.01      inference(instantiation,[status(thm)],[c_178]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_3,plain,
% 0.83/1.01      ( X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
% 0.83/1.01      inference(cnf_transformation,[],[f20]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_175,plain,
% 0.83/1.01      ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
% 0.83/1.01      | k4_xboole_0(sK0,sK1) = sK0 ),
% 0.83/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_5,plain,
% 0.83/1.01      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 0.83/1.01      inference(cnf_transformation,[],[f23]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_6,negated_conjecture,
% 0.83/1.01      ( ~ r1_xboole_0(sK0,sK1) | k4_xboole_0(sK0,sK1) != sK0 ),
% 0.83/1.01      inference(cnf_transformation,[],[f25]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_63,plain,
% 0.83/1.01      ( ~ r1_xboole_0(sK0,sK1) | k4_xboole_0(sK0,sK1) != sK0 ),
% 0.83/1.01      inference(prop_impl,[status(thm)],[c_6]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_143,plain,
% 0.83/1.01      ( k4_xboole_0(X0,X1) != sK0
% 0.83/1.01      | k4_xboole_0(sK0,sK1) != sK0
% 0.83/1.01      | sK1 != X1 ),
% 0.83/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_63]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_144,plain,
% 0.83/1.01      ( k4_xboole_0(X0,sK1) != sK0 | k4_xboole_0(sK0,sK1) != sK0 ),
% 0.83/1.01      inference(unflattening,[status(thm)],[c_143]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_145,plain,
% 0.83/1.01      ( k4_xboole_0(sK0,sK1) != sK0 ),
% 0.83/1.01      inference(instantiation,[status(thm)],[c_144]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_1,plain,
% 0.83/1.01      ( ~ r1_xboole_0(X0,X1)
% 0.83/1.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 0.83/1.01      inference(cnf_transformation,[],[f27]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_61,plain,
% 0.83/1.01      ( ~ r1_xboole_0(X0,X1)
% 0.83/1.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 0.83/1.01      inference(prop_impl,[status(thm)],[c_1]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_7,negated_conjecture,
% 0.83/1.01      ( r1_xboole_0(sK0,sK1) | k4_xboole_0(sK0,sK1) = sK0 ),
% 0.83/1.01      inference(cnf_transformation,[],[f24]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_65,plain,
% 0.83/1.01      ( r1_xboole_0(sK0,sK1) | k4_xboole_0(sK0,sK1) = sK0 ),
% 0.83/1.01      inference(prop_impl,[status(thm)],[c_7]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_135,plain,
% 0.83/1.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 0.83/1.01      | k4_xboole_0(sK0,sK1) = sK0
% 0.83/1.01      | sK1 != X1
% 0.83/1.01      | sK0 != X0 ),
% 0.83/1.01      inference(resolution_lifted,[status(thm)],[c_61,c_65]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(c_136,plain,
% 0.83/1.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 0.83/1.01      | k4_xboole_0(sK0,sK1) = sK0 ),
% 0.83/1.01      inference(unflattening,[status(thm)],[c_135]) ).
% 0.83/1.01  
% 0.83/1.01  cnf(contradiction,plain,
% 0.83/1.01      ( $false ),
% 0.83/1.01      inference(minisat,[status(thm)],[c_210,c_209,c_175,c_145,c_136]) ).
% 0.83/1.01  
% 0.83/1.01  
% 0.83/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 0.83/1.01  
% 0.83/1.01  ------                               Statistics
% 0.83/1.01  
% 0.83/1.01  ------ General
% 0.83/1.01  
% 0.83/1.01  abstr_ref_over_cycles:                  0
% 0.83/1.01  abstr_ref_under_cycles:                 0
% 0.83/1.01  gc_basic_clause_elim:                   0
% 0.83/1.01  forced_gc_time:                         0
% 0.83/1.01  parsing_time:                           0.009
% 0.83/1.01  unif_index_cands_time:                  0.
% 0.83/1.01  unif_index_add_time:                    0.
% 0.83/1.01  orderings_time:                         0.
% 0.83/1.01  out_proof_time:                         0.015
% 0.83/1.01  total_time:                             0.047
% 0.83/1.01  num_of_symbols:                         37
% 0.83/1.01  num_of_terms:                           270
% 0.83/1.01  
% 0.83/1.01  ------ Preprocessing
% 0.83/1.01  
% 0.83/1.01  num_of_splits:                          0
% 0.83/1.01  num_of_split_atoms:                     0
% 0.83/1.01  num_of_reused_defs:                     0
% 0.83/1.01  num_eq_ax_congr_red:                    1
% 0.83/1.01  num_of_sem_filtered_clauses:            0
% 0.83/1.01  num_of_subtypes:                        0
% 0.83/1.01  monotx_restored_types:                  0
% 0.83/1.01  sat_num_of_epr_types:                   0
% 0.83/1.01  sat_num_of_non_cyclic_types:            0
% 0.83/1.01  sat_guarded_non_collapsed_types:        0
% 0.83/1.01  num_pure_diseq_elim:                    0
% 0.83/1.01  simp_replaced_by:                       0
% 0.83/1.01  res_preprocessed:                       21
% 0.83/1.01  prep_upred:                             0
% 0.83/1.01  prep_unflattend:                        9
% 0.83/1.01  smt_new_axioms:                         0
% 0.83/1.01  pred_elim_cands:                        0
% 0.83/1.01  pred_elim:                              2
% 0.83/1.01  pred_elim_cl:                           3
% 0.83/1.01  pred_elim_cycles:                       3
% 0.83/1.01  merged_defs:                            4
% 0.83/1.01  merged_defs_ncl:                        0
% 0.83/1.01  bin_hyper_res:                          4
% 0.83/1.01  prep_cycles:                            3
% 0.83/1.01  pred_elim_time:                         0.001
% 0.83/1.01  splitting_time:                         0.
% 0.83/1.01  sem_filter_time:                        0.
% 0.83/1.01  monotx_time:                            0.001
% 0.83/1.01  subtype_inf_time:                       0.
% 0.83/1.01  
% 0.83/1.01  ------ Problem properties
% 0.83/1.01  
% 0.83/1.01  clauses:                                5
% 0.83/1.01  conjectures:                            0
% 0.83/1.01  epr:                                    0
% 0.83/1.01  horn:                                   5
% 0.83/1.01  ground:                                 2
% 0.83/1.01  unary:                                  4
% 0.83/1.01  binary:                                 1
% 0.83/1.01  lits:                                   6
% 0.83/1.01  lits_eq:                                6
% 0.83/1.01  fd_pure:                                0
% 0.83/1.01  fd_pseudo:                              0
% 0.83/1.01  fd_cond:                                0
% 0.83/1.01  fd_pseudo_cond:                         1
% 0.83/1.01  ac_symbols:                             0
% 0.83/1.01  
% 0.83/1.01  ------ Propositional Solver
% 0.83/1.01  
% 0.83/1.01  prop_solver_calls:                      20
% 0.83/1.01  prop_fast_solver_calls:                 77
% 0.83/1.01  smt_solver_calls:                       0
% 0.83/1.01  smt_fast_solver_calls:                  0
% 0.83/1.01  prop_num_of_clauses:                    70
% 0.83/1.01  prop_preprocess_simplified:             466
% 0.83/1.01  prop_fo_subsumed:                       1
% 0.83/1.01  prop_solver_time:                       0.
% 0.83/1.01  smt_solver_time:                        0.
% 0.83/1.01  smt_fast_solver_time:                   0.
% 0.83/1.01  prop_fast_solver_time:                  0.
% 0.83/1.01  prop_unsat_core_time:                   0.
% 0.83/1.01  
% 0.83/1.01  ------ QBF
% 0.83/1.01  
% 0.83/1.01  qbf_q_res:                              0
% 0.83/1.01  qbf_num_tautologies:                    0
% 0.83/1.01  qbf_prep_cycles:                        0
% 0.83/1.01  
% 0.83/1.01  ------ BMC1
% 0.83/1.01  
% 0.83/1.01  bmc1_current_bound:                     -1
% 0.83/1.01  bmc1_last_solved_bound:                 -1
% 0.83/1.01  bmc1_unsat_core_size:                   -1
% 0.83/1.01  bmc1_unsat_core_parents_size:           -1
% 0.83/1.01  bmc1_merge_next_fun:                    0
% 0.83/1.01  bmc1_unsat_core_clauses_time:           0.
% 0.83/1.01  
% 0.83/1.01  ------ Instantiation
% 0.83/1.01  
% 0.83/1.01  inst_num_of_clauses:                    30
% 0.83/1.01  inst_num_in_passive:                    4
% 0.83/1.01  inst_num_in_active:                     13
% 0.83/1.01  inst_num_in_unprocessed:                12
% 0.83/1.01  inst_num_of_loops:                      15
% 0.83/1.01  inst_num_of_learning_restarts:          0
% 0.83/1.01  inst_num_moves_active_passive:          0
% 0.83/1.01  inst_lit_activity:                      0
% 0.83/1.01  inst_lit_activity_moves:                0
% 0.83/1.01  inst_num_tautologies:                   0
% 0.83/1.01  inst_num_prop_implied:                  0
% 0.83/1.01  inst_num_existing_simplified:           0
% 0.83/1.01  inst_num_eq_res_simplified:             0
% 0.83/1.01  inst_num_child_elim:                    0
% 0.83/1.01  inst_num_of_dismatching_blockings:      0
% 0.83/1.01  inst_num_of_non_proper_insts:           15
% 0.83/1.01  inst_num_of_duplicates:                 0
% 0.83/1.01  inst_inst_num_from_inst_to_res:         0
% 0.83/1.01  inst_dismatching_checking_time:         0.
% 0.83/1.01  
% 0.83/1.01  ------ Resolution
% 0.83/1.01  
% 0.83/1.01  res_num_of_clauses:                     0
% 0.83/1.01  res_num_in_passive:                     0
% 0.83/1.01  res_num_in_active:                      0
% 0.83/1.01  res_num_of_loops:                       24
% 0.83/1.01  res_forward_subset_subsumed:            1
% 0.83/1.01  res_backward_subset_subsumed:           0
% 0.83/1.01  res_forward_subsumed:                   0
% 0.83/1.01  res_backward_subsumed:                  1
% 0.83/1.01  res_forward_subsumption_resolution:     0
% 0.83/1.01  res_backward_subsumption_resolution:    1
% 0.83/1.01  res_clause_to_clause_subsumption:       16
% 0.83/1.01  res_orphan_elimination:                 0
% 0.83/1.01  res_tautology_del:                      10
% 0.83/1.01  res_num_eq_res_simplified:              0
% 0.83/1.01  res_num_sel_changes:                    0
% 0.83/1.01  res_moves_from_active_to_pass:          0
% 0.83/1.01  
% 0.83/1.01  ------ Superposition
% 0.83/1.01  
% 0.83/1.01  sup_time_total:                         0.
% 0.83/1.01  sup_time_generating:                    0.
% 0.83/1.01  sup_time_sim_full:                      0.
% 0.83/1.01  sup_time_sim_immed:                     0.
% 0.83/1.01  
% 0.83/1.01  sup_num_of_clauses:                     6
% 0.83/1.01  sup_num_in_active:                      2
% 0.83/1.01  sup_num_in_passive:                     4
% 0.83/1.01  sup_num_of_loops:                       2
% 0.83/1.01  sup_fw_superposition:                   1
% 0.83/1.01  sup_bw_superposition:                   1
% 0.83/1.01  sup_immediate_simplified:               0
% 0.83/1.01  sup_given_eliminated:                   0
% 0.83/1.01  comparisons_done:                       0
% 0.83/1.01  comparisons_avoided:                    0
% 0.83/1.01  
% 0.83/1.01  ------ Simplifications
% 0.83/1.01  
% 0.83/1.01  
% 0.83/1.01  sim_fw_subset_subsumed:                 0
% 0.83/1.01  sim_bw_subset_subsumed:                 0
% 0.83/1.01  sim_fw_subsumed:                        0
% 0.83/1.01  sim_bw_subsumed:                        0
% 0.83/1.01  sim_fw_subsumption_res:                 0
% 0.83/1.01  sim_bw_subsumption_res:                 0
% 0.83/1.01  sim_tautology_del:                      0
% 0.83/1.01  sim_eq_tautology_del:                   0
% 0.83/1.01  sim_eq_res_simp:                        0
% 0.83/1.01  sim_fw_demodulated:                     0
% 0.83/1.01  sim_bw_demodulated:                     0
% 0.83/1.01  sim_light_normalised:                   0
% 0.83/1.01  sim_joinable_taut:                      0
% 0.83/1.01  sim_joinable_simp:                      0
% 0.83/1.01  sim_ac_normalised:                      0
% 0.83/1.01  sim_smt_subsumption:                    0
% 0.83/1.01  
%------------------------------------------------------------------------------
