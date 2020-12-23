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
% DateTime   : Thu Dec  3 11:30:14 EST 2020

% Result     : Theorem 0.58s
% Output     : CNFRefutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   42 (  68 expanded)
%              Number of clauses        :   17 (  17 expanded)
%              Number of leaves         :    6 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 134 expanded)
%              Number of equality atoms :   68 ( 111 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f18,f16,f16])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
      <=> X0 != X1 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <~> X0 != X1 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( X0 = X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ( X0 = X1
          | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) )
        & ( X0 != X1
          | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) )
   => ( ( sK0 = sK1
        | k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(sK0) )
      & ( sK0 != sK1
        | k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ( sK0 = sK1
      | k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(sK0) )
    & ( sK0 != sK1
      | k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f20,plain,
    ( sK0 = sK1
    | k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f23,plain,
    ( sK0 = sK1
    | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f20,f16,f16,f16])).

fof(f19,plain,
    ( sK0 != sK1
    | k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f24,plain,
    ( sK0 != sK1
    | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f19,f16,f16,f16])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( X0 = X1
        & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f17,f16,f16])).

fof(f25,plain,(
    ! [X1] : ~ r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1)) ),
    inference(equality_resolution,[],[f21])).

cnf(c_3,plain,
    ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
    | X1 = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_268,plain,
    ( X0 = X1
    | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_270,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_405,plain,
    ( X0 = X1
    | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(X0,X0,X0,X0) ),
    inference(superposition,[status(thm)],[c_268,c_270])).

cnf(c_4,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 = sK1 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_460,plain,
    ( sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_405,c_4])).

cnf(c_5,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) = k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_464,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) = k2_enumset1(sK0,sK0,sK0,sK0)
    | sK0 != sK0 ),
    inference(demodulation,[status(thm)],[c_460,c_5])).

cnf(c_466,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(equality_resolution_simp,[status(thm)],[c_464])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_37,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_79,plain,
    ( k2_enumset1(X0,X0,X0,X0) != X1
    | k2_enumset1(X0,X0,X0,X0) != X2
    | k4_xboole_0(X2,X1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_2])).

cnf(c_80,plain,
    ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
    inference(unflattening,[status(thm)],[c_79])).

cnf(c_81,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_80])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_466,c_81])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:09:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 0.58/0.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.58/0.92  
% 0.58/0.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.58/0.92  
% 0.58/0.92  ------  iProver source info
% 0.58/0.92  
% 0.58/0.92  git: date: 2020-06-30 10:37:57 +0100
% 0.58/0.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.58/0.92  git: non_committed_changes: false
% 0.58/0.92  git: last_make_outside_of_git: false
% 0.58/0.92  
% 0.58/0.92  ------ 
% 0.58/0.92  
% 0.58/0.92  ------ Input Options
% 0.58/0.92  
% 0.58/0.92  --out_options                           all
% 0.58/0.92  --tptp_safe_out                         true
% 0.58/0.92  --problem_path                          ""
% 0.58/0.92  --include_path                          ""
% 0.58/0.92  --clausifier                            res/vclausify_rel
% 0.58/0.92  --clausifier_options                    --mode clausify
% 0.58/0.92  --stdin                                 false
% 0.58/0.92  --stats_out                             all
% 0.58/0.92  
% 0.58/0.92  ------ General Options
% 0.58/0.92  
% 0.58/0.92  --fof                                   false
% 0.58/0.92  --time_out_real                         305.
% 0.58/0.92  --time_out_virtual                      -1.
% 0.58/0.92  --symbol_type_check                     false
% 0.58/0.92  --clausify_out                          false
% 0.58/0.92  --sig_cnt_out                           false
% 0.58/0.92  --trig_cnt_out                          false
% 0.58/0.92  --trig_cnt_out_tolerance                1.
% 0.58/0.92  --trig_cnt_out_sk_spl                   false
% 0.58/0.92  --abstr_cl_out                          false
% 0.58/0.92  
% 0.58/0.92  ------ Global Options
% 0.58/0.92  
% 0.58/0.92  --schedule                              default
% 0.58/0.92  --add_important_lit                     false
% 0.58/0.92  --prop_solver_per_cl                    1000
% 0.58/0.92  --min_unsat_core                        false
% 0.58/0.92  --soft_assumptions                      false
% 0.58/0.92  --soft_lemma_size                       3
% 0.58/0.92  --prop_impl_unit_size                   0
% 0.58/0.92  --prop_impl_unit                        []
% 0.58/0.92  --share_sel_clauses                     true
% 0.58/0.92  --reset_solvers                         false
% 0.58/0.92  --bc_imp_inh                            [conj_cone]
% 0.58/0.92  --conj_cone_tolerance                   3.
% 0.58/0.92  --extra_neg_conj                        none
% 0.58/0.92  --large_theory_mode                     true
% 0.58/0.92  --prolific_symb_bound                   200
% 0.58/0.92  --lt_threshold                          2000
% 0.58/0.92  --clause_weak_htbl                      true
% 0.58/0.92  --gc_record_bc_elim                     false
% 0.58/0.92  
% 0.58/0.92  ------ Preprocessing Options
% 0.58/0.92  
% 0.58/0.92  --preprocessing_flag                    true
% 0.58/0.92  --time_out_prep_mult                    0.1
% 0.58/0.92  --splitting_mode                        input
% 0.58/0.92  --splitting_grd                         true
% 0.58/0.92  --splitting_cvd                         false
% 0.58/0.92  --splitting_cvd_svl                     false
% 0.58/0.92  --splitting_nvd                         32
% 0.58/0.92  --sub_typing                            true
% 0.58/0.92  --prep_gs_sim                           true
% 0.58/0.92  --prep_unflatten                        true
% 0.58/0.92  --prep_res_sim                          true
% 0.58/0.92  --prep_upred                            true
% 0.58/0.92  --prep_sem_filter                       exhaustive
% 0.58/0.92  --prep_sem_filter_out                   false
% 0.58/0.92  --pred_elim                             true
% 0.58/0.92  --res_sim_input                         true
% 0.58/0.92  --eq_ax_congr_red                       true
% 0.58/0.92  --pure_diseq_elim                       true
% 0.58/0.92  --brand_transform                       false
% 0.58/0.92  --non_eq_to_eq                          false
% 0.58/0.92  --prep_def_merge                        true
% 0.58/0.92  --prep_def_merge_prop_impl              false
% 0.58/0.92  --prep_def_merge_mbd                    true
% 0.58/0.92  --prep_def_merge_tr_red                 false
% 0.58/0.92  --prep_def_merge_tr_cl                  false
% 0.58/0.92  --smt_preprocessing                     true
% 0.58/0.92  --smt_ac_axioms                         fast
% 0.58/0.92  --preprocessed_out                      false
% 0.58/0.92  --preprocessed_stats                    false
% 0.58/0.92  
% 0.58/0.92  ------ Abstraction refinement Options
% 0.58/0.92  
% 0.58/0.92  --abstr_ref                             []
% 0.58/0.92  --abstr_ref_prep                        false
% 0.58/0.92  --abstr_ref_until_sat                   false
% 0.58/0.92  --abstr_ref_sig_restrict                funpre
% 0.58/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 0.58/0.92  --abstr_ref_under                       []
% 0.58/0.92  
% 0.58/0.92  ------ SAT Options
% 0.58/0.92  
% 0.58/0.92  --sat_mode                              false
% 0.58/0.92  --sat_fm_restart_options                ""
% 0.58/0.92  --sat_gr_def                            false
% 0.58/0.92  --sat_epr_types                         true
% 0.58/0.92  --sat_non_cyclic_types                  false
% 0.58/0.92  --sat_finite_models                     false
% 0.58/0.92  --sat_fm_lemmas                         false
% 0.58/0.92  --sat_fm_prep                           false
% 0.58/0.92  --sat_fm_uc_incr                        true
% 0.58/0.92  --sat_out_model                         small
% 0.58/0.92  --sat_out_clauses                       false
% 0.58/0.92  
% 0.58/0.92  ------ QBF Options
% 0.58/0.92  
% 0.58/0.92  --qbf_mode                              false
% 0.58/0.92  --qbf_elim_univ                         false
% 0.58/0.92  --qbf_dom_inst                          none
% 0.58/0.92  --qbf_dom_pre_inst                      false
% 0.58/0.92  --qbf_sk_in                             false
% 0.58/0.92  --qbf_pred_elim                         true
% 0.58/0.92  --qbf_split                             512
% 0.58/0.92  
% 0.58/0.92  ------ BMC1 Options
% 0.58/0.92  
% 0.58/0.92  --bmc1_incremental                      false
% 0.58/0.92  --bmc1_axioms                           reachable_all
% 0.58/0.92  --bmc1_min_bound                        0
% 0.58/0.92  --bmc1_max_bound                        -1
% 0.58/0.92  --bmc1_max_bound_default                -1
% 0.58/0.92  --bmc1_symbol_reachability              true
% 0.58/0.92  --bmc1_property_lemmas                  false
% 0.58/0.92  --bmc1_k_induction                      false
% 0.58/0.92  --bmc1_non_equiv_states                 false
% 0.58/0.92  --bmc1_deadlock                         false
% 0.58/0.92  --bmc1_ucm                              false
% 0.58/0.92  --bmc1_add_unsat_core                   none
% 0.58/0.92  --bmc1_unsat_core_children              false
% 0.58/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 0.58/0.92  --bmc1_out_stat                         full
% 0.58/0.92  --bmc1_ground_init                      false
% 0.58/0.92  --bmc1_pre_inst_next_state              false
% 0.58/0.92  --bmc1_pre_inst_state                   false
% 0.58/0.92  --bmc1_pre_inst_reach_state             false
% 0.58/0.92  --bmc1_out_unsat_core                   false
% 0.58/0.92  --bmc1_aig_witness_out                  false
% 0.58/0.92  --bmc1_verbose                          false
% 0.58/0.92  --bmc1_dump_clauses_tptp                false
% 0.58/0.92  --bmc1_dump_unsat_core_tptp             false
% 0.58/0.92  --bmc1_dump_file                        -
% 0.58/0.92  --bmc1_ucm_expand_uc_limit              128
% 0.58/0.92  --bmc1_ucm_n_expand_iterations          6
% 0.58/0.92  --bmc1_ucm_extend_mode                  1
% 0.58/0.92  --bmc1_ucm_init_mode                    2
% 0.58/0.92  --bmc1_ucm_cone_mode                    none
% 0.58/0.92  --bmc1_ucm_reduced_relation_type        0
% 0.58/0.92  --bmc1_ucm_relax_model                  4
% 0.58/0.92  --bmc1_ucm_full_tr_after_sat            true
% 0.58/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 0.58/0.92  --bmc1_ucm_layered_model                none
% 0.58/0.92  --bmc1_ucm_max_lemma_size               10
% 0.58/0.92  
% 0.58/0.92  ------ AIG Options
% 0.58/0.92  
% 0.58/0.92  --aig_mode                              false
% 0.58/0.92  
% 0.58/0.92  ------ Instantiation Options
% 0.58/0.92  
% 0.58/0.92  --instantiation_flag                    true
% 0.58/0.92  --inst_sos_flag                         false
% 0.58/0.92  --inst_sos_phase                        true
% 0.58/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.58/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.58/0.92  --inst_lit_sel_side                     num_symb
% 0.58/0.92  --inst_solver_per_active                1400
% 0.58/0.92  --inst_solver_calls_frac                1.
% 0.58/0.92  --inst_passive_queue_type               priority_queues
% 0.58/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.58/0.92  --inst_passive_queues_freq              [25;2]
% 0.58/0.92  --inst_dismatching                      true
% 0.58/0.92  --inst_eager_unprocessed_to_passive     true
% 0.58/0.92  --inst_prop_sim_given                   true
% 0.58/0.92  --inst_prop_sim_new                     false
% 0.58/0.92  --inst_subs_new                         false
% 0.58/0.92  --inst_eq_res_simp                      false
% 0.58/0.92  --inst_subs_given                       false
% 0.58/0.92  --inst_orphan_elimination               true
% 0.58/0.92  --inst_learning_loop_flag               true
% 0.58/0.92  --inst_learning_start                   3000
% 0.58/0.92  --inst_learning_factor                  2
% 0.58/0.92  --inst_start_prop_sim_after_learn       3
% 0.58/0.92  --inst_sel_renew                        solver
% 0.58/0.92  --inst_lit_activity_flag                true
% 0.58/0.92  --inst_restr_to_given                   false
% 0.58/0.92  --inst_activity_threshold               500
% 0.58/0.92  --inst_out_proof                        true
% 0.58/0.92  
% 0.58/0.92  ------ Resolution Options
% 0.58/0.92  
% 0.58/0.92  --resolution_flag                       true
% 0.58/0.92  --res_lit_sel                           adaptive
% 0.58/0.92  --res_lit_sel_side                      none
% 0.58/0.92  --res_ordering                          kbo
% 0.58/0.92  --res_to_prop_solver                    active
% 0.58/0.92  --res_prop_simpl_new                    false
% 0.58/0.92  --res_prop_simpl_given                  true
% 0.58/0.92  --res_passive_queue_type                priority_queues
% 0.58/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.58/0.92  --res_passive_queues_freq               [15;5]
% 0.58/0.92  --res_forward_subs                      full
% 0.58/0.92  --res_backward_subs                     full
% 0.58/0.92  --res_forward_subs_resolution           true
% 0.58/0.92  --res_backward_subs_resolution          true
% 0.58/0.92  --res_orphan_elimination                true
% 0.58/0.92  --res_time_limit                        2.
% 0.58/0.92  --res_out_proof                         true
% 0.58/0.92  
% 0.58/0.92  ------ Superposition Options
% 0.58/0.92  
% 0.58/0.92  --superposition_flag                    true
% 0.58/0.92  --sup_passive_queue_type                priority_queues
% 0.58/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.58/0.92  --sup_passive_queues_freq               [8;1;4]
% 0.58/0.92  --demod_completeness_check              fast
% 0.58/0.92  --demod_use_ground                      true
% 0.58/0.92  --sup_to_prop_solver                    passive
% 0.58/0.92  --sup_prop_simpl_new                    true
% 0.58/0.92  --sup_prop_simpl_given                  true
% 0.58/0.92  --sup_fun_splitting                     false
% 0.58/0.92  --sup_smt_interval                      50000
% 0.58/0.92  
% 0.58/0.92  ------ Superposition Simplification Setup
% 0.58/0.92  
% 0.58/0.92  --sup_indices_passive                   []
% 0.58/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.58/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.58/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.58/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 0.58/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.58/0.92  --sup_full_bw                           [BwDemod]
% 0.58/0.92  --sup_immed_triv                        [TrivRules]
% 0.58/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.58/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.58/0.92  --sup_immed_bw_main                     []
% 0.58/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.58/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 0.58/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.58/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.58/0.92  
% 0.58/0.92  ------ Combination Options
% 0.58/0.92  
% 0.58/0.92  --comb_res_mult                         3
% 0.58/0.92  --comb_sup_mult                         2
% 0.58/0.92  --comb_inst_mult                        10
% 0.58/0.92  
% 0.58/0.92  ------ Debug Options
% 0.58/0.92  
% 0.58/0.92  --dbg_backtrace                         false
% 0.58/0.92  --dbg_dump_prop_clauses                 false
% 0.58/0.92  --dbg_dump_prop_clauses_file            -
% 0.58/0.92  --dbg_out_stat                          false
% 0.58/0.92  ------ Parsing...
% 0.58/0.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.58/0.92  
% 0.58/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.58/0.92  
% 0.58/0.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.58/0.92  
% 0.58/0.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.58/0.92  ------ Proving...
% 0.58/0.92  ------ Problem Properties 
% 0.58/0.92  
% 0.58/0.92  
% 0.58/0.92  clauses                                 6
% 0.58/0.92  conjectures                             2
% 0.58/0.92  EPR                                     0
% 0.58/0.92  Horn                                    5
% 0.58/0.92  unary                                   1
% 0.58/0.92  binary                                  5
% 0.58/0.92  lits                                    11
% 0.58/0.92  lits eq                                 7
% 0.58/0.92  fd_pure                                 0
% 0.58/0.92  fd_pseudo                               0
% 0.58/0.92  fd_cond                                 0
% 0.58/0.92  fd_pseudo_cond                          1
% 0.58/0.92  AC symbols                              0
% 0.58/0.92  
% 0.58/0.92  ------ Schedule dynamic 5 is on 
% 0.58/0.92  
% 0.58/0.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.58/0.92  
% 0.58/0.92  
% 0.58/0.92  ------ 
% 0.58/0.92  Current options:
% 0.58/0.92  ------ 
% 0.58/0.92  
% 0.58/0.92  ------ Input Options
% 0.58/0.92  
% 0.58/0.92  --out_options                           all
% 0.58/0.92  --tptp_safe_out                         true
% 0.58/0.92  --problem_path                          ""
% 0.58/0.92  --include_path                          ""
% 0.58/0.92  --clausifier                            res/vclausify_rel
% 0.58/0.92  --clausifier_options                    --mode clausify
% 0.58/0.92  --stdin                                 false
% 0.58/0.92  --stats_out                             all
% 0.58/0.92  
% 0.58/0.92  ------ General Options
% 0.58/0.92  
% 0.58/0.92  --fof                                   false
% 0.58/0.92  --time_out_real                         305.
% 0.58/0.92  --time_out_virtual                      -1.
% 0.58/0.92  --symbol_type_check                     false
% 0.58/0.92  --clausify_out                          false
% 0.58/0.92  --sig_cnt_out                           false
% 0.58/0.92  --trig_cnt_out                          false
% 0.58/0.92  --trig_cnt_out_tolerance                1.
% 0.58/0.92  --trig_cnt_out_sk_spl                   false
% 0.58/0.92  --abstr_cl_out                          false
% 0.58/0.92  
% 0.58/0.92  ------ Global Options
% 0.58/0.92  
% 0.58/0.92  --schedule                              default
% 0.58/0.92  --add_important_lit                     false
% 0.58/0.92  --prop_solver_per_cl                    1000
% 0.58/0.92  --min_unsat_core                        false
% 0.58/0.92  --soft_assumptions                      false
% 0.58/0.92  --soft_lemma_size                       3
% 0.58/0.92  --prop_impl_unit_size                   0
% 0.58/0.92  --prop_impl_unit                        []
% 0.58/0.92  --share_sel_clauses                     true
% 0.58/0.92  --reset_solvers                         false
% 0.58/0.92  --bc_imp_inh                            [conj_cone]
% 0.58/0.92  --conj_cone_tolerance                   3.
% 0.58/0.92  --extra_neg_conj                        none
% 0.58/0.92  --large_theory_mode                     true
% 0.58/0.92  --prolific_symb_bound                   200
% 0.58/0.92  --lt_threshold                          2000
% 0.58/0.92  --clause_weak_htbl                      true
% 0.58/0.92  --gc_record_bc_elim                     false
% 0.58/0.92  
% 0.58/0.92  ------ Preprocessing Options
% 0.58/0.92  
% 0.58/0.92  --preprocessing_flag                    true
% 0.58/0.92  --time_out_prep_mult                    0.1
% 0.58/0.92  --splitting_mode                        input
% 0.58/0.92  --splitting_grd                         true
% 0.58/0.92  --splitting_cvd                         false
% 0.58/0.92  --splitting_cvd_svl                     false
% 0.58/0.92  --splitting_nvd                         32
% 0.58/0.92  --sub_typing                            true
% 0.58/0.92  --prep_gs_sim                           true
% 0.58/0.92  --prep_unflatten                        true
% 0.58/0.92  --prep_res_sim                          true
% 0.58/0.92  --prep_upred                            true
% 0.58/0.92  --prep_sem_filter                       exhaustive
% 0.58/0.92  --prep_sem_filter_out                   false
% 0.58/0.92  --pred_elim                             true
% 0.58/0.92  --res_sim_input                         true
% 0.58/0.92  --eq_ax_congr_red                       true
% 0.58/0.92  --pure_diseq_elim                       true
% 0.58/0.92  --brand_transform                       false
% 0.58/0.92  --non_eq_to_eq                          false
% 0.58/0.92  --prep_def_merge                        true
% 0.58/0.92  --prep_def_merge_prop_impl              false
% 0.58/0.92  --prep_def_merge_mbd                    true
% 0.58/0.92  --prep_def_merge_tr_red                 false
% 0.58/0.92  --prep_def_merge_tr_cl                  false
% 0.58/0.92  --smt_preprocessing                     true
% 0.58/0.92  --smt_ac_axioms                         fast
% 0.58/0.92  --preprocessed_out                      false
% 0.58/0.92  --preprocessed_stats                    false
% 0.58/0.92  
% 0.58/0.92  ------ Abstraction refinement Options
% 0.58/0.92  
% 0.58/0.92  --abstr_ref                             []
% 0.58/0.92  --abstr_ref_prep                        false
% 0.58/0.92  --abstr_ref_until_sat                   false
% 0.58/0.92  --abstr_ref_sig_restrict                funpre
% 0.58/0.92  --abstr_ref_af_restrict_to_split_sk     false
% 0.58/0.92  --abstr_ref_under                       []
% 0.58/0.92  
% 0.58/0.92  ------ SAT Options
% 0.58/0.92  
% 0.58/0.92  --sat_mode                              false
% 0.58/0.92  --sat_fm_restart_options                ""
% 0.58/0.92  --sat_gr_def                            false
% 0.58/0.92  --sat_epr_types                         true
% 0.58/0.92  --sat_non_cyclic_types                  false
% 0.58/0.92  --sat_finite_models                     false
% 0.58/0.92  --sat_fm_lemmas                         false
% 0.58/0.92  --sat_fm_prep                           false
% 0.58/0.92  --sat_fm_uc_incr                        true
% 0.58/0.92  --sat_out_model                         small
% 0.58/0.92  --sat_out_clauses                       false
% 0.58/0.92  
% 0.58/0.92  ------ QBF Options
% 0.58/0.92  
% 0.58/0.92  --qbf_mode                              false
% 0.58/0.92  --qbf_elim_univ                         false
% 0.58/0.92  --qbf_dom_inst                          none
% 0.58/0.92  --qbf_dom_pre_inst                      false
% 0.58/0.92  --qbf_sk_in                             false
% 0.58/0.92  --qbf_pred_elim                         true
% 0.58/0.92  --qbf_split                             512
% 0.58/0.92  
% 0.58/0.92  ------ BMC1 Options
% 0.58/0.92  
% 0.58/0.92  --bmc1_incremental                      false
% 0.58/0.92  --bmc1_axioms                           reachable_all
% 0.58/0.92  --bmc1_min_bound                        0
% 0.58/0.92  --bmc1_max_bound                        -1
% 0.58/0.92  --bmc1_max_bound_default                -1
% 0.58/0.92  --bmc1_symbol_reachability              true
% 0.58/0.92  --bmc1_property_lemmas                  false
% 0.58/0.92  --bmc1_k_induction                      false
% 0.58/0.92  --bmc1_non_equiv_states                 false
% 0.58/0.92  --bmc1_deadlock                         false
% 0.58/0.92  --bmc1_ucm                              false
% 0.58/0.92  --bmc1_add_unsat_core                   none
% 0.58/0.92  --bmc1_unsat_core_children              false
% 0.58/0.92  --bmc1_unsat_core_extrapolate_axioms    false
% 0.58/0.92  --bmc1_out_stat                         full
% 0.58/0.92  --bmc1_ground_init                      false
% 0.58/0.92  --bmc1_pre_inst_next_state              false
% 0.58/0.92  --bmc1_pre_inst_state                   false
% 0.58/0.92  --bmc1_pre_inst_reach_state             false
% 0.58/0.92  --bmc1_out_unsat_core                   false
% 0.58/0.92  --bmc1_aig_witness_out                  false
% 0.58/0.92  --bmc1_verbose                          false
% 0.58/0.92  --bmc1_dump_clauses_tptp                false
% 0.58/0.92  --bmc1_dump_unsat_core_tptp             false
% 0.58/0.92  --bmc1_dump_file                        -
% 0.58/0.92  --bmc1_ucm_expand_uc_limit              128
% 0.58/0.92  --bmc1_ucm_n_expand_iterations          6
% 0.58/0.92  --bmc1_ucm_extend_mode                  1
% 0.58/0.92  --bmc1_ucm_init_mode                    2
% 0.58/0.92  --bmc1_ucm_cone_mode                    none
% 0.58/0.92  --bmc1_ucm_reduced_relation_type        0
% 0.58/0.92  --bmc1_ucm_relax_model                  4
% 0.58/0.92  --bmc1_ucm_full_tr_after_sat            true
% 0.58/0.92  --bmc1_ucm_expand_neg_assumptions       false
% 0.58/0.92  --bmc1_ucm_layered_model                none
% 0.58/0.92  --bmc1_ucm_max_lemma_size               10
% 0.58/0.92  
% 0.58/0.92  ------ AIG Options
% 0.58/0.92  
% 0.58/0.92  --aig_mode                              false
% 0.58/0.92  
% 0.58/0.92  ------ Instantiation Options
% 0.58/0.92  
% 0.58/0.92  --instantiation_flag                    true
% 0.58/0.92  --inst_sos_flag                         false
% 0.58/0.92  --inst_sos_phase                        true
% 0.58/0.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.58/0.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.58/0.92  --inst_lit_sel_side                     none
% 0.58/0.92  --inst_solver_per_active                1400
% 0.58/0.92  --inst_solver_calls_frac                1.
% 0.58/0.92  --inst_passive_queue_type               priority_queues
% 0.58/0.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.58/0.92  --inst_passive_queues_freq              [25;2]
% 0.58/0.92  --inst_dismatching                      true
% 0.58/0.92  --inst_eager_unprocessed_to_passive     true
% 0.58/0.92  --inst_prop_sim_given                   true
% 0.58/0.92  --inst_prop_sim_new                     false
% 0.58/0.92  --inst_subs_new                         false
% 0.58/0.92  --inst_eq_res_simp                      false
% 0.58/0.92  --inst_subs_given                       false
% 0.58/0.92  --inst_orphan_elimination               true
% 0.58/0.92  --inst_learning_loop_flag               true
% 0.58/0.92  --inst_learning_start                   3000
% 0.58/0.92  --inst_learning_factor                  2
% 0.58/0.92  --inst_start_prop_sim_after_learn       3
% 0.58/0.92  --inst_sel_renew                        solver
% 0.58/0.92  --inst_lit_activity_flag                true
% 0.58/0.92  --inst_restr_to_given                   false
% 0.58/0.92  --inst_activity_threshold               500
% 0.58/0.92  --inst_out_proof                        true
% 0.58/0.92  
% 0.58/0.92  ------ Resolution Options
% 0.58/0.92  
% 0.58/0.92  --resolution_flag                       false
% 0.58/0.92  --res_lit_sel                           adaptive
% 0.58/0.92  --res_lit_sel_side                      none
% 0.58/0.92  --res_ordering                          kbo
% 0.58/0.92  --res_to_prop_solver                    active
% 0.58/0.92  --res_prop_simpl_new                    false
% 0.58/0.92  --res_prop_simpl_given                  true
% 0.58/0.92  --res_passive_queue_type                priority_queues
% 0.58/0.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.58/0.92  --res_passive_queues_freq               [15;5]
% 0.58/0.92  --res_forward_subs                      full
% 0.58/0.92  --res_backward_subs                     full
% 0.58/0.92  --res_forward_subs_resolution           true
% 0.58/0.92  --res_backward_subs_resolution          true
% 0.58/0.92  --res_orphan_elimination                true
% 0.58/0.92  --res_time_limit                        2.
% 0.58/0.92  --res_out_proof                         true
% 0.58/0.92  
% 0.58/0.92  ------ Superposition Options
% 0.58/0.92  
% 0.58/0.92  --superposition_flag                    true
% 0.58/0.92  --sup_passive_queue_type                priority_queues
% 0.58/0.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.58/0.92  --sup_passive_queues_freq               [8;1;4]
% 0.58/0.92  --demod_completeness_check              fast
% 0.58/0.92  --demod_use_ground                      true
% 0.58/0.92  --sup_to_prop_solver                    passive
% 0.58/0.92  --sup_prop_simpl_new                    true
% 0.58/0.92  --sup_prop_simpl_given                  true
% 0.58/0.92  --sup_fun_splitting                     false
% 0.58/0.92  --sup_smt_interval                      50000
% 0.58/0.92  
% 0.58/0.92  ------ Superposition Simplification Setup
% 0.58/0.92  
% 0.58/0.92  --sup_indices_passive                   []
% 0.58/0.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.58/0.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.58/0.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.58/0.92  --sup_full_triv                         [TrivRules;PropSubs]
% 0.58/0.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.58/0.92  --sup_full_bw                           [BwDemod]
% 0.58/0.92  --sup_immed_triv                        [TrivRules]
% 0.58/0.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.58/0.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.58/0.92  --sup_immed_bw_main                     []
% 0.58/0.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.58/0.92  --sup_input_triv                        [Unflattening;TrivRules]
% 0.58/0.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.58/0.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.58/0.92  
% 0.58/0.92  ------ Combination Options
% 0.58/0.92  
% 0.58/0.92  --comb_res_mult                         3
% 0.58/0.92  --comb_sup_mult                         2
% 0.58/0.92  --comb_inst_mult                        10
% 0.58/0.92  
% 0.58/0.92  ------ Debug Options
% 0.58/0.92  
% 0.58/0.92  --dbg_backtrace                         false
% 0.58/0.92  --dbg_dump_prop_clauses                 false
% 0.58/0.92  --dbg_dump_prop_clauses_file            -
% 0.58/0.92  --dbg_out_stat                          false
% 0.58/0.92  
% 0.58/0.92  
% 0.58/0.92  
% 0.58/0.92  
% 0.58/0.92  ------ Proving...
% 0.58/0.92  
% 0.58/0.92  
% 0.58/0.92  % SZS status Theorem for theBenchmark.p
% 0.58/0.92  
% 0.58/0.92  % SZS output start CNFRefutation for theBenchmark.p
% 0.58/0.92  
% 0.58/0.92  fof(f4,axiom,(
% 0.58/0.92    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.58/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.58/0.92  
% 0.58/0.92  fof(f8,plain,(
% 0.58/0.92    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 0.58/0.92    inference(ennf_transformation,[],[f4])).
% 0.58/0.92  
% 0.58/0.92  fof(f18,plain,(
% 0.58/0.92    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.58/0.92    inference(cnf_transformation,[],[f8])).
% 0.58/0.92  
% 0.58/0.92  fof(f2,axiom,(
% 0.58/0.92    ! [X0] : k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)),
% 0.58/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.58/0.92  
% 0.58/0.92  fof(f16,plain,(
% 0.58/0.92    ( ! [X0] : (k2_enumset1(X0,X0,X0,X0) = k1_tarski(X0)) )),
% 0.58/0.92    inference(cnf_transformation,[],[f2])).
% 0.58/0.92  
% 0.58/0.92  fof(f22,plain,(
% 0.58/0.92    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) | X0 = X1) )),
% 0.58/0.92    inference(definition_unfolding,[],[f18,f16,f16])).
% 0.58/0.92  
% 0.58/0.92  fof(f1,axiom,(
% 0.58/0.92    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.58/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.58/0.92  
% 0.58/0.92  fof(f10,plain,(
% 0.58/0.92    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.58/0.92    inference(nnf_transformation,[],[f1])).
% 0.58/0.92  
% 0.58/0.92  fof(f14,plain,(
% 0.58/0.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.58/0.92    inference(cnf_transformation,[],[f10])).
% 0.58/0.92  
% 0.58/0.92  fof(f5,conjecture,(
% 0.58/0.92    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 0.58/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.58/0.92  
% 0.58/0.92  fof(f6,negated_conjecture,(
% 0.58/0.92    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 0.58/0.92    inference(negated_conjecture,[],[f5])).
% 0.58/0.92  
% 0.58/0.92  fof(f9,plain,(
% 0.58/0.92    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <~> X0 != X1)),
% 0.58/0.92    inference(ennf_transformation,[],[f6])).
% 0.58/0.92  
% 0.58/0.92  fof(f11,plain,(
% 0.58/0.92    ? [X0,X1] : ((X0 = X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)))),
% 0.58/0.92    inference(nnf_transformation,[],[f9])).
% 0.58/0.92  
% 0.58/0.92  fof(f12,plain,(
% 0.58/0.92    ? [X0,X1] : ((X0 = X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))) => ((sK0 = sK1 | k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(sK0)) & (sK0 != sK1 | k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0)))),
% 0.58/0.92    introduced(choice_axiom,[])).
% 0.58/0.92  
% 0.58/0.92  fof(f13,plain,(
% 0.58/0.92    (sK0 = sK1 | k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(sK0)) & (sK0 != sK1 | k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0))),
% 0.58/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 0.58/0.92  
% 0.58/0.92  fof(f20,plain,(
% 0.58/0.92    sK0 = sK1 | k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k1_tarski(sK0)),
% 0.58/0.92    inference(cnf_transformation,[],[f13])).
% 0.58/0.92  
% 0.58/0.92  fof(f23,plain,(
% 0.58/0.92    sK0 = sK1 | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.58/0.92    inference(definition_unfolding,[],[f20,f16,f16,f16])).
% 0.58/0.92  
% 0.58/0.92  fof(f19,plain,(
% 0.58/0.92    sK0 != sK1 | k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) = k1_tarski(sK0)),
% 0.58/0.92    inference(cnf_transformation,[],[f13])).
% 0.58/0.92  
% 0.58/0.92  fof(f24,plain,(
% 0.58/0.92    sK0 != sK1 | k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.58/0.92    inference(definition_unfolding,[],[f19,f16,f16,f16])).
% 0.58/0.92  
% 0.58/0.92  fof(f15,plain,(
% 0.58/0.92    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.58/0.92    inference(cnf_transformation,[],[f10])).
% 0.58/0.92  
% 0.58/0.92  fof(f3,axiom,(
% 0.58/0.92    ! [X0,X1] : ~(X0 = X1 & r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.58/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.58/0.92  
% 0.58/0.92  fof(f7,plain,(
% 0.58/0.92    ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.58/0.92    inference(ennf_transformation,[],[f3])).
% 0.58/0.92  
% 0.58/0.92  fof(f17,plain,(
% 0.58/0.92    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.58/0.92    inference(cnf_transformation,[],[f7])).
% 0.58/0.92  
% 0.58/0.92  fof(f21,plain,(
% 0.58/0.92    ( ! [X0,X1] : (X0 != X1 | ~r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))) )),
% 0.58/0.92    inference(definition_unfolding,[],[f17,f16,f16])).
% 0.58/0.92  
% 0.58/0.92  fof(f25,plain,(
% 0.58/0.92    ( ! [X1] : (~r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X1))) )),
% 0.58/0.92    inference(equality_resolution,[],[f21])).
% 0.58/0.92  
% 0.58/0.92  cnf(c_3,plain,
% 0.58/0.92      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1))
% 0.58/0.92      | X1 = X0 ),
% 0.58/0.92      inference(cnf_transformation,[],[f22]) ).
% 0.58/0.92  
% 0.58/0.92  cnf(c_268,plain,
% 0.58/0.92      ( X0 = X1
% 0.58/0.92      | r1_xboole_0(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 0.58/0.92      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 0.58/0.92  
% 0.58/0.92  cnf(c_1,plain,
% 0.58/0.92      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 0.58/0.92      inference(cnf_transformation,[],[f14]) ).
% 0.58/0.92  
% 0.58/0.92  cnf(c_270,plain,
% 0.58/0.92      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 0.58/0.92      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 0.58/0.92  
% 0.58/0.92  cnf(c_405,plain,
% 0.58/0.92      ( X0 = X1
% 0.58/0.92      | k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X1)) = k2_enumset1(X0,X0,X0,X0) ),
% 0.58/0.92      inference(superposition,[status(thm)],[c_268,c_270]) ).
% 0.58/0.92  
% 0.58/0.92  cnf(c_4,negated_conjecture,
% 0.58/0.92      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) != k2_enumset1(sK0,sK0,sK0,sK0)
% 0.58/0.92      | sK0 = sK1 ),
% 0.58/0.92      inference(cnf_transformation,[],[f23]) ).
% 0.58/0.92  
% 0.58/0.92  cnf(c_460,plain,
% 0.58/0.92      ( sK1 = sK0 ),
% 0.58/0.92      inference(superposition,[status(thm)],[c_405,c_4]) ).
% 0.58/0.92  
% 0.58/0.92  cnf(c_5,negated_conjecture,
% 0.58/0.92      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) = k2_enumset1(sK0,sK0,sK0,sK0)
% 0.58/0.92      | sK0 != sK1 ),
% 0.58/0.92      inference(cnf_transformation,[],[f24]) ).
% 0.58/0.92  
% 0.58/0.92  cnf(c_464,plain,
% 0.58/0.92      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) = k2_enumset1(sK0,sK0,sK0,sK0)
% 0.58/0.92      | sK0 != sK0 ),
% 0.58/0.92      inference(demodulation,[status(thm)],[c_460,c_5]) ).
% 0.58/0.92  
% 0.58/0.92  cnf(c_466,plain,
% 0.58/0.92      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 0.58/0.92      inference(equality_resolution_simp,[status(thm)],[c_464]) ).
% 0.58/0.92  
% 0.58/0.92  cnf(c_0,plain,
% 0.58/0.92      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 0.58/0.92      inference(cnf_transformation,[],[f15]) ).
% 0.58/0.92  
% 0.58/0.92  cnf(c_37,plain,
% 0.58/0.92      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 0.58/0.92      inference(prop_impl,[status(thm)],[c_0]) ).
% 0.58/0.92  
% 0.58/0.92  cnf(c_2,plain,
% 0.58/0.92      ( ~ r1_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) ),
% 0.58/0.92      inference(cnf_transformation,[],[f25]) ).
% 0.58/0.92  
% 0.58/0.92  cnf(c_79,plain,
% 0.58/0.92      ( k2_enumset1(X0,X0,X0,X0) != X1
% 0.58/0.92      | k2_enumset1(X0,X0,X0,X0) != X2
% 0.58/0.92      | k4_xboole_0(X2,X1) != X2 ),
% 0.58/0.92      inference(resolution_lifted,[status(thm)],[c_37,c_2]) ).
% 0.58/0.92  
% 0.58/0.92  cnf(c_80,plain,
% 0.58/0.92      ( k4_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X0)) != k2_enumset1(X0,X0,X0,X0) ),
% 0.58/0.92      inference(unflattening,[status(thm)],[c_79]) ).
% 0.58/0.92  
% 0.58/0.92  cnf(c_81,plain,
% 0.58/0.92      ( k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) != k2_enumset1(sK0,sK0,sK0,sK0) ),
% 0.58/0.92      inference(instantiation,[status(thm)],[c_80]) ).
% 0.58/0.92  
% 0.58/0.92  cnf(contradiction,plain,
% 0.58/0.92      ( $false ),
% 0.58/0.92      inference(minisat,[status(thm)],[c_466,c_81]) ).
% 0.58/0.92  
% 0.58/0.92  
% 0.58/0.92  % SZS output end CNFRefutation for theBenchmark.p
% 0.58/0.92  
% 0.58/0.92  ------                               Statistics
% 0.58/0.92  
% 0.58/0.92  ------ General
% 0.58/0.92  
% 0.58/0.92  abstr_ref_over_cycles:                  0
% 0.58/0.92  abstr_ref_under_cycles:                 0
% 0.58/0.92  gc_basic_clause_elim:                   0
% 0.58/0.92  forced_gc_time:                         0
% 0.58/0.92  parsing_time:                           0.007
% 0.58/0.92  unif_index_cands_time:                  0.
% 0.58/0.92  unif_index_add_time:                    0.
% 0.58/0.92  orderings_time:                         0.
% 0.58/0.92  out_proof_time:                         0.006
% 0.58/0.92  total_time:                             0.043
% 0.58/0.92  num_of_symbols:                         36
% 0.58/0.92  num_of_terms:                           387
% 0.58/0.92  
% 0.58/0.92  ------ Preprocessing
% 0.58/0.92  
% 0.58/0.92  num_of_splits:                          0
% 0.58/0.92  num_of_split_atoms:                     0
% 0.58/0.92  num_of_reused_defs:                     0
% 0.58/0.92  num_eq_ax_congr_red:                    0
% 0.58/0.92  num_of_sem_filtered_clauses:            1
% 0.58/0.92  num_of_subtypes:                        0
% 0.58/0.92  monotx_restored_types:                  0
% 0.58/0.92  sat_num_of_epr_types:                   0
% 0.58/0.92  sat_num_of_non_cyclic_types:            0
% 0.58/0.92  sat_guarded_non_collapsed_types:        0
% 0.58/0.92  num_pure_diseq_elim:                    0
% 0.58/0.92  simp_replaced_by:                       0
% 0.58/0.92  res_preprocessed:                       29
% 0.58/0.92  prep_upred:                             0
% 0.58/0.92  prep_unflattend:                        4
% 0.58/0.92  smt_new_axioms:                         0
% 0.58/0.92  pred_elim_cands:                        1
% 0.58/0.92  pred_elim:                              0
% 0.58/0.92  pred_elim_cl:                           0
% 0.58/0.92  pred_elim_cycles:                       1
% 0.58/0.92  merged_defs:                            12
% 0.58/0.92  merged_defs_ncl:                        0
% 0.58/0.92  bin_hyper_res:                          12
% 0.58/0.92  prep_cycles:                            3
% 0.58/0.92  pred_elim_time:                         0.
% 0.58/0.92  splitting_time:                         0.
% 0.58/0.92  sem_filter_time:                        0.
% 0.58/0.92  monotx_time:                            0.
% 0.58/0.92  subtype_inf_time:                       0.
% 0.58/0.92  
% 0.58/0.92  ------ Problem properties
% 0.58/0.92  
% 0.58/0.92  clauses:                                6
% 0.58/0.92  conjectures:                            2
% 0.58/0.92  epr:                                    0
% 0.58/0.92  horn:                                   5
% 0.58/0.92  ground:                                 2
% 0.58/0.92  unary:                                  1
% 0.58/0.92  binary:                                 5
% 0.58/0.92  lits:                                   11
% 0.58/0.92  lits_eq:                                7
% 0.58/0.92  fd_pure:                                0
% 0.58/0.92  fd_pseudo:                              0
% 0.58/0.92  fd_cond:                                0
% 0.58/0.92  fd_pseudo_cond:                         1
% 0.58/0.92  ac_symbols:                             0
% 0.58/0.92  
% 0.58/0.92  ------ Propositional Solver
% 0.58/0.92  
% 0.58/0.92  prop_solver_calls:                      20
% 0.58/0.92  prop_fast_solver_calls:                 152
% 0.58/0.92  smt_solver_calls:                       0
% 0.58/0.92  smt_fast_solver_calls:                  0
% 0.58/0.92  prop_num_of_clauses:                    108
% 0.58/0.92  prop_preprocess_simplified:             768
% 0.58/0.92  prop_fo_subsumed:                       0
% 0.58/0.92  prop_solver_time:                       0.
% 0.58/0.92  smt_solver_time:                        0.
% 0.58/0.92  smt_fast_solver_time:                   0.
% 0.58/0.92  prop_fast_solver_time:                  0.
% 0.58/0.92  prop_unsat_core_time:                   0.
% 0.58/0.92  
% 0.58/0.92  ------ QBF
% 0.58/0.92  
% 0.58/0.92  qbf_q_res:                              0
% 0.58/0.92  qbf_num_tautologies:                    0
% 0.58/0.92  qbf_prep_cycles:                        0
% 0.58/0.92  
% 0.58/0.92  ------ BMC1
% 0.58/0.92  
% 0.58/0.92  bmc1_current_bound:                     -1
% 0.58/0.92  bmc1_last_solved_bound:                 -1
% 0.58/0.92  bmc1_unsat_core_size:                   -1
% 0.58/0.92  bmc1_unsat_core_parents_size:           -1
% 0.58/0.92  bmc1_merge_next_fun:                    0
% 0.58/0.92  bmc1_unsat_core_clauses_time:           0.
% 0.58/0.92  
% 0.58/0.92  ------ Instantiation
% 0.58/0.92  
% 0.58/0.92  inst_num_of_clauses:                    39
% 0.58/0.92  inst_num_in_passive:                    4
% 0.58/0.92  inst_num_in_active:                     31
% 0.58/0.92  inst_num_in_unprocessed:                4
% 0.58/0.92  inst_num_of_loops:                      40
% 0.58/0.92  inst_num_of_learning_restarts:          0
% 0.58/0.92  inst_num_moves_active_passive:          6
% 0.58/0.92  inst_lit_activity:                      0
% 0.58/0.92  inst_lit_activity_moves:                0
% 0.58/0.92  inst_num_tautologies:                   0
% 0.58/0.92  inst_num_prop_implied:                  0
% 0.58/0.92  inst_num_existing_simplified:           0
% 0.58/0.92  inst_num_eq_res_simplified:             0
% 0.58/0.92  inst_num_child_elim:                    0
% 0.58/0.92  inst_num_of_dismatching_blockings:      17
% 0.58/0.92  inst_num_of_non_proper_insts:           35
% 0.58/0.92  inst_num_of_duplicates:                 0
% 0.58/0.92  inst_inst_num_from_inst_to_res:         0
% 0.58/0.92  inst_dismatching_checking_time:         0.
% 0.58/0.92  
% 0.58/0.92  ------ Resolution
% 0.58/0.92  
% 0.58/0.92  res_num_of_clauses:                     0
% 0.58/0.92  res_num_in_passive:                     0
% 0.58/0.92  res_num_in_active:                      0
% 0.58/0.92  res_num_of_loops:                       32
% 0.58/0.92  res_forward_subset_subsumed:            2
% 0.58/0.92  res_backward_subset_subsumed:           0
% 0.58/0.92  res_forward_subsumed:                   0
% 0.58/0.92  res_backward_subsumed:                  0
% 0.58/0.92  res_forward_subsumption_resolution:     0
% 0.58/0.92  res_backward_subsumption_resolution:    0
% 0.58/0.92  res_clause_to_clause_subsumption:       18
% 0.58/0.92  res_orphan_elimination:                 0
% 0.58/0.92  res_tautology_del:                      29
% 0.58/0.92  res_num_eq_res_simplified:              0
% 0.58/0.92  res_num_sel_changes:                    0
% 0.58/0.92  res_moves_from_active_to_pass:          0
% 0.58/0.92  
% 0.58/0.92  ------ Superposition
% 0.58/0.92  
% 0.58/0.92  sup_time_total:                         0.
% 0.58/0.92  sup_time_generating:                    0.
% 0.58/0.92  sup_time_sim_full:                      0.
% 0.58/0.92  sup_time_sim_immed:                     0.
% 0.58/0.92  
% 0.58/0.92  sup_num_of_clauses:                     7
% 0.58/0.92  sup_num_in_active:                      5
% 0.58/0.92  sup_num_in_passive:                     2
% 0.58/0.92  sup_num_of_loops:                       7
% 0.58/0.92  sup_fw_superposition:                   0
% 0.58/0.92  sup_bw_superposition:                   4
% 0.58/0.92  sup_immediate_simplified:               0
% 0.58/0.92  sup_given_eliminated:                   0
% 0.58/0.92  comparisons_done:                       0
% 0.58/0.92  comparisons_avoided:                    1
% 0.58/0.92  
% 0.58/0.92  ------ Simplifications
% 0.58/0.92  
% 0.58/0.92  
% 0.58/0.92  sim_fw_subset_subsumed:                 0
% 0.58/0.92  sim_bw_subset_subsumed:                 0
% 0.58/0.92  sim_fw_subsumed:                        0
% 0.58/0.92  sim_bw_subsumed:                        0
% 0.58/0.92  sim_fw_subsumption_res:                 0
% 0.58/0.92  sim_bw_subsumption_res:                 0
% 0.58/0.92  sim_tautology_del:                      0
% 0.58/0.92  sim_eq_tautology_del:                   2
% 0.58/0.92  sim_eq_res_simp:                        1
% 0.58/0.92  sim_fw_demodulated:                     0
% 0.58/0.92  sim_bw_demodulated:                     2
% 0.58/0.92  sim_light_normalised:                   0
% 0.58/0.92  sim_joinable_taut:                      0
% 0.58/0.92  sim_joinable_simp:                      0
% 0.58/0.92  sim_ac_normalised:                      0
% 0.58/0.92  sim_smt_subsumption:                    0
% 0.58/0.92  
%------------------------------------------------------------------------------
