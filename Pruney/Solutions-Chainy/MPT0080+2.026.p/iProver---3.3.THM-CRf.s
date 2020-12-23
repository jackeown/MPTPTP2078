%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:57 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   57 (  88 expanded)
%              Number of clauses        :   27 (  31 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :   12
%              Number of atoms          :   86 ( 147 expanded)
%              Number of equality atoms :   44 (  63 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f20])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK2,sK3)
      & r1_xboole_0(sK2,sK4)
      & r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ~ r1_tarski(sK2,sK3)
    & r1_xboole_0(sK2,sK4)
    & r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f29])).

fof(f47,plain,(
    r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    r1_xboole_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f44])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f40,f44])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f49,plain,(
    ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_590,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_594,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1621,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_594])).

cnf(c_2779,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_590,c_1621])).

cnf(c_16,negated_conjecture,
    ( r1_xboole_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_591,plain,
    ( r1_xboole_0(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_598,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1490,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_591,c_598])).

cnf(c_10,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1504,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK4),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK4),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1490,c_10])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_613,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9,c_11])).

cnf(c_13,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_931,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_613,c_13])).

cnf(c_937,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_931,c_11])).

cnf(c_932,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_13,c_0])).

cnf(c_1012,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_932,c_10])).

cnf(c_1506,plain,
    ( k4_xboole_0(sK2,sK4) = sK2 ),
    inference(demodulation,[status(thm)],[c_1504,c_937,c_1012])).

cnf(c_2811,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2779,c_1506])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20,plain,
    ( r1_tarski(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2811,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:32:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.92/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/0.97  
% 1.92/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.92/0.97  
% 1.92/0.97  ------  iProver source info
% 1.92/0.97  
% 1.92/0.97  git: date: 2020-06-30 10:37:57 +0100
% 1.92/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.92/0.97  git: non_committed_changes: false
% 1.92/0.97  git: last_make_outside_of_git: false
% 1.92/0.97  
% 1.92/0.97  ------ 
% 1.92/0.97  
% 1.92/0.97  ------ Input Options
% 1.92/0.97  
% 1.92/0.97  --out_options                           all
% 1.92/0.97  --tptp_safe_out                         true
% 1.92/0.97  --problem_path                          ""
% 1.92/0.97  --include_path                          ""
% 1.92/0.97  --clausifier                            res/vclausify_rel
% 1.92/0.97  --clausifier_options                    --mode clausify
% 1.92/0.97  --stdin                                 false
% 1.92/0.97  --stats_out                             all
% 1.92/0.97  
% 1.92/0.97  ------ General Options
% 1.92/0.97  
% 1.92/0.97  --fof                                   false
% 1.92/0.97  --time_out_real                         305.
% 1.92/0.97  --time_out_virtual                      -1.
% 1.92/0.97  --symbol_type_check                     false
% 1.92/0.97  --clausify_out                          false
% 1.92/0.97  --sig_cnt_out                           false
% 1.92/0.97  --trig_cnt_out                          false
% 1.92/0.97  --trig_cnt_out_tolerance                1.
% 1.92/0.97  --trig_cnt_out_sk_spl                   false
% 1.92/0.97  --abstr_cl_out                          false
% 1.92/0.97  
% 1.92/0.97  ------ Global Options
% 1.92/0.97  
% 1.92/0.97  --schedule                              default
% 1.92/0.97  --add_important_lit                     false
% 1.92/0.97  --prop_solver_per_cl                    1000
% 1.92/0.97  --min_unsat_core                        false
% 1.92/0.97  --soft_assumptions                      false
% 1.92/0.97  --soft_lemma_size                       3
% 1.92/0.97  --prop_impl_unit_size                   0
% 1.92/0.97  --prop_impl_unit                        []
% 1.92/0.97  --share_sel_clauses                     true
% 1.92/0.97  --reset_solvers                         false
% 1.92/0.97  --bc_imp_inh                            [conj_cone]
% 1.92/0.97  --conj_cone_tolerance                   3.
% 1.92/0.97  --extra_neg_conj                        none
% 1.92/0.97  --large_theory_mode                     true
% 1.92/0.97  --prolific_symb_bound                   200
% 1.92/0.97  --lt_threshold                          2000
% 1.92/0.97  --clause_weak_htbl                      true
% 1.92/0.97  --gc_record_bc_elim                     false
% 1.92/0.97  
% 1.92/0.97  ------ Preprocessing Options
% 1.92/0.97  
% 1.92/0.97  --preprocessing_flag                    true
% 1.92/0.97  --time_out_prep_mult                    0.1
% 1.92/0.97  --splitting_mode                        input
% 1.92/0.97  --splitting_grd                         true
% 1.92/0.97  --splitting_cvd                         false
% 1.92/0.97  --splitting_cvd_svl                     false
% 1.92/0.97  --splitting_nvd                         32
% 1.92/0.97  --sub_typing                            true
% 1.92/0.97  --prep_gs_sim                           true
% 1.92/0.97  --prep_unflatten                        true
% 1.92/0.97  --prep_res_sim                          true
% 1.92/0.97  --prep_upred                            true
% 1.92/0.97  --prep_sem_filter                       exhaustive
% 1.92/0.97  --prep_sem_filter_out                   false
% 1.92/0.97  --pred_elim                             true
% 1.92/0.97  --res_sim_input                         true
% 1.92/0.97  --eq_ax_congr_red                       true
% 1.92/0.97  --pure_diseq_elim                       true
% 1.92/0.97  --brand_transform                       false
% 1.92/0.97  --non_eq_to_eq                          false
% 1.92/0.97  --prep_def_merge                        true
% 1.92/0.97  --prep_def_merge_prop_impl              false
% 1.92/0.97  --prep_def_merge_mbd                    true
% 1.92/0.97  --prep_def_merge_tr_red                 false
% 1.92/0.97  --prep_def_merge_tr_cl                  false
% 1.92/0.97  --smt_preprocessing                     true
% 1.92/0.97  --smt_ac_axioms                         fast
% 1.92/0.97  --preprocessed_out                      false
% 1.92/0.97  --preprocessed_stats                    false
% 1.92/0.97  
% 1.92/0.97  ------ Abstraction refinement Options
% 1.92/0.97  
% 1.92/0.97  --abstr_ref                             []
% 1.92/0.97  --abstr_ref_prep                        false
% 1.92/0.97  --abstr_ref_until_sat                   false
% 1.92/0.97  --abstr_ref_sig_restrict                funpre
% 1.92/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.92/0.97  --abstr_ref_under                       []
% 1.92/0.97  
% 1.92/0.97  ------ SAT Options
% 1.92/0.97  
% 1.92/0.97  --sat_mode                              false
% 1.92/0.97  --sat_fm_restart_options                ""
% 1.92/0.97  --sat_gr_def                            false
% 1.92/0.97  --sat_epr_types                         true
% 1.92/0.97  --sat_non_cyclic_types                  false
% 1.92/0.97  --sat_finite_models                     false
% 1.92/0.97  --sat_fm_lemmas                         false
% 1.92/0.97  --sat_fm_prep                           false
% 1.92/0.97  --sat_fm_uc_incr                        true
% 1.92/0.97  --sat_out_model                         small
% 1.92/0.97  --sat_out_clauses                       false
% 1.92/0.97  
% 1.92/0.97  ------ QBF Options
% 1.92/0.97  
% 1.92/0.97  --qbf_mode                              false
% 1.92/0.97  --qbf_elim_univ                         false
% 1.92/0.97  --qbf_dom_inst                          none
% 1.92/0.97  --qbf_dom_pre_inst                      false
% 1.92/0.97  --qbf_sk_in                             false
% 1.92/0.97  --qbf_pred_elim                         true
% 1.92/0.97  --qbf_split                             512
% 1.92/0.97  
% 1.92/0.97  ------ BMC1 Options
% 1.92/0.97  
% 1.92/0.97  --bmc1_incremental                      false
% 1.92/0.97  --bmc1_axioms                           reachable_all
% 1.92/0.97  --bmc1_min_bound                        0
% 1.92/0.97  --bmc1_max_bound                        -1
% 1.92/0.97  --bmc1_max_bound_default                -1
% 1.92/0.97  --bmc1_symbol_reachability              true
% 1.92/0.97  --bmc1_property_lemmas                  false
% 1.92/0.97  --bmc1_k_induction                      false
% 1.92/0.97  --bmc1_non_equiv_states                 false
% 1.92/0.97  --bmc1_deadlock                         false
% 1.92/0.97  --bmc1_ucm                              false
% 1.92/0.97  --bmc1_add_unsat_core                   none
% 1.92/0.97  --bmc1_unsat_core_children              false
% 1.92/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.92/0.97  --bmc1_out_stat                         full
% 1.92/0.97  --bmc1_ground_init                      false
% 1.92/0.97  --bmc1_pre_inst_next_state              false
% 1.92/0.97  --bmc1_pre_inst_state                   false
% 1.92/0.97  --bmc1_pre_inst_reach_state             false
% 1.92/0.97  --bmc1_out_unsat_core                   false
% 1.92/0.97  --bmc1_aig_witness_out                  false
% 1.92/0.97  --bmc1_verbose                          false
% 1.92/0.97  --bmc1_dump_clauses_tptp                false
% 1.92/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.92/0.97  --bmc1_dump_file                        -
% 1.92/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.92/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.92/0.97  --bmc1_ucm_extend_mode                  1
% 1.92/0.97  --bmc1_ucm_init_mode                    2
% 1.92/0.97  --bmc1_ucm_cone_mode                    none
% 1.92/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.92/0.97  --bmc1_ucm_relax_model                  4
% 1.92/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.92/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.92/0.97  --bmc1_ucm_layered_model                none
% 1.92/0.97  --bmc1_ucm_max_lemma_size               10
% 1.92/0.97  
% 1.92/0.97  ------ AIG Options
% 1.92/0.97  
% 1.92/0.97  --aig_mode                              false
% 1.92/0.97  
% 1.92/0.97  ------ Instantiation Options
% 1.92/0.97  
% 1.92/0.97  --instantiation_flag                    true
% 1.92/0.97  --inst_sos_flag                         false
% 1.92/0.97  --inst_sos_phase                        true
% 1.92/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.92/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.92/0.97  --inst_lit_sel_side                     num_symb
% 1.92/0.97  --inst_solver_per_active                1400
% 1.92/0.97  --inst_solver_calls_frac                1.
% 1.92/0.97  --inst_passive_queue_type               priority_queues
% 1.92/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.92/0.97  --inst_passive_queues_freq              [25;2]
% 1.92/0.97  --inst_dismatching                      true
% 1.92/0.97  --inst_eager_unprocessed_to_passive     true
% 1.92/0.97  --inst_prop_sim_given                   true
% 1.92/0.97  --inst_prop_sim_new                     false
% 1.92/0.97  --inst_subs_new                         false
% 1.92/0.97  --inst_eq_res_simp                      false
% 1.92/0.97  --inst_subs_given                       false
% 1.92/0.97  --inst_orphan_elimination               true
% 1.92/0.97  --inst_learning_loop_flag               true
% 1.92/0.97  --inst_learning_start                   3000
% 1.92/0.97  --inst_learning_factor                  2
% 1.92/0.97  --inst_start_prop_sim_after_learn       3
% 1.92/0.97  --inst_sel_renew                        solver
% 1.92/0.97  --inst_lit_activity_flag                true
% 1.92/0.97  --inst_restr_to_given                   false
% 1.92/0.97  --inst_activity_threshold               500
% 1.92/0.97  --inst_out_proof                        true
% 1.92/0.97  
% 1.92/0.97  ------ Resolution Options
% 1.92/0.97  
% 1.92/0.97  --resolution_flag                       true
% 1.92/0.97  --res_lit_sel                           adaptive
% 1.92/0.97  --res_lit_sel_side                      none
% 1.92/0.97  --res_ordering                          kbo
% 1.92/0.97  --res_to_prop_solver                    active
% 1.92/0.97  --res_prop_simpl_new                    false
% 1.92/0.97  --res_prop_simpl_given                  true
% 1.92/0.97  --res_passive_queue_type                priority_queues
% 1.92/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.92/0.98  --res_passive_queues_freq               [15;5]
% 1.92/0.98  --res_forward_subs                      full
% 1.92/0.98  --res_backward_subs                     full
% 1.92/0.98  --res_forward_subs_resolution           true
% 1.92/0.98  --res_backward_subs_resolution          true
% 1.92/0.98  --res_orphan_elimination                true
% 1.92/0.98  --res_time_limit                        2.
% 1.92/0.98  --res_out_proof                         true
% 1.92/0.98  
% 1.92/0.98  ------ Superposition Options
% 1.92/0.98  
% 1.92/0.98  --superposition_flag                    true
% 1.92/0.98  --sup_passive_queue_type                priority_queues
% 1.92/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.92/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.92/0.98  --demod_completeness_check              fast
% 1.92/0.98  --demod_use_ground                      true
% 1.92/0.98  --sup_to_prop_solver                    passive
% 1.92/0.98  --sup_prop_simpl_new                    true
% 1.92/0.98  --sup_prop_simpl_given                  true
% 1.92/0.98  --sup_fun_splitting                     false
% 1.92/0.98  --sup_smt_interval                      50000
% 1.92/0.98  
% 1.92/0.98  ------ Superposition Simplification Setup
% 1.92/0.98  
% 1.92/0.98  --sup_indices_passive                   []
% 1.92/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.92/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/0.98  --sup_full_bw                           [BwDemod]
% 1.92/0.98  --sup_immed_triv                        [TrivRules]
% 1.92/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.92/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/0.98  --sup_immed_bw_main                     []
% 1.92/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.92/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/0.98  
% 1.92/0.98  ------ Combination Options
% 1.92/0.98  
% 1.92/0.98  --comb_res_mult                         3
% 1.92/0.98  --comb_sup_mult                         2
% 1.92/0.98  --comb_inst_mult                        10
% 1.92/0.98  
% 1.92/0.98  ------ Debug Options
% 1.92/0.98  
% 1.92/0.98  --dbg_backtrace                         false
% 1.92/0.98  --dbg_dump_prop_clauses                 false
% 1.92/0.98  --dbg_dump_prop_clauses_file            -
% 1.92/0.98  --dbg_out_stat                          false
% 1.92/0.98  ------ Parsing...
% 1.92/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.92/0.98  
% 1.92/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.92/0.98  
% 1.92/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.92/0.98  
% 1.92/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.92/0.98  ------ Proving...
% 1.92/0.98  ------ Problem Properties 
% 1.92/0.98  
% 1.92/0.98  
% 1.92/0.98  clauses                                 18
% 1.92/0.98  conjectures                             3
% 1.92/0.98  EPR                                     4
% 1.92/0.98  Horn                                    16
% 1.92/0.98  unary                                   9
% 1.92/0.98  binary                                  8
% 1.92/0.98  lits                                    28
% 1.92/0.98  lits eq                                 8
% 1.92/0.98  fd_pure                                 0
% 1.92/0.98  fd_pseudo                               0
% 1.92/0.98  fd_cond                                 0
% 1.92/0.98  fd_pseudo_cond                          0
% 1.92/0.98  AC symbols                              0
% 1.92/0.98  
% 1.92/0.98  ------ Schedule dynamic 5 is on 
% 1.92/0.98  
% 1.92/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.92/0.98  
% 1.92/0.98  
% 1.92/0.98  ------ 
% 1.92/0.98  Current options:
% 1.92/0.98  ------ 
% 1.92/0.98  
% 1.92/0.98  ------ Input Options
% 1.92/0.98  
% 1.92/0.98  --out_options                           all
% 1.92/0.98  --tptp_safe_out                         true
% 1.92/0.98  --problem_path                          ""
% 1.92/0.98  --include_path                          ""
% 1.92/0.98  --clausifier                            res/vclausify_rel
% 1.92/0.98  --clausifier_options                    --mode clausify
% 1.92/0.98  --stdin                                 false
% 1.92/0.98  --stats_out                             all
% 1.92/0.98  
% 1.92/0.98  ------ General Options
% 1.92/0.98  
% 1.92/0.98  --fof                                   false
% 1.92/0.98  --time_out_real                         305.
% 1.92/0.98  --time_out_virtual                      -1.
% 1.92/0.98  --symbol_type_check                     false
% 1.92/0.98  --clausify_out                          false
% 1.92/0.98  --sig_cnt_out                           false
% 1.92/0.98  --trig_cnt_out                          false
% 1.92/0.98  --trig_cnt_out_tolerance                1.
% 1.92/0.98  --trig_cnt_out_sk_spl                   false
% 1.92/0.98  --abstr_cl_out                          false
% 1.92/0.98  
% 1.92/0.98  ------ Global Options
% 1.92/0.98  
% 1.92/0.98  --schedule                              default
% 1.92/0.98  --add_important_lit                     false
% 1.92/0.98  --prop_solver_per_cl                    1000
% 1.92/0.98  --min_unsat_core                        false
% 1.92/0.98  --soft_assumptions                      false
% 1.92/0.98  --soft_lemma_size                       3
% 1.92/0.98  --prop_impl_unit_size                   0
% 1.92/0.98  --prop_impl_unit                        []
% 1.92/0.98  --share_sel_clauses                     true
% 1.92/0.98  --reset_solvers                         false
% 1.92/0.98  --bc_imp_inh                            [conj_cone]
% 1.92/0.98  --conj_cone_tolerance                   3.
% 1.92/0.98  --extra_neg_conj                        none
% 1.92/0.98  --large_theory_mode                     true
% 1.92/0.98  --prolific_symb_bound                   200
% 1.92/0.98  --lt_threshold                          2000
% 1.92/0.98  --clause_weak_htbl                      true
% 1.92/0.98  --gc_record_bc_elim                     false
% 1.92/0.98  
% 1.92/0.98  ------ Preprocessing Options
% 1.92/0.98  
% 1.92/0.98  --preprocessing_flag                    true
% 1.92/0.98  --time_out_prep_mult                    0.1
% 1.92/0.98  --splitting_mode                        input
% 1.92/0.98  --splitting_grd                         true
% 1.92/0.98  --splitting_cvd                         false
% 1.92/0.98  --splitting_cvd_svl                     false
% 1.92/0.98  --splitting_nvd                         32
% 1.92/0.98  --sub_typing                            true
% 1.92/0.98  --prep_gs_sim                           true
% 1.92/0.98  --prep_unflatten                        true
% 1.92/0.98  --prep_res_sim                          true
% 1.92/0.98  --prep_upred                            true
% 1.92/0.98  --prep_sem_filter                       exhaustive
% 1.92/0.98  --prep_sem_filter_out                   false
% 1.92/0.98  --pred_elim                             true
% 1.92/0.98  --res_sim_input                         true
% 1.92/0.98  --eq_ax_congr_red                       true
% 1.92/0.98  --pure_diseq_elim                       true
% 1.92/0.98  --brand_transform                       false
% 1.92/0.98  --non_eq_to_eq                          false
% 1.92/0.98  --prep_def_merge                        true
% 1.92/0.98  --prep_def_merge_prop_impl              false
% 1.92/0.98  --prep_def_merge_mbd                    true
% 1.92/0.98  --prep_def_merge_tr_red                 false
% 1.92/0.98  --prep_def_merge_tr_cl                  false
% 1.92/0.98  --smt_preprocessing                     true
% 1.92/0.98  --smt_ac_axioms                         fast
% 1.92/0.98  --preprocessed_out                      false
% 1.92/0.98  --preprocessed_stats                    false
% 1.92/0.98  
% 1.92/0.98  ------ Abstraction refinement Options
% 1.92/0.98  
% 1.92/0.98  --abstr_ref                             []
% 1.92/0.98  --abstr_ref_prep                        false
% 1.92/0.98  --abstr_ref_until_sat                   false
% 1.92/0.98  --abstr_ref_sig_restrict                funpre
% 1.92/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.92/0.98  --abstr_ref_under                       []
% 1.92/0.98  
% 1.92/0.98  ------ SAT Options
% 1.92/0.98  
% 1.92/0.98  --sat_mode                              false
% 1.92/0.98  --sat_fm_restart_options                ""
% 1.92/0.98  --sat_gr_def                            false
% 1.92/0.98  --sat_epr_types                         true
% 1.92/0.98  --sat_non_cyclic_types                  false
% 1.92/0.98  --sat_finite_models                     false
% 1.92/0.98  --sat_fm_lemmas                         false
% 1.92/0.98  --sat_fm_prep                           false
% 1.92/0.98  --sat_fm_uc_incr                        true
% 1.92/0.98  --sat_out_model                         small
% 1.92/0.98  --sat_out_clauses                       false
% 1.92/0.98  
% 1.92/0.98  ------ QBF Options
% 1.92/0.98  
% 1.92/0.98  --qbf_mode                              false
% 1.92/0.98  --qbf_elim_univ                         false
% 1.92/0.98  --qbf_dom_inst                          none
% 1.92/0.98  --qbf_dom_pre_inst                      false
% 1.92/0.98  --qbf_sk_in                             false
% 1.92/0.98  --qbf_pred_elim                         true
% 1.92/0.98  --qbf_split                             512
% 1.92/0.98  
% 1.92/0.98  ------ BMC1 Options
% 1.92/0.98  
% 1.92/0.98  --bmc1_incremental                      false
% 1.92/0.98  --bmc1_axioms                           reachable_all
% 1.92/0.98  --bmc1_min_bound                        0
% 1.92/0.98  --bmc1_max_bound                        -1
% 1.92/0.98  --bmc1_max_bound_default                -1
% 1.92/0.98  --bmc1_symbol_reachability              true
% 1.92/0.98  --bmc1_property_lemmas                  false
% 1.92/0.98  --bmc1_k_induction                      false
% 1.92/0.98  --bmc1_non_equiv_states                 false
% 1.92/0.98  --bmc1_deadlock                         false
% 1.92/0.98  --bmc1_ucm                              false
% 1.92/0.98  --bmc1_add_unsat_core                   none
% 1.92/0.98  --bmc1_unsat_core_children              false
% 1.92/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.92/0.98  --bmc1_out_stat                         full
% 1.92/0.98  --bmc1_ground_init                      false
% 1.92/0.98  --bmc1_pre_inst_next_state              false
% 1.92/0.98  --bmc1_pre_inst_state                   false
% 1.92/0.98  --bmc1_pre_inst_reach_state             false
% 1.92/0.98  --bmc1_out_unsat_core                   false
% 1.92/0.98  --bmc1_aig_witness_out                  false
% 1.92/0.98  --bmc1_verbose                          false
% 1.92/0.98  --bmc1_dump_clauses_tptp                false
% 1.92/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.92/0.98  --bmc1_dump_file                        -
% 1.92/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.92/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.92/0.98  --bmc1_ucm_extend_mode                  1
% 1.92/0.98  --bmc1_ucm_init_mode                    2
% 1.92/0.98  --bmc1_ucm_cone_mode                    none
% 1.92/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.92/0.98  --bmc1_ucm_relax_model                  4
% 1.92/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.92/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.92/0.98  --bmc1_ucm_layered_model                none
% 1.92/0.98  --bmc1_ucm_max_lemma_size               10
% 1.92/0.98  
% 1.92/0.98  ------ AIG Options
% 1.92/0.98  
% 1.92/0.98  --aig_mode                              false
% 1.92/0.98  
% 1.92/0.98  ------ Instantiation Options
% 1.92/0.98  
% 1.92/0.98  --instantiation_flag                    true
% 1.92/0.98  --inst_sos_flag                         false
% 1.92/0.98  --inst_sos_phase                        true
% 1.92/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.92/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.92/0.98  --inst_lit_sel_side                     none
% 1.92/0.98  --inst_solver_per_active                1400
% 1.92/0.98  --inst_solver_calls_frac                1.
% 1.92/0.98  --inst_passive_queue_type               priority_queues
% 1.92/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.92/0.98  --inst_passive_queues_freq              [25;2]
% 1.92/0.98  --inst_dismatching                      true
% 1.92/0.98  --inst_eager_unprocessed_to_passive     true
% 1.92/0.98  --inst_prop_sim_given                   true
% 1.92/0.98  --inst_prop_sim_new                     false
% 1.92/0.98  --inst_subs_new                         false
% 1.92/0.98  --inst_eq_res_simp                      false
% 1.92/0.98  --inst_subs_given                       false
% 1.92/0.98  --inst_orphan_elimination               true
% 1.92/0.98  --inst_learning_loop_flag               true
% 1.92/0.98  --inst_learning_start                   3000
% 1.92/0.98  --inst_learning_factor                  2
% 1.92/0.98  --inst_start_prop_sim_after_learn       3
% 1.92/0.98  --inst_sel_renew                        solver
% 1.92/0.98  --inst_lit_activity_flag                true
% 1.92/0.98  --inst_restr_to_given                   false
% 1.92/0.98  --inst_activity_threshold               500
% 1.92/0.98  --inst_out_proof                        true
% 1.92/0.98  
% 1.92/0.98  ------ Resolution Options
% 1.92/0.98  
% 1.92/0.98  --resolution_flag                       false
% 1.92/0.98  --res_lit_sel                           adaptive
% 1.92/0.98  --res_lit_sel_side                      none
% 1.92/0.98  --res_ordering                          kbo
% 1.92/0.98  --res_to_prop_solver                    active
% 1.92/0.98  --res_prop_simpl_new                    false
% 1.92/0.98  --res_prop_simpl_given                  true
% 1.92/0.98  --res_passive_queue_type                priority_queues
% 1.92/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.92/0.98  --res_passive_queues_freq               [15;5]
% 1.92/0.98  --res_forward_subs                      full
% 1.92/0.98  --res_backward_subs                     full
% 1.92/0.98  --res_forward_subs_resolution           true
% 1.92/0.98  --res_backward_subs_resolution          true
% 1.92/0.98  --res_orphan_elimination                true
% 1.92/0.98  --res_time_limit                        2.
% 1.92/0.98  --res_out_proof                         true
% 1.92/0.98  
% 1.92/0.98  ------ Superposition Options
% 1.92/0.98  
% 1.92/0.98  --superposition_flag                    true
% 1.92/0.98  --sup_passive_queue_type                priority_queues
% 1.92/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.92/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.92/0.98  --demod_completeness_check              fast
% 1.92/0.98  --demod_use_ground                      true
% 1.92/0.98  --sup_to_prop_solver                    passive
% 1.92/0.98  --sup_prop_simpl_new                    true
% 1.92/0.98  --sup_prop_simpl_given                  true
% 1.92/0.98  --sup_fun_splitting                     false
% 1.92/0.98  --sup_smt_interval                      50000
% 1.92/0.98  
% 1.92/0.98  ------ Superposition Simplification Setup
% 1.92/0.98  
% 1.92/0.98  --sup_indices_passive                   []
% 1.92/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.92/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.92/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/0.98  --sup_full_bw                           [BwDemod]
% 1.92/0.98  --sup_immed_triv                        [TrivRules]
% 1.92/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.92/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/0.98  --sup_immed_bw_main                     []
% 1.92/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.92/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.92/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.92/0.98  
% 1.92/0.98  ------ Combination Options
% 1.92/0.98  
% 1.92/0.98  --comb_res_mult                         3
% 1.92/0.98  --comb_sup_mult                         2
% 1.92/0.98  --comb_inst_mult                        10
% 1.92/0.98  
% 1.92/0.98  ------ Debug Options
% 1.92/0.98  
% 1.92/0.98  --dbg_backtrace                         false
% 1.92/0.98  --dbg_dump_prop_clauses                 false
% 1.92/0.98  --dbg_dump_prop_clauses_file            -
% 1.92/0.98  --dbg_out_stat                          false
% 1.92/0.98  
% 1.92/0.98  
% 1.92/0.98  
% 1.92/0.98  
% 1.92/0.98  ------ Proving...
% 1.92/0.98  
% 1.92/0.98  
% 1.92/0.98  % SZS status Theorem for theBenchmark.p
% 1.92/0.98  
% 1.92/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.92/0.98  
% 1.92/0.98  fof(f13,conjecture,(
% 1.92/0.98    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/0.98  
% 1.92/0.98  fof(f14,negated_conjecture,(
% 1.92/0.98    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 1.92/0.98    inference(negated_conjecture,[],[f13])).
% 1.92/0.98  
% 1.92/0.98  fof(f20,plain,(
% 1.92/0.98    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 1.92/0.98    inference(ennf_transformation,[],[f14])).
% 1.92/0.98  
% 1.92/0.98  fof(f21,plain,(
% 1.92/0.98    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.92/0.98    inference(flattening,[],[f20])).
% 1.92/0.98  
% 1.92/0.98  fof(f29,plain,(
% 1.92/0.98    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK2,sK3) & r1_xboole_0(sK2,sK4) & r1_tarski(sK2,k2_xboole_0(sK3,sK4)))),
% 1.92/0.98    introduced(choice_axiom,[])).
% 1.92/0.98  
% 1.92/0.98  fof(f30,plain,(
% 1.92/0.98    ~r1_tarski(sK2,sK3) & r1_xboole_0(sK2,sK4) & r1_tarski(sK2,k2_xboole_0(sK3,sK4))),
% 1.92/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f21,f29])).
% 1.92/0.98  
% 1.92/0.98  fof(f47,plain,(
% 1.92/0.98    r1_tarski(sK2,k2_xboole_0(sK3,sK4))),
% 1.92/0.98    inference(cnf_transformation,[],[f30])).
% 1.92/0.98  
% 1.92/0.98  fof(f1,axiom,(
% 1.92/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/0.98  
% 1.92/0.98  fof(f31,plain,(
% 1.92/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.92/0.98    inference(cnf_transformation,[],[f1])).
% 1.92/0.98  
% 1.92/0.98  fof(f9,axiom,(
% 1.92/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 1.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/0.98  
% 1.92/0.98  fof(f19,plain,(
% 1.92/0.98    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 1.92/0.98    inference(ennf_transformation,[],[f9])).
% 1.92/0.98  
% 1.92/0.98  fof(f43,plain,(
% 1.92/0.98    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 1.92/0.98    inference(cnf_transformation,[],[f19])).
% 1.92/0.98  
% 1.92/0.98  fof(f48,plain,(
% 1.92/0.98    r1_xboole_0(sK2,sK4)),
% 1.92/0.98    inference(cnf_transformation,[],[f30])).
% 1.92/0.98  
% 1.92/0.98  fof(f3,axiom,(
% 1.92/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/0.98  
% 1.92/0.98  fof(f26,plain,(
% 1.92/0.98    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.92/0.98    inference(nnf_transformation,[],[f3])).
% 1.92/0.98  
% 1.92/0.98  fof(f35,plain,(
% 1.92/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.92/0.98    inference(cnf_transformation,[],[f26])).
% 1.92/0.98  
% 1.92/0.98  fof(f10,axiom,(
% 1.92/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/0.98  
% 1.92/0.98  fof(f44,plain,(
% 1.92/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.92/0.98    inference(cnf_transformation,[],[f10])).
% 1.92/0.98  
% 1.92/0.98  fof(f51,plain,(
% 1.92/0.98    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.92/0.98    inference(definition_unfolding,[],[f35,f44])).
% 1.92/0.98  
% 1.92/0.98  fof(f7,axiom,(
% 1.92/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/0.98  
% 1.92/0.98  fof(f41,plain,(
% 1.92/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.92/0.98    inference(cnf_transformation,[],[f7])).
% 1.92/0.98  
% 1.92/0.98  fof(f6,axiom,(
% 1.92/0.98    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 1.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/0.98  
% 1.92/0.98  fof(f40,plain,(
% 1.92/0.98    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 1.92/0.98    inference(cnf_transformation,[],[f6])).
% 1.92/0.98  
% 1.92/0.98  fof(f54,plain,(
% 1.92/0.98    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.92/0.98    inference(definition_unfolding,[],[f40,f44])).
% 1.92/0.98  
% 1.92/0.98  fof(f8,axiom,(
% 1.92/0.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/0.98  
% 1.92/0.98  fof(f42,plain,(
% 1.92/0.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.92/0.98    inference(cnf_transformation,[],[f8])).
% 1.92/0.98  
% 1.92/0.98  fof(f11,axiom,(
% 1.92/0.98    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.92/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.92/0.98  
% 1.92/0.98  fof(f45,plain,(
% 1.92/0.98    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.92/0.98    inference(cnf_transformation,[],[f11])).
% 1.92/0.98  
% 1.92/0.98  fof(f55,plain,(
% 1.92/0.98    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.92/0.98    inference(definition_unfolding,[],[f45,f44])).
% 1.92/0.98  
% 1.92/0.98  fof(f49,plain,(
% 1.92/0.98    ~r1_tarski(sK2,sK3)),
% 1.92/0.98    inference(cnf_transformation,[],[f30])).
% 1.92/0.98  
% 1.92/0.98  cnf(c_17,negated_conjecture,
% 1.92/0.98      ( r1_tarski(sK2,k2_xboole_0(sK3,sK4)) ),
% 1.92/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_590,plain,
% 1.92/0.98      ( r1_tarski(sK2,k2_xboole_0(sK3,sK4)) = iProver_top ),
% 1.92/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_0,plain,
% 1.92/0.98      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 1.92/0.98      inference(cnf_transformation,[],[f31]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_12,plain,
% 1.92/0.98      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 1.92/0.98      | r1_tarski(k4_xboole_0(X0,X1),X2) ),
% 1.92/0.98      inference(cnf_transformation,[],[f43]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_594,plain,
% 1.92/0.98      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 1.92/0.98      | r1_tarski(k4_xboole_0(X0,X1),X2) = iProver_top ),
% 1.92/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_1621,plain,
% 1.92/0.98      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 1.92/0.98      | r1_tarski(k4_xboole_0(X0,X2),X1) = iProver_top ),
% 1.92/0.98      inference(superposition,[status(thm)],[c_0,c_594]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_2779,plain,
% 1.92/0.98      ( r1_tarski(k4_xboole_0(sK2,sK4),sK3) = iProver_top ),
% 1.92/0.98      inference(superposition,[status(thm)],[c_590,c_1621]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_16,negated_conjecture,
% 1.92/0.98      ( r1_xboole_0(sK2,sK4) ),
% 1.92/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_591,plain,
% 1.92/0.98      ( r1_xboole_0(sK2,sK4) = iProver_top ),
% 1.92/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_5,plain,
% 1.92/0.98      ( ~ r1_xboole_0(X0,X1)
% 1.92/0.98      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 1.92/0.98      inference(cnf_transformation,[],[f51]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_598,plain,
% 1.92/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 1.92/0.98      | r1_xboole_0(X0,X1) != iProver_top ),
% 1.92/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_1490,plain,
% 1.92/0.98      ( k4_xboole_0(sK2,k4_xboole_0(sK2,sK4)) = k1_xboole_0 ),
% 1.92/0.98      inference(superposition,[status(thm)],[c_591,c_598]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_10,plain,
% 1.92/0.98      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 1.92/0.98      inference(cnf_transformation,[],[f41]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_1504,plain,
% 1.92/0.98      ( k2_xboole_0(k4_xboole_0(sK2,sK4),sK2) = k2_xboole_0(k4_xboole_0(sK2,sK4),k1_xboole_0) ),
% 1.92/0.98      inference(superposition,[status(thm)],[c_1490,c_10]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_9,plain,
% 1.92/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 1.92/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_11,plain,
% 1.92/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.92/0.98      inference(cnf_transformation,[],[f42]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_613,plain,
% 1.92/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 1.92/0.98      inference(light_normalisation,[status(thm)],[c_9,c_11]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_13,plain,
% 1.92/0.98      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 1.92/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_931,plain,
% 1.92/0.98      ( k2_xboole_0(k4_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
% 1.92/0.98      inference(superposition,[status(thm)],[c_613,c_13]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_937,plain,
% 1.92/0.98      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.92/0.98      inference(light_normalisation,[status(thm)],[c_931,c_11]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_932,plain,
% 1.92/0.98      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 1.92/0.98      inference(superposition,[status(thm)],[c_13,c_0]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_1012,plain,
% 1.92/0.98      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 1.92/0.98      inference(superposition,[status(thm)],[c_932,c_10]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_1506,plain,
% 1.92/0.98      ( k4_xboole_0(sK2,sK4) = sK2 ),
% 1.92/0.98      inference(demodulation,[status(thm)],[c_1504,c_937,c_1012]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_2811,plain,
% 1.92/0.98      ( r1_tarski(sK2,sK3) = iProver_top ),
% 1.92/0.98      inference(light_normalisation,[status(thm)],[c_2779,c_1506]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_15,negated_conjecture,
% 1.92/0.98      ( ~ r1_tarski(sK2,sK3) ),
% 1.92/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(c_20,plain,
% 1.92/0.98      ( r1_tarski(sK2,sK3) != iProver_top ),
% 1.92/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.92/0.98  
% 1.92/0.98  cnf(contradiction,plain,
% 1.92/0.98      ( $false ),
% 1.92/0.98      inference(minisat,[status(thm)],[c_2811,c_20]) ).
% 1.92/0.98  
% 1.92/0.98  
% 1.92/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.92/0.98  
% 1.92/0.98  ------                               Statistics
% 1.92/0.98  
% 1.92/0.98  ------ General
% 1.92/0.98  
% 1.92/0.98  abstr_ref_over_cycles:                  0
% 1.92/0.98  abstr_ref_under_cycles:                 0
% 1.92/0.98  gc_basic_clause_elim:                   0
% 1.92/0.98  forced_gc_time:                         0
% 1.92/0.98  parsing_time:                           0.007
% 1.92/0.98  unif_index_cands_time:                  0.
% 1.92/0.98  unif_index_add_time:                    0.
% 1.92/0.98  orderings_time:                         0.
% 1.92/0.98  out_proof_time:                         0.007
% 1.92/0.98  total_time:                             0.107
% 1.92/0.98  num_of_symbols:                         42
% 1.92/0.98  num_of_terms:                           2878
% 1.92/0.98  
% 1.92/0.98  ------ Preprocessing
% 1.92/0.98  
% 1.92/0.98  num_of_splits:                          0
% 1.92/0.98  num_of_split_atoms:                     0
% 1.92/0.98  num_of_reused_defs:                     0
% 1.92/0.98  num_eq_ax_congr_red:                    10
% 1.92/0.98  num_of_sem_filtered_clauses:            1
% 1.92/0.98  num_of_subtypes:                        0
% 1.92/0.98  monotx_restored_types:                  0
% 1.92/0.98  sat_num_of_epr_types:                   0
% 1.92/0.98  sat_num_of_non_cyclic_types:            0
% 1.92/0.98  sat_guarded_non_collapsed_types:        0
% 1.92/0.98  num_pure_diseq_elim:                    0
% 1.92/0.98  simp_replaced_by:                       0
% 1.92/0.98  res_preprocessed:                       69
% 1.92/0.98  prep_upred:                             0
% 1.92/0.98  prep_unflattend:                        8
% 1.92/0.98  smt_new_axioms:                         0
% 1.92/0.98  pred_elim_cands:                        3
% 1.92/0.98  pred_elim:                              0
% 1.92/0.98  pred_elim_cl:                           0
% 1.92/0.98  pred_elim_cycles:                       1
% 1.92/0.98  merged_defs:                            6
% 1.92/0.98  merged_defs_ncl:                        0
% 1.92/0.98  bin_hyper_res:                          6
% 1.92/0.98  prep_cycles:                            3
% 1.92/0.98  pred_elim_time:                         0.001
% 1.92/0.98  splitting_time:                         0.
% 1.92/0.98  sem_filter_time:                        0.
% 1.92/0.98  monotx_time:                            0.
% 1.92/0.98  subtype_inf_time:                       0.
% 1.92/0.98  
% 1.92/0.98  ------ Problem properties
% 1.92/0.98  
% 1.92/0.98  clauses:                                18
% 1.92/0.98  conjectures:                            3
% 1.92/0.98  epr:                                    4
% 1.92/0.98  horn:                                   16
% 1.92/0.98  ground:                                 3
% 1.92/0.98  unary:                                  9
% 1.92/0.98  binary:                                 8
% 1.92/0.98  lits:                                   28
% 1.92/0.98  lits_eq:                                8
% 1.92/0.98  fd_pure:                                0
% 1.92/0.98  fd_pseudo:                              0
% 1.92/0.98  fd_cond:                                0
% 1.92/0.98  fd_pseudo_cond:                         0
% 1.92/0.98  ac_symbols:                             0
% 1.92/0.98  
% 1.92/0.98  ------ Propositional Solver
% 1.92/0.98  
% 1.92/0.98  prop_solver_calls:                      24
% 1.92/0.98  prop_fast_solver_calls:                 317
% 1.92/0.98  smt_solver_calls:                       0
% 1.92/0.98  smt_fast_solver_calls:                  0
% 1.92/0.98  prop_num_of_clauses:                    1205
% 1.92/0.98  prop_preprocess_simplified:             3119
% 1.92/0.98  prop_fo_subsumed:                       1
% 1.92/0.98  prop_solver_time:                       0.
% 1.92/0.98  smt_solver_time:                        0.
% 1.92/0.98  smt_fast_solver_time:                   0.
% 1.92/0.98  prop_fast_solver_time:                  0.
% 1.92/0.98  prop_unsat_core_time:                   0.
% 1.92/0.98  
% 1.92/0.98  ------ QBF
% 1.92/0.98  
% 1.92/0.98  qbf_q_res:                              0
% 1.92/0.98  qbf_num_tautologies:                    0
% 1.92/0.98  qbf_prep_cycles:                        0
% 1.92/0.98  
% 1.92/0.98  ------ BMC1
% 1.92/0.98  
% 1.92/0.98  bmc1_current_bound:                     -1
% 1.92/0.98  bmc1_last_solved_bound:                 -1
% 1.92/0.98  bmc1_unsat_core_size:                   -1
% 1.92/0.98  bmc1_unsat_core_parents_size:           -1
% 1.92/0.98  bmc1_merge_next_fun:                    0
% 1.92/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.92/0.98  
% 1.92/0.98  ------ Instantiation
% 1.92/0.98  
% 1.92/0.98  inst_num_of_clauses:                    337
% 1.92/0.98  inst_num_in_passive:                    70
% 1.92/0.98  inst_num_in_active:                     154
% 1.92/0.98  inst_num_in_unprocessed:                113
% 1.92/0.98  inst_num_of_loops:                      190
% 1.92/0.98  inst_num_of_learning_restarts:          0
% 1.92/0.98  inst_num_moves_active_passive:          32
% 1.92/0.98  inst_lit_activity:                      0
% 1.92/0.98  inst_lit_activity_moves:                0
% 1.92/0.98  inst_num_tautologies:                   0
% 1.92/0.98  inst_num_prop_implied:                  0
% 1.92/0.98  inst_num_existing_simplified:           0
% 1.92/0.98  inst_num_eq_res_simplified:             0
% 1.92/0.98  inst_num_child_elim:                    0
% 1.92/0.98  inst_num_of_dismatching_blockings:      87
% 1.92/0.98  inst_num_of_non_proper_insts:           268
% 1.92/0.98  inst_num_of_duplicates:                 0
% 1.92/0.98  inst_inst_num_from_inst_to_res:         0
% 1.92/0.98  inst_dismatching_checking_time:         0.
% 1.92/0.98  
% 1.92/0.98  ------ Resolution
% 1.92/0.98  
% 1.92/0.98  res_num_of_clauses:                     0
% 1.92/0.98  res_num_in_passive:                     0
% 1.92/0.98  res_num_in_active:                      0
% 1.92/0.98  res_num_of_loops:                       72
% 1.92/0.98  res_forward_subset_subsumed:            10
% 1.92/0.98  res_backward_subset_subsumed:           0
% 1.92/0.98  res_forward_subsumed:                   0
% 1.92/0.98  res_backward_subsumed:                  0
% 1.92/0.98  res_forward_subsumption_resolution:     0
% 1.92/0.98  res_backward_subsumption_resolution:    0
% 1.92/0.98  res_clause_to_clause_subsumption:       207
% 1.92/0.98  res_orphan_elimination:                 0
% 1.92/0.98  res_tautology_del:                      31
% 1.92/0.98  res_num_eq_res_simplified:              0
% 1.92/0.98  res_num_sel_changes:                    0
% 1.92/0.98  res_moves_from_active_to_pass:          0
% 1.92/0.98  
% 1.92/0.98  ------ Superposition
% 1.92/0.98  
% 1.92/0.98  sup_time_total:                         0.
% 1.92/0.98  sup_time_generating:                    0.
% 1.92/0.98  sup_time_sim_full:                      0.
% 1.92/0.98  sup_time_sim_immed:                     0.
% 1.92/0.98  
% 1.92/0.98  sup_num_of_clauses:                     58
% 1.92/0.98  sup_num_in_active:                      36
% 1.92/0.98  sup_num_in_passive:                     22
% 1.92/0.98  sup_num_of_loops:                       36
% 1.92/0.98  sup_fw_superposition:                   80
% 1.92/0.98  sup_bw_superposition:                   46
% 1.92/0.98  sup_immediate_simplified:               45
% 1.92/0.98  sup_given_eliminated:                   1
% 1.92/0.98  comparisons_done:                       0
% 1.92/0.98  comparisons_avoided:                    0
% 1.92/0.98  
% 1.92/0.98  ------ Simplifications
% 1.92/0.98  
% 1.92/0.98  
% 1.92/0.98  sim_fw_subset_subsumed:                 8
% 1.92/0.98  sim_bw_subset_subsumed:                 0
% 1.92/0.98  sim_fw_subsumed:                        8
% 1.92/0.98  sim_bw_subsumed:                        0
% 1.92/0.98  sim_fw_subsumption_res:                 0
% 1.92/0.98  sim_bw_subsumption_res:                 0
% 1.92/0.98  sim_tautology_del:                      3
% 1.92/0.98  sim_eq_tautology_del:                   9
% 1.92/0.98  sim_eq_res_simp:                        1
% 1.92/0.98  sim_fw_demodulated:                     15
% 1.92/0.98  sim_bw_demodulated:                     1
% 1.92/0.98  sim_light_normalised:                   17
% 1.92/0.98  sim_joinable_taut:                      0
% 1.92/0.98  sim_joinable_simp:                      0
% 1.92/0.98  sim_ac_normalised:                      0
% 1.92/0.98  sim_smt_subsumption:                    0
% 1.92/0.98  
%------------------------------------------------------------------------------
