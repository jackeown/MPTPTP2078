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
% DateTime   : Thu Dec  3 11:31:36 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 101 expanded)
%              Number of clauses        :   22 (  25 expanded)
%              Number of leaves         :   13 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   77 ( 130 expanded)
%              Number of equality atoms :   76 ( 129 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X1,X1)) = k2_tarski(X0,X0)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f24,f22,f22])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f16,f19,f19])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
    inference(definition_unfolding,[],[f18,f27,f19])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f17,f19])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) = k2_tarski(X0,X0) ),
    inference(definition_unfolding,[],[f23,f19,f22,f22])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k2_tarski(X0,X1)
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k2_tarski(X0,X1)
        & X0 != X1 )
   => ( k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_tarski(sK0,sK1)
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_tarski(sK0,sK1)
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f26,plain,(
    k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) != k2_tarski(sK0,sK1) ),
    inference(definition_unfolding,[],[f26,f22,f22])).

fof(f25,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_3,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_5,plain,
    ( X0 = X1
    | k4_xboole_0(k2_tarski(X1,X0),k2_tarski(X0,X0)) = k2_tarski(X1,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_300,plain,
    ( X0 = X1
    | k4_xboole_0(k2_tarski(X1,X0),k2_tarski(X1,X1)) = k2_tarski(X0,X0) ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_43,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_2,c_0])).

cnf(c_197,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_43])).

cnf(c_1291,plain,
    ( X0 = X1
    | k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)))))) = k2_tarski(X0,X1) ),
    inference(superposition,[status(thm)],[c_300,c_197])).

cnf(c_4,plain,
    ( k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_176,plain,
    ( k4_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))) = k2_tarski(X0,X0) ),
    inference(superposition,[status(thm)],[c_4,c_1])).

cnf(c_1465,plain,
    ( X0 = X1
    | k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) = k2_tarski(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1291,c_4,c_176])).

cnf(c_6,negated_conjecture,
    ( k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) != k2_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2754,plain,
    ( k2_tarski(sK1,sK0) != k2_tarski(sK0,sK1)
    | sK1 = sK0 ),
    inference(superposition,[status(thm)],[c_1465,c_6])).

cnf(c_1686,plain,
    ( k2_tarski(sK1,sK0) = k2_tarski(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_20,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_49,plain,
    ( sK1 != X0
    | sK0 != X0
    | sK0 = sK1 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_50,plain,
    ( sK1 != sK0
    | sK0 = sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_49])).

cnf(c_19,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_26,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_7,negated_conjecture,
    ( sK0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2754,c_1686,c_50,c_26,c_7])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:32:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.20/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.20/1.05  
% 2.20/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.20/1.05  
% 2.20/1.05  ------  iProver source info
% 2.20/1.05  
% 2.20/1.05  git: date: 2020-06-30 10:37:57 +0100
% 2.20/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.20/1.05  git: non_committed_changes: false
% 2.20/1.05  git: last_make_outside_of_git: false
% 2.20/1.05  
% 2.20/1.05  ------ 
% 2.20/1.05  
% 2.20/1.05  ------ Input Options
% 2.20/1.05  
% 2.20/1.05  --out_options                           all
% 2.20/1.05  --tptp_safe_out                         true
% 2.20/1.05  --problem_path                          ""
% 2.20/1.05  --include_path                          ""
% 2.20/1.05  --clausifier                            res/vclausify_rel
% 2.20/1.05  --clausifier_options                    --mode clausify
% 2.20/1.05  --stdin                                 false
% 2.20/1.05  --stats_out                             all
% 2.20/1.05  
% 2.20/1.05  ------ General Options
% 2.20/1.05  
% 2.20/1.05  --fof                                   false
% 2.20/1.05  --time_out_real                         305.
% 2.20/1.05  --time_out_virtual                      -1.
% 2.20/1.05  --symbol_type_check                     false
% 2.20/1.05  --clausify_out                          false
% 2.20/1.05  --sig_cnt_out                           false
% 2.20/1.05  --trig_cnt_out                          false
% 2.20/1.05  --trig_cnt_out_tolerance                1.
% 2.20/1.05  --trig_cnt_out_sk_spl                   false
% 2.20/1.05  --abstr_cl_out                          false
% 2.20/1.05  
% 2.20/1.05  ------ Global Options
% 2.20/1.05  
% 2.20/1.05  --schedule                              default
% 2.20/1.05  --add_important_lit                     false
% 2.20/1.05  --prop_solver_per_cl                    1000
% 2.20/1.05  --min_unsat_core                        false
% 2.20/1.05  --soft_assumptions                      false
% 2.20/1.05  --soft_lemma_size                       3
% 2.20/1.05  --prop_impl_unit_size                   0
% 2.20/1.05  --prop_impl_unit                        []
% 2.20/1.05  --share_sel_clauses                     true
% 2.20/1.05  --reset_solvers                         false
% 2.20/1.05  --bc_imp_inh                            [conj_cone]
% 2.20/1.05  --conj_cone_tolerance                   3.
% 2.20/1.05  --extra_neg_conj                        none
% 2.20/1.05  --large_theory_mode                     true
% 2.20/1.05  --prolific_symb_bound                   200
% 2.20/1.05  --lt_threshold                          2000
% 2.20/1.05  --clause_weak_htbl                      true
% 2.20/1.05  --gc_record_bc_elim                     false
% 2.20/1.05  
% 2.20/1.05  ------ Preprocessing Options
% 2.20/1.05  
% 2.20/1.05  --preprocessing_flag                    true
% 2.20/1.05  --time_out_prep_mult                    0.1
% 2.20/1.05  --splitting_mode                        input
% 2.20/1.05  --splitting_grd                         true
% 2.20/1.05  --splitting_cvd                         false
% 2.20/1.05  --splitting_cvd_svl                     false
% 2.20/1.05  --splitting_nvd                         32
% 2.20/1.05  --sub_typing                            true
% 2.20/1.05  --prep_gs_sim                           true
% 2.20/1.05  --prep_unflatten                        true
% 2.20/1.05  --prep_res_sim                          true
% 2.20/1.05  --prep_upred                            true
% 2.20/1.05  --prep_sem_filter                       exhaustive
% 2.20/1.05  --prep_sem_filter_out                   false
% 2.20/1.05  --pred_elim                             true
% 2.20/1.05  --res_sim_input                         true
% 2.20/1.05  --eq_ax_congr_red                       true
% 2.20/1.05  --pure_diseq_elim                       true
% 2.20/1.05  --brand_transform                       false
% 2.20/1.05  --non_eq_to_eq                          false
% 2.20/1.05  --prep_def_merge                        true
% 2.20/1.05  --prep_def_merge_prop_impl              false
% 2.20/1.05  --prep_def_merge_mbd                    true
% 2.20/1.05  --prep_def_merge_tr_red                 false
% 2.20/1.05  --prep_def_merge_tr_cl                  false
% 2.20/1.05  --smt_preprocessing                     true
% 2.20/1.05  --smt_ac_axioms                         fast
% 2.20/1.05  --preprocessed_out                      false
% 2.20/1.05  --preprocessed_stats                    false
% 2.20/1.05  
% 2.20/1.05  ------ Abstraction refinement Options
% 2.20/1.05  
% 2.20/1.05  --abstr_ref                             []
% 2.20/1.05  --abstr_ref_prep                        false
% 2.20/1.05  --abstr_ref_until_sat                   false
% 2.20/1.05  --abstr_ref_sig_restrict                funpre
% 2.20/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.20/1.05  --abstr_ref_under                       []
% 2.20/1.05  
% 2.20/1.05  ------ SAT Options
% 2.20/1.05  
% 2.20/1.05  --sat_mode                              false
% 2.20/1.05  --sat_fm_restart_options                ""
% 2.20/1.05  --sat_gr_def                            false
% 2.20/1.05  --sat_epr_types                         true
% 2.20/1.05  --sat_non_cyclic_types                  false
% 2.20/1.05  --sat_finite_models                     false
% 2.20/1.05  --sat_fm_lemmas                         false
% 2.20/1.05  --sat_fm_prep                           false
% 2.20/1.05  --sat_fm_uc_incr                        true
% 2.20/1.05  --sat_out_model                         small
% 2.20/1.05  --sat_out_clauses                       false
% 2.20/1.05  
% 2.20/1.05  ------ QBF Options
% 2.20/1.05  
% 2.20/1.05  --qbf_mode                              false
% 2.20/1.05  --qbf_elim_univ                         false
% 2.20/1.05  --qbf_dom_inst                          none
% 2.20/1.05  --qbf_dom_pre_inst                      false
% 2.20/1.05  --qbf_sk_in                             false
% 2.20/1.05  --qbf_pred_elim                         true
% 2.20/1.05  --qbf_split                             512
% 2.20/1.05  
% 2.20/1.05  ------ BMC1 Options
% 2.20/1.05  
% 2.20/1.05  --bmc1_incremental                      false
% 2.20/1.05  --bmc1_axioms                           reachable_all
% 2.20/1.05  --bmc1_min_bound                        0
% 2.20/1.05  --bmc1_max_bound                        -1
% 2.20/1.05  --bmc1_max_bound_default                -1
% 2.20/1.05  --bmc1_symbol_reachability              true
% 2.20/1.05  --bmc1_property_lemmas                  false
% 2.20/1.05  --bmc1_k_induction                      false
% 2.20/1.05  --bmc1_non_equiv_states                 false
% 2.20/1.05  --bmc1_deadlock                         false
% 2.20/1.05  --bmc1_ucm                              false
% 2.20/1.05  --bmc1_add_unsat_core                   none
% 2.20/1.05  --bmc1_unsat_core_children              false
% 2.20/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.20/1.05  --bmc1_out_stat                         full
% 2.20/1.05  --bmc1_ground_init                      false
% 2.20/1.05  --bmc1_pre_inst_next_state              false
% 2.20/1.05  --bmc1_pre_inst_state                   false
% 2.20/1.05  --bmc1_pre_inst_reach_state             false
% 2.20/1.05  --bmc1_out_unsat_core                   false
% 2.20/1.05  --bmc1_aig_witness_out                  false
% 2.20/1.05  --bmc1_verbose                          false
% 2.20/1.05  --bmc1_dump_clauses_tptp                false
% 2.20/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.20/1.05  --bmc1_dump_file                        -
% 2.20/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.20/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.20/1.05  --bmc1_ucm_extend_mode                  1
% 2.20/1.05  --bmc1_ucm_init_mode                    2
% 2.20/1.05  --bmc1_ucm_cone_mode                    none
% 2.20/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.20/1.05  --bmc1_ucm_relax_model                  4
% 2.20/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.20/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.20/1.05  --bmc1_ucm_layered_model                none
% 2.20/1.05  --bmc1_ucm_max_lemma_size               10
% 2.20/1.05  
% 2.20/1.05  ------ AIG Options
% 2.20/1.05  
% 2.20/1.05  --aig_mode                              false
% 2.20/1.05  
% 2.20/1.05  ------ Instantiation Options
% 2.20/1.05  
% 2.20/1.05  --instantiation_flag                    true
% 2.20/1.05  --inst_sos_flag                         false
% 2.20/1.05  --inst_sos_phase                        true
% 2.20/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.20/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.20/1.05  --inst_lit_sel_side                     num_symb
% 2.20/1.05  --inst_solver_per_active                1400
% 2.20/1.05  --inst_solver_calls_frac                1.
% 2.20/1.05  --inst_passive_queue_type               priority_queues
% 2.20/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.20/1.05  --inst_passive_queues_freq              [25;2]
% 2.20/1.05  --inst_dismatching                      true
% 2.20/1.05  --inst_eager_unprocessed_to_passive     true
% 2.20/1.05  --inst_prop_sim_given                   true
% 2.20/1.05  --inst_prop_sim_new                     false
% 2.20/1.05  --inst_subs_new                         false
% 2.20/1.05  --inst_eq_res_simp                      false
% 2.20/1.05  --inst_subs_given                       false
% 2.20/1.05  --inst_orphan_elimination               true
% 2.20/1.05  --inst_learning_loop_flag               true
% 2.20/1.05  --inst_learning_start                   3000
% 2.20/1.05  --inst_learning_factor                  2
% 2.20/1.05  --inst_start_prop_sim_after_learn       3
% 2.20/1.05  --inst_sel_renew                        solver
% 2.20/1.05  --inst_lit_activity_flag                true
% 2.20/1.05  --inst_restr_to_given                   false
% 2.20/1.05  --inst_activity_threshold               500
% 2.20/1.05  --inst_out_proof                        true
% 2.20/1.05  
% 2.20/1.05  ------ Resolution Options
% 2.20/1.05  
% 2.20/1.05  --resolution_flag                       true
% 2.20/1.05  --res_lit_sel                           adaptive
% 2.20/1.05  --res_lit_sel_side                      none
% 2.20/1.05  --res_ordering                          kbo
% 2.20/1.05  --res_to_prop_solver                    active
% 2.20/1.05  --res_prop_simpl_new                    false
% 2.20/1.05  --res_prop_simpl_given                  true
% 2.20/1.05  --res_passive_queue_type                priority_queues
% 2.20/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.20/1.05  --res_passive_queues_freq               [15;5]
% 2.20/1.05  --res_forward_subs                      full
% 2.20/1.05  --res_backward_subs                     full
% 2.20/1.05  --res_forward_subs_resolution           true
% 2.20/1.05  --res_backward_subs_resolution          true
% 2.20/1.05  --res_orphan_elimination                true
% 2.20/1.05  --res_time_limit                        2.
% 2.20/1.05  --res_out_proof                         true
% 2.20/1.05  
% 2.20/1.05  ------ Superposition Options
% 2.20/1.05  
% 2.20/1.05  --superposition_flag                    true
% 2.20/1.05  --sup_passive_queue_type                priority_queues
% 2.20/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.20/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.20/1.05  --demod_completeness_check              fast
% 2.20/1.05  --demod_use_ground                      true
% 2.20/1.05  --sup_to_prop_solver                    passive
% 2.20/1.05  --sup_prop_simpl_new                    true
% 2.20/1.05  --sup_prop_simpl_given                  true
% 2.20/1.05  --sup_fun_splitting                     false
% 2.20/1.05  --sup_smt_interval                      50000
% 2.20/1.05  
% 2.20/1.05  ------ Superposition Simplification Setup
% 2.20/1.05  
% 2.20/1.05  --sup_indices_passive                   []
% 2.20/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.20/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.05  --sup_full_bw                           [BwDemod]
% 2.20/1.05  --sup_immed_triv                        [TrivRules]
% 2.20/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.20/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.05  --sup_immed_bw_main                     []
% 2.20/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.20/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/1.05  
% 2.20/1.05  ------ Combination Options
% 2.20/1.05  
% 2.20/1.05  --comb_res_mult                         3
% 2.20/1.05  --comb_sup_mult                         2
% 2.20/1.05  --comb_inst_mult                        10
% 2.20/1.05  
% 2.20/1.05  ------ Debug Options
% 2.20/1.05  
% 2.20/1.05  --dbg_backtrace                         false
% 2.20/1.05  --dbg_dump_prop_clauses                 false
% 2.20/1.05  --dbg_dump_prop_clauses_file            -
% 2.20/1.05  --dbg_out_stat                          false
% 2.20/1.05  ------ Parsing...
% 2.20/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.20/1.05  
% 2.20/1.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.20/1.05  
% 2.20/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.20/1.05  
% 2.20/1.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.20/1.05  ------ Proving...
% 2.20/1.05  ------ Problem Properties 
% 2.20/1.05  
% 2.20/1.05  
% 2.20/1.05  clauses                                 8
% 2.20/1.05  conjectures                             2
% 2.20/1.05  EPR                                     1
% 2.20/1.05  Horn                                    7
% 2.20/1.05  unary                                   7
% 2.20/1.05  binary                                  1
% 2.20/1.05  lits                                    9
% 2.20/1.05  lits eq                                 9
% 2.20/1.05  fd_pure                                 0
% 2.20/1.05  fd_pseudo                               0
% 2.20/1.05  fd_cond                                 0
% 2.20/1.05  fd_pseudo_cond                          1
% 2.20/1.05  AC symbols                              0
% 2.20/1.05  
% 2.20/1.05  ------ Schedule dynamic 5 is on 
% 2.20/1.05  
% 2.20/1.05  ------ pure equality problem: resolution off 
% 2.20/1.05  
% 2.20/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.20/1.05  
% 2.20/1.05  
% 2.20/1.05  ------ 
% 2.20/1.05  Current options:
% 2.20/1.05  ------ 
% 2.20/1.05  
% 2.20/1.05  ------ Input Options
% 2.20/1.05  
% 2.20/1.05  --out_options                           all
% 2.20/1.05  --tptp_safe_out                         true
% 2.20/1.05  --problem_path                          ""
% 2.20/1.05  --include_path                          ""
% 2.20/1.05  --clausifier                            res/vclausify_rel
% 2.20/1.05  --clausifier_options                    --mode clausify
% 2.20/1.05  --stdin                                 false
% 2.20/1.05  --stats_out                             all
% 2.20/1.05  
% 2.20/1.05  ------ General Options
% 2.20/1.05  
% 2.20/1.05  --fof                                   false
% 2.20/1.05  --time_out_real                         305.
% 2.20/1.05  --time_out_virtual                      -1.
% 2.20/1.05  --symbol_type_check                     false
% 2.20/1.05  --clausify_out                          false
% 2.20/1.05  --sig_cnt_out                           false
% 2.20/1.05  --trig_cnt_out                          false
% 2.20/1.05  --trig_cnt_out_tolerance                1.
% 2.20/1.05  --trig_cnt_out_sk_spl                   false
% 2.20/1.05  --abstr_cl_out                          false
% 2.20/1.05  
% 2.20/1.05  ------ Global Options
% 2.20/1.05  
% 2.20/1.05  --schedule                              default
% 2.20/1.05  --add_important_lit                     false
% 2.20/1.05  --prop_solver_per_cl                    1000
% 2.20/1.05  --min_unsat_core                        false
% 2.20/1.05  --soft_assumptions                      false
% 2.20/1.05  --soft_lemma_size                       3
% 2.20/1.05  --prop_impl_unit_size                   0
% 2.20/1.05  --prop_impl_unit                        []
% 2.20/1.05  --share_sel_clauses                     true
% 2.20/1.05  --reset_solvers                         false
% 2.20/1.05  --bc_imp_inh                            [conj_cone]
% 2.20/1.05  --conj_cone_tolerance                   3.
% 2.20/1.05  --extra_neg_conj                        none
% 2.20/1.05  --large_theory_mode                     true
% 2.20/1.05  --prolific_symb_bound                   200
% 2.20/1.05  --lt_threshold                          2000
% 2.20/1.05  --clause_weak_htbl                      true
% 2.20/1.05  --gc_record_bc_elim                     false
% 2.20/1.05  
% 2.20/1.05  ------ Preprocessing Options
% 2.20/1.05  
% 2.20/1.05  --preprocessing_flag                    true
% 2.20/1.05  --time_out_prep_mult                    0.1
% 2.20/1.05  --splitting_mode                        input
% 2.20/1.05  --splitting_grd                         true
% 2.20/1.05  --splitting_cvd                         false
% 2.20/1.05  --splitting_cvd_svl                     false
% 2.20/1.05  --splitting_nvd                         32
% 2.20/1.05  --sub_typing                            true
% 2.20/1.05  --prep_gs_sim                           true
% 2.20/1.05  --prep_unflatten                        true
% 2.20/1.05  --prep_res_sim                          true
% 2.20/1.05  --prep_upred                            true
% 2.20/1.05  --prep_sem_filter                       exhaustive
% 2.20/1.05  --prep_sem_filter_out                   false
% 2.20/1.05  --pred_elim                             true
% 2.20/1.05  --res_sim_input                         true
% 2.20/1.05  --eq_ax_congr_red                       true
% 2.20/1.05  --pure_diseq_elim                       true
% 2.20/1.05  --brand_transform                       false
% 2.20/1.05  --non_eq_to_eq                          false
% 2.20/1.05  --prep_def_merge                        true
% 2.20/1.05  --prep_def_merge_prop_impl              false
% 2.20/1.05  --prep_def_merge_mbd                    true
% 2.20/1.05  --prep_def_merge_tr_red                 false
% 2.20/1.05  --prep_def_merge_tr_cl                  false
% 2.20/1.05  --smt_preprocessing                     true
% 2.20/1.05  --smt_ac_axioms                         fast
% 2.20/1.05  --preprocessed_out                      false
% 2.20/1.05  --preprocessed_stats                    false
% 2.20/1.05  
% 2.20/1.05  ------ Abstraction refinement Options
% 2.20/1.05  
% 2.20/1.05  --abstr_ref                             []
% 2.20/1.05  --abstr_ref_prep                        false
% 2.20/1.05  --abstr_ref_until_sat                   false
% 2.20/1.05  --abstr_ref_sig_restrict                funpre
% 2.20/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.20/1.05  --abstr_ref_under                       []
% 2.20/1.05  
% 2.20/1.05  ------ SAT Options
% 2.20/1.05  
% 2.20/1.05  --sat_mode                              false
% 2.20/1.05  --sat_fm_restart_options                ""
% 2.20/1.05  --sat_gr_def                            false
% 2.20/1.05  --sat_epr_types                         true
% 2.20/1.05  --sat_non_cyclic_types                  false
% 2.20/1.05  --sat_finite_models                     false
% 2.20/1.05  --sat_fm_lemmas                         false
% 2.20/1.05  --sat_fm_prep                           false
% 2.20/1.05  --sat_fm_uc_incr                        true
% 2.20/1.05  --sat_out_model                         small
% 2.20/1.05  --sat_out_clauses                       false
% 2.20/1.05  
% 2.20/1.05  ------ QBF Options
% 2.20/1.05  
% 2.20/1.05  --qbf_mode                              false
% 2.20/1.05  --qbf_elim_univ                         false
% 2.20/1.05  --qbf_dom_inst                          none
% 2.20/1.05  --qbf_dom_pre_inst                      false
% 2.20/1.05  --qbf_sk_in                             false
% 2.20/1.05  --qbf_pred_elim                         true
% 2.20/1.05  --qbf_split                             512
% 2.20/1.05  
% 2.20/1.05  ------ BMC1 Options
% 2.20/1.05  
% 2.20/1.05  --bmc1_incremental                      false
% 2.20/1.05  --bmc1_axioms                           reachable_all
% 2.20/1.05  --bmc1_min_bound                        0
% 2.20/1.05  --bmc1_max_bound                        -1
% 2.20/1.05  --bmc1_max_bound_default                -1
% 2.20/1.05  --bmc1_symbol_reachability              true
% 2.20/1.05  --bmc1_property_lemmas                  false
% 2.20/1.05  --bmc1_k_induction                      false
% 2.20/1.05  --bmc1_non_equiv_states                 false
% 2.20/1.05  --bmc1_deadlock                         false
% 2.20/1.05  --bmc1_ucm                              false
% 2.20/1.05  --bmc1_add_unsat_core                   none
% 2.20/1.05  --bmc1_unsat_core_children              false
% 2.20/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.20/1.05  --bmc1_out_stat                         full
% 2.20/1.05  --bmc1_ground_init                      false
% 2.20/1.05  --bmc1_pre_inst_next_state              false
% 2.20/1.05  --bmc1_pre_inst_state                   false
% 2.20/1.05  --bmc1_pre_inst_reach_state             false
% 2.20/1.05  --bmc1_out_unsat_core                   false
% 2.20/1.05  --bmc1_aig_witness_out                  false
% 2.20/1.05  --bmc1_verbose                          false
% 2.20/1.05  --bmc1_dump_clauses_tptp                false
% 2.20/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.20/1.05  --bmc1_dump_file                        -
% 2.20/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.20/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.20/1.05  --bmc1_ucm_extend_mode                  1
% 2.20/1.05  --bmc1_ucm_init_mode                    2
% 2.20/1.05  --bmc1_ucm_cone_mode                    none
% 2.20/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.20/1.05  --bmc1_ucm_relax_model                  4
% 2.20/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.20/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.20/1.05  --bmc1_ucm_layered_model                none
% 2.20/1.05  --bmc1_ucm_max_lemma_size               10
% 2.20/1.05  
% 2.20/1.05  ------ AIG Options
% 2.20/1.05  
% 2.20/1.05  --aig_mode                              false
% 2.20/1.05  
% 2.20/1.05  ------ Instantiation Options
% 2.20/1.05  
% 2.20/1.05  --instantiation_flag                    true
% 2.20/1.05  --inst_sos_flag                         false
% 2.20/1.05  --inst_sos_phase                        true
% 2.20/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.20/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.20/1.05  --inst_lit_sel_side                     none
% 2.20/1.05  --inst_solver_per_active                1400
% 2.20/1.05  --inst_solver_calls_frac                1.
% 2.20/1.05  --inst_passive_queue_type               priority_queues
% 2.20/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.20/1.05  --inst_passive_queues_freq              [25;2]
% 2.20/1.05  --inst_dismatching                      true
% 2.20/1.05  --inst_eager_unprocessed_to_passive     true
% 2.20/1.05  --inst_prop_sim_given                   true
% 2.20/1.05  --inst_prop_sim_new                     false
% 2.20/1.05  --inst_subs_new                         false
% 2.20/1.05  --inst_eq_res_simp                      false
% 2.20/1.05  --inst_subs_given                       false
% 2.20/1.05  --inst_orphan_elimination               true
% 2.20/1.05  --inst_learning_loop_flag               true
% 2.20/1.05  --inst_learning_start                   3000
% 2.20/1.05  --inst_learning_factor                  2
% 2.20/1.05  --inst_start_prop_sim_after_learn       3
% 2.20/1.05  --inst_sel_renew                        solver
% 2.20/1.05  --inst_lit_activity_flag                true
% 2.20/1.05  --inst_restr_to_given                   false
% 2.20/1.05  --inst_activity_threshold               500
% 2.20/1.05  --inst_out_proof                        true
% 2.20/1.05  
% 2.20/1.05  ------ Resolution Options
% 2.20/1.05  
% 2.20/1.05  --resolution_flag                       false
% 2.20/1.05  --res_lit_sel                           adaptive
% 2.20/1.05  --res_lit_sel_side                      none
% 2.20/1.05  --res_ordering                          kbo
% 2.20/1.05  --res_to_prop_solver                    active
% 2.20/1.05  --res_prop_simpl_new                    false
% 2.20/1.05  --res_prop_simpl_given                  true
% 2.20/1.05  --res_passive_queue_type                priority_queues
% 2.20/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.20/1.05  --res_passive_queues_freq               [15;5]
% 2.20/1.05  --res_forward_subs                      full
% 2.20/1.05  --res_backward_subs                     full
% 2.20/1.05  --res_forward_subs_resolution           true
% 2.20/1.05  --res_backward_subs_resolution          true
% 2.20/1.05  --res_orphan_elimination                true
% 2.20/1.05  --res_time_limit                        2.
% 2.20/1.05  --res_out_proof                         true
% 2.20/1.05  
% 2.20/1.05  ------ Superposition Options
% 2.20/1.05  
% 2.20/1.05  --superposition_flag                    true
% 2.20/1.05  --sup_passive_queue_type                priority_queues
% 2.20/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.20/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.20/1.05  --demod_completeness_check              fast
% 2.20/1.05  --demod_use_ground                      true
% 2.20/1.05  --sup_to_prop_solver                    passive
% 2.20/1.05  --sup_prop_simpl_new                    true
% 2.20/1.05  --sup_prop_simpl_given                  true
% 2.20/1.05  --sup_fun_splitting                     false
% 2.20/1.05  --sup_smt_interval                      50000
% 2.20/1.05  
% 2.20/1.05  ------ Superposition Simplification Setup
% 2.20/1.05  
% 2.20/1.05  --sup_indices_passive                   []
% 2.20/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.20/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.20/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.05  --sup_full_bw                           [BwDemod]
% 2.20/1.05  --sup_immed_triv                        [TrivRules]
% 2.20/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.20/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.05  --sup_immed_bw_main                     []
% 2.20/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.20/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.20/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.20/1.05  
% 2.20/1.05  ------ Combination Options
% 2.20/1.05  
% 2.20/1.05  --comb_res_mult                         3
% 2.20/1.05  --comb_sup_mult                         2
% 2.20/1.05  --comb_inst_mult                        10
% 2.20/1.05  
% 2.20/1.05  ------ Debug Options
% 2.20/1.05  
% 2.20/1.05  --dbg_backtrace                         false
% 2.20/1.05  --dbg_dump_prop_clauses                 false
% 2.20/1.05  --dbg_dump_prop_clauses_file            -
% 2.20/1.05  --dbg_out_stat                          false
% 2.20/1.05  
% 2.20/1.05  
% 2.20/1.05  
% 2.20/1.05  
% 2.20/1.05  ------ Proving...
% 2.20/1.05  
% 2.20/1.05  
% 2.20/1.05  % SZS status Theorem for theBenchmark.p
% 2.20/1.05  
% 2.20/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 2.20/1.05  
% 2.20/1.05  fof(f6,axiom,(
% 2.20/1.05    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.20/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.05  
% 2.20/1.05  fof(f21,plain,(
% 2.20/1.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.20/1.05    inference(cnf_transformation,[],[f6])).
% 2.20/1.05  
% 2.20/1.05  fof(f9,axiom,(
% 2.20/1.05    ! [X0,X1] : (X0 != X1 => k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0))),
% 2.20/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.05  
% 2.20/1.05  fof(f12,plain,(
% 2.20/1.05    ! [X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1)),
% 2.20/1.05    inference(ennf_transformation,[],[f9])).
% 2.20/1.05  
% 2.20/1.05  fof(f24,plain,(
% 2.20/1.05    ( ! [X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) )),
% 2.20/1.05    inference(cnf_transformation,[],[f12])).
% 2.20/1.05  
% 2.20/1.05  fof(f7,axiom,(
% 2.20/1.05    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.20/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.05  
% 2.20/1.05  fof(f22,plain,(
% 2.20/1.05    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.20/1.05    inference(cnf_transformation,[],[f7])).
% 2.20/1.05  
% 2.20/1.05  fof(f32,plain,(
% 2.20/1.05    ( ! [X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X1,X1)) = k2_tarski(X0,X0) | X0 = X1) )),
% 2.20/1.05    inference(definition_unfolding,[],[f24,f22,f22])).
% 2.20/1.05  
% 2.20/1.05  fof(f1,axiom,(
% 2.20/1.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.20/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.05  
% 2.20/1.05  fof(f16,plain,(
% 2.20/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.20/1.05    inference(cnf_transformation,[],[f1])).
% 2.20/1.05  
% 2.20/1.05  fof(f4,axiom,(
% 2.20/1.05    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.20/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.05  
% 2.20/1.05  fof(f19,plain,(
% 2.20/1.05    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.20/1.05    inference(cnf_transformation,[],[f4])).
% 2.20/1.05  
% 2.20/1.05  fof(f29,plain,(
% 2.20/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.20/1.05    inference(definition_unfolding,[],[f16,f19,f19])).
% 2.20/1.05  
% 2.20/1.05  fof(f3,axiom,(
% 2.20/1.05    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.20/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.05  
% 2.20/1.05  fof(f18,plain,(
% 2.20/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.20/1.05    inference(cnf_transformation,[],[f3])).
% 2.20/1.05  
% 2.20/1.05  fof(f5,axiom,(
% 2.20/1.05    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)),
% 2.20/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.05  
% 2.20/1.05  fof(f20,plain,(
% 2.20/1.05    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 2.20/1.05    inference(cnf_transformation,[],[f5])).
% 2.20/1.05  
% 2.20/1.05  fof(f27,plain,(
% 2.20/1.05    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k2_xboole_0(X0,X1)) )),
% 2.20/1.05    inference(definition_unfolding,[],[f20,f19])).
% 2.20/1.05  
% 2.20/1.05  fof(f30,plain,(
% 2.20/1.05    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0) )),
% 2.20/1.05    inference(definition_unfolding,[],[f18,f27,f19])).
% 2.20/1.05  
% 2.20/1.05  fof(f2,axiom,(
% 2.20/1.05    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.20/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.05  
% 2.20/1.05  fof(f17,plain,(
% 2.20/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.20/1.05    inference(cnf_transformation,[],[f2])).
% 2.20/1.05  
% 2.20/1.05  fof(f28,plain,(
% 2.20/1.05    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.20/1.05    inference(definition_unfolding,[],[f17,f19])).
% 2.20/1.05  
% 2.20/1.05  fof(f8,axiom,(
% 2.20/1.05    ! [X0,X1] : k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)),
% 2.20/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.05  
% 2.20/1.05  fof(f23,plain,(
% 2.20/1.05    ( ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) = k1_tarski(X0)) )),
% 2.20/1.05    inference(cnf_transformation,[],[f8])).
% 2.20/1.05  
% 2.20/1.05  fof(f31,plain,(
% 2.20/1.05    ( ! [X0,X1] : (k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) = k2_tarski(X0,X0)) )),
% 2.20/1.05    inference(definition_unfolding,[],[f23,f19,f22,f22])).
% 2.20/1.05  
% 2.20/1.05  fof(f10,conjecture,(
% 2.20/1.05    ! [X0,X1] : (X0 != X1 => k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1))),
% 2.20/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.20/1.05  
% 2.20/1.05  fof(f11,negated_conjecture,(
% 2.20/1.05    ~! [X0,X1] : (X0 != X1 => k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1))),
% 2.20/1.05    inference(negated_conjecture,[],[f10])).
% 2.20/1.05  
% 2.20/1.05  fof(f13,plain,(
% 2.20/1.05    ? [X0,X1] : (k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k2_tarski(X0,X1) & X0 != X1)),
% 2.20/1.05    inference(ennf_transformation,[],[f11])).
% 2.20/1.05  
% 2.20/1.05  fof(f14,plain,(
% 2.20/1.05    ? [X0,X1] : (k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k2_tarski(X0,X1) & X0 != X1) => (k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_tarski(sK0,sK1) & sK0 != sK1)),
% 2.20/1.05    introduced(choice_axiom,[])).
% 2.20/1.05  
% 2.20/1.05  fof(f15,plain,(
% 2.20/1.05    k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_tarski(sK0,sK1) & sK0 != sK1),
% 2.20/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 2.20/1.05  
% 2.20/1.05  fof(f26,plain,(
% 2.20/1.05    k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) != k2_tarski(sK0,sK1)),
% 2.20/1.05    inference(cnf_transformation,[],[f15])).
% 2.20/1.05  
% 2.20/1.05  fof(f33,plain,(
% 2.20/1.05    k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) != k2_tarski(sK0,sK1)),
% 2.20/1.05    inference(definition_unfolding,[],[f26,f22,f22])).
% 2.20/1.05  
% 2.20/1.05  fof(f25,plain,(
% 2.20/1.05    sK0 != sK1),
% 2.20/1.05    inference(cnf_transformation,[],[f15])).
% 2.20/1.05  
% 2.20/1.05  cnf(c_3,plain,
% 2.20/1.05      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 2.20/1.05      inference(cnf_transformation,[],[f21]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_5,plain,
% 2.20/1.05      ( X0 = X1
% 2.20/1.05      | k4_xboole_0(k2_tarski(X1,X0),k2_tarski(X0,X0)) = k2_tarski(X1,X1) ),
% 2.20/1.05      inference(cnf_transformation,[],[f32]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_300,plain,
% 2.20/1.05      ( X0 = X1
% 2.20/1.05      | k4_xboole_0(k2_tarski(X1,X0),k2_tarski(X1,X1)) = k2_tarski(X0,X0) ),
% 2.20/1.05      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_1,plain,
% 2.20/1.05      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 2.20/1.05      inference(cnf_transformation,[],[f29]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_2,plain,
% 2.20/1.05      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
% 2.20/1.05      inference(cnf_transformation,[],[f30]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_0,plain,
% 2.20/1.05      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 2.20/1.05      inference(cnf_transformation,[],[f28]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_43,plain,
% 2.20/1.05      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))))) = X0 ),
% 2.20/1.05      inference(light_normalisation,[status(thm)],[c_2,c_0]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_197,plain,
% 2.20/1.05      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) = X0 ),
% 2.20/1.05      inference(superposition,[status(thm)],[c_1,c_43]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_1291,plain,
% 2.20/1.05      ( X0 = X1
% 2.20/1.05      | k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)))))) = k2_tarski(X0,X1) ),
% 2.20/1.05      inference(superposition,[status(thm)],[c_300,c_197]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_4,plain,
% 2.20/1.05      ( k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) = k2_tarski(X0,X0) ),
% 2.20/1.05      inference(cnf_transformation,[],[f31]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_176,plain,
% 2.20/1.05      ( k4_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))) = k2_tarski(X0,X0) ),
% 2.20/1.05      inference(superposition,[status(thm)],[c_4,c_1]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_1465,plain,
% 2.20/1.05      ( X0 = X1
% 2.20/1.05      | k5_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) = k2_tarski(X1,X0) ),
% 2.20/1.05      inference(light_normalisation,[status(thm)],[c_1291,c_4,c_176]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_6,negated_conjecture,
% 2.20/1.05      ( k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK1)) != k2_tarski(sK0,sK1) ),
% 2.20/1.05      inference(cnf_transformation,[],[f33]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_2754,plain,
% 2.20/1.05      ( k2_tarski(sK1,sK0) != k2_tarski(sK0,sK1) | sK1 = sK0 ),
% 2.20/1.05      inference(superposition,[status(thm)],[c_1465,c_6]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_1686,plain,
% 2.20/1.05      ( k2_tarski(sK1,sK0) = k2_tarski(sK0,sK1) ),
% 2.20/1.05      inference(instantiation,[status(thm)],[c_3]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_20,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_49,plain,
% 2.20/1.05      ( sK1 != X0 | sK0 != X0 | sK0 = sK1 ),
% 2.20/1.05      inference(instantiation,[status(thm)],[c_20]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_50,plain,
% 2.20/1.05      ( sK1 != sK0 | sK0 = sK1 | sK0 != sK0 ),
% 2.20/1.05      inference(instantiation,[status(thm)],[c_49]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_19,plain,( X0 = X0 ),theory(equality) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_26,plain,
% 2.20/1.05      ( sK0 = sK0 ),
% 2.20/1.05      inference(instantiation,[status(thm)],[c_19]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(c_7,negated_conjecture,
% 2.20/1.05      ( sK0 != sK1 ),
% 2.20/1.05      inference(cnf_transformation,[],[f25]) ).
% 2.20/1.05  
% 2.20/1.05  cnf(contradiction,plain,
% 2.20/1.05      ( $false ),
% 2.20/1.05      inference(minisat,[status(thm)],[c_2754,c_1686,c_50,c_26,c_7]) ).
% 2.20/1.05  
% 2.20/1.05  
% 2.20/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 2.20/1.05  
% 2.20/1.05  ------                               Statistics
% 2.20/1.05  
% 2.20/1.05  ------ General
% 2.20/1.05  
% 2.20/1.05  abstr_ref_over_cycles:                  0
% 2.20/1.05  abstr_ref_under_cycles:                 0
% 2.20/1.05  gc_basic_clause_elim:                   0
% 2.20/1.05  forced_gc_time:                         0
% 2.20/1.05  parsing_time:                           0.008
% 2.20/1.05  unif_index_cands_time:                  0.
% 2.20/1.05  unif_index_add_time:                    0.
% 2.20/1.05  orderings_time:                         0.
% 2.20/1.05  out_proof_time:                         0.022
% 2.20/1.05  total_time:                             0.147
% 2.20/1.05  num_of_symbols:                         36
% 2.20/1.05  num_of_terms:                           2622
% 2.20/1.05  
% 2.20/1.05  ------ Preprocessing
% 2.20/1.05  
% 2.20/1.05  num_of_splits:                          0
% 2.20/1.05  num_of_split_atoms:                     0
% 2.20/1.05  num_of_reused_defs:                     0
% 2.20/1.05  num_eq_ax_congr_red:                    0
% 2.20/1.05  num_of_sem_filtered_clauses:            0
% 2.20/1.05  num_of_subtypes:                        0
% 2.20/1.05  monotx_restored_types:                  0
% 2.20/1.05  sat_num_of_epr_types:                   0
% 2.20/1.05  sat_num_of_non_cyclic_types:            0
% 2.20/1.05  sat_guarded_non_collapsed_types:        0
% 2.20/1.05  num_pure_diseq_elim:                    0
% 2.20/1.05  simp_replaced_by:                       0
% 2.20/1.05  res_preprocessed:                       21
% 2.20/1.05  prep_upred:                             0
% 2.20/1.05  prep_unflattend:                        0
% 2.20/1.05  smt_new_axioms:                         0
% 2.20/1.05  pred_elim_cands:                        0
% 2.20/1.05  pred_elim:                              0
% 2.20/1.05  pred_elim_cl:                           0
% 2.20/1.05  pred_elim_cycles:                       0
% 2.20/1.05  merged_defs:                            0
% 2.20/1.05  merged_defs_ncl:                        0
% 2.20/1.05  bin_hyper_res:                          0
% 2.20/1.05  prep_cycles:                            2
% 2.20/1.05  pred_elim_time:                         0.
% 2.20/1.05  splitting_time:                         0.
% 2.20/1.05  sem_filter_time:                        0.
% 2.20/1.05  monotx_time:                            0.
% 2.20/1.05  subtype_inf_time:                       0.
% 2.20/1.05  
% 2.20/1.05  ------ Problem properties
% 2.20/1.05  
% 2.20/1.05  clauses:                                8
% 2.20/1.05  conjectures:                            2
% 2.20/1.05  epr:                                    1
% 2.20/1.05  horn:                                   7
% 2.20/1.05  ground:                                 2
% 2.20/1.05  unary:                                  7
% 2.20/1.05  binary:                                 1
% 2.20/1.05  lits:                                   9
% 2.20/1.05  lits_eq:                                9
% 2.20/1.05  fd_pure:                                0
% 2.20/1.05  fd_pseudo:                              0
% 2.20/1.05  fd_cond:                                0
% 2.20/1.05  fd_pseudo_cond:                         1
% 2.20/1.05  ac_symbols:                             0
% 2.20/1.05  
% 2.20/1.05  ------ Propositional Solver
% 2.20/1.05  
% 2.20/1.05  prop_solver_calls:                      21
% 2.20/1.05  prop_fast_solver_calls:                 105
% 2.20/1.05  smt_solver_calls:                       0
% 2.20/1.05  smt_fast_solver_calls:                  0
% 2.20/1.05  prop_num_of_clauses:                    634
% 2.20/1.05  prop_preprocess_simplified:             1235
% 2.20/1.05  prop_fo_subsumed:                       0
% 2.20/1.05  prop_solver_time:                       0.
% 2.20/1.05  smt_solver_time:                        0.
% 2.20/1.05  smt_fast_solver_time:                   0.
% 2.20/1.05  prop_fast_solver_time:                  0.
% 2.20/1.05  prop_unsat_core_time:                   0.
% 2.20/1.05  
% 2.20/1.05  ------ QBF
% 2.20/1.05  
% 2.20/1.05  qbf_q_res:                              0
% 2.20/1.05  qbf_num_tautologies:                    0
% 2.20/1.05  qbf_prep_cycles:                        0
% 2.20/1.05  
% 2.20/1.05  ------ BMC1
% 2.20/1.05  
% 2.20/1.05  bmc1_current_bound:                     -1
% 2.20/1.05  bmc1_last_solved_bound:                 -1
% 2.20/1.05  bmc1_unsat_core_size:                   -1
% 2.20/1.05  bmc1_unsat_core_parents_size:           -1
% 2.20/1.05  bmc1_merge_next_fun:                    0
% 2.20/1.05  bmc1_unsat_core_clauses_time:           0.
% 2.20/1.05  
% 2.20/1.05  ------ Instantiation
% 2.20/1.05  
% 2.20/1.05  inst_num_of_clauses:                    262
% 2.20/1.05  inst_num_in_passive:                    108
% 2.20/1.05  inst_num_in_active:                     134
% 2.20/1.05  inst_num_in_unprocessed:                20
% 2.20/1.05  inst_num_of_loops:                      180
% 2.20/1.05  inst_num_of_learning_restarts:          0
% 2.20/1.05  inst_num_moves_active_passive:          42
% 2.20/1.05  inst_lit_activity:                      0
% 2.20/1.05  inst_lit_activity_moves:                0
% 2.20/1.05  inst_num_tautologies:                   0
% 2.20/1.05  inst_num_prop_implied:                  0
% 2.20/1.05  inst_num_existing_simplified:           0
% 2.20/1.05  inst_num_eq_res_simplified:             0
% 2.20/1.05  inst_num_child_elim:                    0
% 2.20/1.05  inst_num_of_dismatching_blockings:      105
% 2.20/1.05  inst_num_of_non_proper_insts:           284
% 2.20/1.05  inst_num_of_duplicates:                 0
% 2.20/1.05  inst_inst_num_from_inst_to_res:         0
% 2.20/1.05  inst_dismatching_checking_time:         0.
% 2.20/1.05  
% 2.20/1.05  ------ Resolution
% 2.20/1.05  
% 2.20/1.05  res_num_of_clauses:                     0
% 2.20/1.05  res_num_in_passive:                     0
% 2.20/1.05  res_num_in_active:                      0
% 2.20/1.05  res_num_of_loops:                       23
% 2.20/1.05  res_forward_subset_subsumed:            92
% 2.20/1.05  res_backward_subset_subsumed:           0
% 2.20/1.05  res_forward_subsumed:                   0
% 2.20/1.05  res_backward_subsumed:                  0
% 2.20/1.05  res_forward_subsumption_resolution:     0
% 2.20/1.05  res_backward_subsumption_resolution:    0
% 2.20/1.05  res_clause_to_clause_subsumption:       664
% 2.20/1.05  res_orphan_elimination:                 0
% 2.20/1.05  res_tautology_del:                      20
% 2.20/1.05  res_num_eq_res_simplified:              0
% 2.20/1.05  res_num_sel_changes:                    0
% 2.20/1.05  res_moves_from_active_to_pass:          0
% 2.20/1.05  
% 2.20/1.05  ------ Superposition
% 2.20/1.05  
% 2.20/1.05  sup_time_total:                         0.
% 2.20/1.05  sup_time_generating:                    0.
% 2.20/1.05  sup_time_sim_full:                      0.
% 2.20/1.05  sup_time_sim_immed:                     0.
% 2.20/1.05  
% 2.20/1.05  sup_num_of_clauses:                     185
% 2.20/1.05  sup_num_in_active:                      35
% 2.20/1.05  sup_num_in_passive:                     150
% 2.20/1.05  sup_num_of_loops:                       35
% 2.20/1.05  sup_fw_superposition:                   398
% 2.20/1.05  sup_bw_superposition:                   483
% 2.20/1.05  sup_immediate_simplified:               85
% 2.20/1.05  sup_given_eliminated:                   1
% 2.20/1.05  comparisons_done:                       0
% 2.20/1.05  comparisons_avoided:                    6
% 2.20/1.05  
% 2.20/1.05  ------ Simplifications
% 2.20/1.05  
% 2.20/1.05  
% 2.20/1.05  sim_fw_subset_subsumed:                 1
% 2.20/1.05  sim_bw_subset_subsumed:                 0
% 2.20/1.05  sim_fw_subsumed:                        6
% 2.20/1.05  sim_bw_subsumed:                        2
% 2.20/1.05  sim_fw_subsumption_res:                 0
% 2.20/1.05  sim_bw_subsumption_res:                 0
% 2.20/1.05  sim_tautology_del:                      0
% 2.20/1.05  sim_eq_tautology_del:                   100
% 2.20/1.05  sim_eq_res_simp:                        0
% 2.20/1.05  sim_fw_demodulated:                     52
% 2.20/1.05  sim_bw_demodulated:                     0
% 2.20/1.05  sim_light_normalised:                   35
% 2.20/1.05  sim_joinable_taut:                      0
% 2.20/1.05  sim_joinable_simp:                      0
% 2.20/1.05  sim_ac_normalised:                      0
% 2.20/1.05  sim_smt_subsumption:                    0
% 2.20/1.05  
%------------------------------------------------------------------------------
