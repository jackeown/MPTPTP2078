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
% DateTime   : Thu Dec  3 11:24:31 EST 2020

% Result     : Theorem 26.47s
% Output     : CNFRefutation 26.47s
% Verified   : 
% Statistics : Number of formulae       :   51 (  91 expanded)
%              Number of clauses        :   27 (  38 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :   14
%              Number of atoms          :   71 ( 126 expanded)
%              Number of equality atoms :   44 (  77 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f14,f20])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X1,X2))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).

fof(f22,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f23,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_48,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_8,negated_conjecture,
    ( r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_96,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_48,c_8])).

cnf(c_97,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_96])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_291,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_97,c_5])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_306,plain,
    ( k4_xboole_0(sK0,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_291,c_3])).

cnf(c_6,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_85,plain,
    ( X0 != X1
    | k4_xboole_0(X2,X0) != X3
    | k4_xboole_0(X3,k4_xboole_0(X3,X1)) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_48,c_6])).

cnf(c_86,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_85])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_623,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X1)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_86,c_4])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_253,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_4,c_2])).

cnf(c_624,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_623,c_253])).

cnf(c_625,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_624,c_2])).

cnf(c_1140,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_625,c_253])).

cnf(c_7,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_101,plain,
    ( k4_xboole_0(X0,X1) != sK0
    | k4_xboole_0(sK1,sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_7])).

cnf(c_102,plain,
    ( k4_xboole_0(X0,k4_xboole_0(sK1,sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_101])).

cnf(c_255,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(sK1,sK2))) != sK0 ),
    inference(superposition,[status(thm)],[c_4,c_102])).

cnf(c_41240,plain,
    ( k4_xboole_0(X0,k2_xboole_0(sK1,k1_xboole_0)) != sK0 ),
    inference(superposition,[status(thm)],[c_1140,c_255])).

cnf(c_254,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_4,c_3])).

cnf(c_41482,plain,
    ( k4_xboole_0(X0,sK1) != sK0 ),
    inference(demodulation,[status(thm)],[c_41240,c_254])).

cnf(c_42346,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_306,c_41482])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:51:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 26.47/4.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.47/4.01  
% 26.47/4.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 26.47/4.01  
% 26.47/4.01  ------  iProver source info
% 26.47/4.01  
% 26.47/4.01  git: date: 2020-06-30 10:37:57 +0100
% 26.47/4.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 26.47/4.01  git: non_committed_changes: false
% 26.47/4.01  git: last_make_outside_of_git: false
% 26.47/4.01  
% 26.47/4.01  ------ 
% 26.47/4.01  
% 26.47/4.01  ------ Input Options
% 26.47/4.01  
% 26.47/4.01  --out_options                           all
% 26.47/4.01  --tptp_safe_out                         true
% 26.47/4.01  --problem_path                          ""
% 26.47/4.01  --include_path                          ""
% 26.47/4.01  --clausifier                            res/vclausify_rel
% 26.47/4.01  --clausifier_options                    ""
% 26.47/4.01  --stdin                                 false
% 26.47/4.01  --stats_out                             all
% 26.47/4.01  
% 26.47/4.01  ------ General Options
% 26.47/4.01  
% 26.47/4.01  --fof                                   false
% 26.47/4.01  --time_out_real                         305.
% 26.47/4.01  --time_out_virtual                      -1.
% 26.47/4.01  --symbol_type_check                     false
% 26.47/4.01  --clausify_out                          false
% 26.47/4.01  --sig_cnt_out                           false
% 26.47/4.01  --trig_cnt_out                          false
% 26.47/4.01  --trig_cnt_out_tolerance                1.
% 26.47/4.01  --trig_cnt_out_sk_spl                   false
% 26.47/4.01  --abstr_cl_out                          false
% 26.47/4.01  
% 26.47/4.01  ------ Global Options
% 26.47/4.01  
% 26.47/4.01  --schedule                              default
% 26.47/4.01  --add_important_lit                     false
% 26.47/4.01  --prop_solver_per_cl                    1000
% 26.47/4.01  --min_unsat_core                        false
% 26.47/4.01  --soft_assumptions                      false
% 26.47/4.01  --soft_lemma_size                       3
% 26.47/4.01  --prop_impl_unit_size                   0
% 26.47/4.01  --prop_impl_unit                        []
% 26.47/4.01  --share_sel_clauses                     true
% 26.47/4.01  --reset_solvers                         false
% 26.47/4.01  --bc_imp_inh                            [conj_cone]
% 26.47/4.01  --conj_cone_tolerance                   3.
% 26.47/4.01  --extra_neg_conj                        none
% 26.47/4.01  --large_theory_mode                     true
% 26.47/4.01  --prolific_symb_bound                   200
% 26.47/4.01  --lt_threshold                          2000
% 26.47/4.01  --clause_weak_htbl                      true
% 26.47/4.01  --gc_record_bc_elim                     false
% 26.47/4.01  
% 26.47/4.01  ------ Preprocessing Options
% 26.47/4.01  
% 26.47/4.01  --preprocessing_flag                    true
% 26.47/4.01  --time_out_prep_mult                    0.1
% 26.47/4.01  --splitting_mode                        input
% 26.47/4.01  --splitting_grd                         true
% 26.47/4.01  --splitting_cvd                         false
% 26.47/4.01  --splitting_cvd_svl                     false
% 26.47/4.01  --splitting_nvd                         32
% 26.47/4.01  --sub_typing                            true
% 26.47/4.01  --prep_gs_sim                           true
% 26.47/4.01  --prep_unflatten                        true
% 26.47/4.01  --prep_res_sim                          true
% 26.47/4.01  --prep_upred                            true
% 26.47/4.01  --prep_sem_filter                       exhaustive
% 26.47/4.01  --prep_sem_filter_out                   false
% 26.47/4.01  --pred_elim                             true
% 26.47/4.01  --res_sim_input                         true
% 26.47/4.01  --eq_ax_congr_red                       true
% 26.47/4.01  --pure_diseq_elim                       true
% 26.47/4.01  --brand_transform                       false
% 26.47/4.01  --non_eq_to_eq                          false
% 26.47/4.01  --prep_def_merge                        true
% 26.47/4.01  --prep_def_merge_prop_impl              false
% 26.47/4.01  --prep_def_merge_mbd                    true
% 26.47/4.01  --prep_def_merge_tr_red                 false
% 26.47/4.01  --prep_def_merge_tr_cl                  false
% 26.47/4.01  --smt_preprocessing                     true
% 26.47/4.01  --smt_ac_axioms                         fast
% 26.47/4.01  --preprocessed_out                      false
% 26.47/4.01  --preprocessed_stats                    false
% 26.47/4.01  
% 26.47/4.01  ------ Abstraction refinement Options
% 26.47/4.01  
% 26.47/4.01  --abstr_ref                             []
% 26.47/4.01  --abstr_ref_prep                        false
% 26.47/4.01  --abstr_ref_until_sat                   false
% 26.47/4.01  --abstr_ref_sig_restrict                funpre
% 26.47/4.01  --abstr_ref_af_restrict_to_split_sk     false
% 26.47/4.01  --abstr_ref_under                       []
% 26.47/4.01  
% 26.47/4.01  ------ SAT Options
% 26.47/4.01  
% 26.47/4.01  --sat_mode                              false
% 26.47/4.01  --sat_fm_restart_options                ""
% 26.47/4.01  --sat_gr_def                            false
% 26.47/4.01  --sat_epr_types                         true
% 26.47/4.01  --sat_non_cyclic_types                  false
% 26.47/4.01  --sat_finite_models                     false
% 26.47/4.01  --sat_fm_lemmas                         false
% 26.47/4.01  --sat_fm_prep                           false
% 26.47/4.01  --sat_fm_uc_incr                        true
% 26.47/4.01  --sat_out_model                         small
% 26.47/4.01  --sat_out_clauses                       false
% 26.47/4.01  
% 26.47/4.01  ------ QBF Options
% 26.47/4.01  
% 26.47/4.01  --qbf_mode                              false
% 26.47/4.01  --qbf_elim_univ                         false
% 26.47/4.01  --qbf_dom_inst                          none
% 26.47/4.01  --qbf_dom_pre_inst                      false
% 26.47/4.01  --qbf_sk_in                             false
% 26.47/4.01  --qbf_pred_elim                         true
% 26.47/4.01  --qbf_split                             512
% 26.47/4.01  
% 26.47/4.01  ------ BMC1 Options
% 26.47/4.01  
% 26.47/4.01  --bmc1_incremental                      false
% 26.47/4.01  --bmc1_axioms                           reachable_all
% 26.47/4.01  --bmc1_min_bound                        0
% 26.47/4.01  --bmc1_max_bound                        -1
% 26.47/4.01  --bmc1_max_bound_default                -1
% 26.47/4.01  --bmc1_symbol_reachability              true
% 26.47/4.01  --bmc1_property_lemmas                  false
% 26.47/4.01  --bmc1_k_induction                      false
% 26.47/4.01  --bmc1_non_equiv_states                 false
% 26.47/4.01  --bmc1_deadlock                         false
% 26.47/4.01  --bmc1_ucm                              false
% 26.47/4.01  --bmc1_add_unsat_core                   none
% 26.47/4.01  --bmc1_unsat_core_children              false
% 26.47/4.01  --bmc1_unsat_core_extrapolate_axioms    false
% 26.47/4.01  --bmc1_out_stat                         full
% 26.47/4.01  --bmc1_ground_init                      false
% 26.47/4.01  --bmc1_pre_inst_next_state              false
% 26.47/4.01  --bmc1_pre_inst_state                   false
% 26.47/4.01  --bmc1_pre_inst_reach_state             false
% 26.47/4.01  --bmc1_out_unsat_core                   false
% 26.47/4.01  --bmc1_aig_witness_out                  false
% 26.47/4.01  --bmc1_verbose                          false
% 26.47/4.01  --bmc1_dump_clauses_tptp                false
% 26.47/4.01  --bmc1_dump_unsat_core_tptp             false
% 26.47/4.01  --bmc1_dump_file                        -
% 26.47/4.01  --bmc1_ucm_expand_uc_limit              128
% 26.47/4.01  --bmc1_ucm_n_expand_iterations          6
% 26.47/4.01  --bmc1_ucm_extend_mode                  1
% 26.47/4.01  --bmc1_ucm_init_mode                    2
% 26.47/4.01  --bmc1_ucm_cone_mode                    none
% 26.47/4.01  --bmc1_ucm_reduced_relation_type        0
% 26.47/4.01  --bmc1_ucm_relax_model                  4
% 26.47/4.01  --bmc1_ucm_full_tr_after_sat            true
% 26.47/4.01  --bmc1_ucm_expand_neg_assumptions       false
% 26.47/4.01  --bmc1_ucm_layered_model                none
% 26.47/4.01  --bmc1_ucm_max_lemma_size               10
% 26.47/4.01  
% 26.47/4.01  ------ AIG Options
% 26.47/4.01  
% 26.47/4.01  --aig_mode                              false
% 26.47/4.01  
% 26.47/4.01  ------ Instantiation Options
% 26.47/4.01  
% 26.47/4.01  --instantiation_flag                    true
% 26.47/4.01  --inst_sos_flag                         true
% 26.47/4.01  --inst_sos_phase                        true
% 26.47/4.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 26.47/4.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 26.47/4.01  --inst_lit_sel_side                     num_symb
% 26.47/4.01  --inst_solver_per_active                1400
% 26.47/4.01  --inst_solver_calls_frac                1.
% 26.47/4.01  --inst_passive_queue_type               priority_queues
% 26.47/4.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 26.47/4.01  --inst_passive_queues_freq              [25;2]
% 26.47/4.01  --inst_dismatching                      true
% 26.47/4.01  --inst_eager_unprocessed_to_passive     true
% 26.47/4.01  --inst_prop_sim_given                   true
% 26.47/4.01  --inst_prop_sim_new                     false
% 26.47/4.01  --inst_subs_new                         false
% 26.47/4.01  --inst_eq_res_simp                      false
% 26.47/4.01  --inst_subs_given                       false
% 26.47/4.01  --inst_orphan_elimination               true
% 26.47/4.01  --inst_learning_loop_flag               true
% 26.47/4.01  --inst_learning_start                   3000
% 26.47/4.01  --inst_learning_factor                  2
% 26.47/4.01  --inst_start_prop_sim_after_learn       3
% 26.47/4.01  --inst_sel_renew                        solver
% 26.47/4.01  --inst_lit_activity_flag                true
% 26.47/4.01  --inst_restr_to_given                   false
% 26.47/4.01  --inst_activity_threshold               500
% 26.47/4.01  --inst_out_proof                        true
% 26.47/4.01  
% 26.47/4.01  ------ Resolution Options
% 26.47/4.01  
% 26.47/4.01  --resolution_flag                       true
% 26.47/4.01  --res_lit_sel                           adaptive
% 26.47/4.01  --res_lit_sel_side                      none
% 26.47/4.01  --res_ordering                          kbo
% 26.47/4.01  --res_to_prop_solver                    active
% 26.47/4.01  --res_prop_simpl_new                    false
% 26.47/4.01  --res_prop_simpl_given                  true
% 26.47/4.01  --res_passive_queue_type                priority_queues
% 26.47/4.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 26.47/4.01  --res_passive_queues_freq               [15;5]
% 26.47/4.01  --res_forward_subs                      full
% 26.47/4.01  --res_backward_subs                     full
% 26.47/4.01  --res_forward_subs_resolution           true
% 26.47/4.01  --res_backward_subs_resolution          true
% 26.47/4.01  --res_orphan_elimination                true
% 26.47/4.01  --res_time_limit                        2.
% 26.47/4.01  --res_out_proof                         true
% 26.47/4.01  
% 26.47/4.01  ------ Superposition Options
% 26.47/4.01  
% 26.47/4.01  --superposition_flag                    true
% 26.47/4.01  --sup_passive_queue_type                priority_queues
% 26.47/4.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 26.47/4.01  --sup_passive_queues_freq               [8;1;4]
% 26.47/4.01  --demod_completeness_check              fast
% 26.47/4.01  --demod_use_ground                      true
% 26.47/4.01  --sup_to_prop_solver                    passive
% 26.47/4.01  --sup_prop_simpl_new                    true
% 26.47/4.01  --sup_prop_simpl_given                  true
% 26.47/4.01  --sup_fun_splitting                     true
% 26.47/4.01  --sup_smt_interval                      50000
% 26.47/4.01  
% 26.47/4.01  ------ Superposition Simplification Setup
% 26.47/4.01  
% 26.47/4.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 26.47/4.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 26.47/4.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 26.47/4.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 26.47/4.01  --sup_full_triv                         [TrivRules;PropSubs]
% 26.47/4.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 26.47/4.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 26.47/4.01  --sup_immed_triv                        [TrivRules]
% 26.47/4.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 26.47/4.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 26.47/4.01  --sup_immed_bw_main                     []
% 26.47/4.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 26.47/4.01  --sup_input_triv                        [Unflattening;TrivRules]
% 26.47/4.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 26.47/4.01  --sup_input_bw                          []
% 26.47/4.01  
% 26.47/4.01  ------ Combination Options
% 26.47/4.01  
% 26.47/4.01  --comb_res_mult                         3
% 26.47/4.01  --comb_sup_mult                         2
% 26.47/4.01  --comb_inst_mult                        10
% 26.47/4.01  
% 26.47/4.01  ------ Debug Options
% 26.47/4.01  
% 26.47/4.01  --dbg_backtrace                         false
% 26.47/4.01  --dbg_dump_prop_clauses                 false
% 26.47/4.01  --dbg_dump_prop_clauses_file            -
% 26.47/4.01  --dbg_out_stat                          false
% 26.47/4.01  ------ Parsing...
% 26.47/4.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 26.47/4.01  
% 26.47/4.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 26.47/4.01  
% 26.47/4.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 26.47/4.01  
% 26.47/4.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 26.47/4.01  ------ Proving...
% 26.47/4.01  ------ Problem Properties 
% 26.47/4.01  
% 26.47/4.01  
% 26.47/4.01  clauses                                 9
% 26.47/4.01  conjectures                             0
% 26.47/4.01  EPR                                     0
% 26.47/4.01  Horn                                    9
% 26.47/4.01  unary                                   8
% 26.47/4.01  binary                                  1
% 26.47/4.01  lits                                    10
% 26.47/4.01  lits eq                                 10
% 26.47/4.01  fd_pure                                 0
% 26.47/4.01  fd_pseudo                               0
% 26.47/4.01  fd_cond                                 0
% 26.47/4.01  fd_pseudo_cond                          0
% 26.47/4.01  AC symbols                              0
% 26.47/4.01  
% 26.47/4.01  ------ Schedule dynamic 5 is on 
% 26.47/4.01  
% 26.47/4.01  ------ no conjectures: strip conj schedule 
% 26.47/4.01  
% 26.47/4.01  ------ pure equality problem: resolution off 
% 26.47/4.01  
% 26.47/4.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 26.47/4.01  
% 26.47/4.01  
% 26.47/4.01  ------ 
% 26.47/4.01  Current options:
% 26.47/4.01  ------ 
% 26.47/4.01  
% 26.47/4.01  ------ Input Options
% 26.47/4.01  
% 26.47/4.01  --out_options                           all
% 26.47/4.01  --tptp_safe_out                         true
% 26.47/4.01  --problem_path                          ""
% 26.47/4.01  --include_path                          ""
% 26.47/4.01  --clausifier                            res/vclausify_rel
% 26.47/4.01  --clausifier_options                    ""
% 26.47/4.01  --stdin                                 false
% 26.47/4.01  --stats_out                             all
% 26.47/4.01  
% 26.47/4.01  ------ General Options
% 26.47/4.01  
% 26.47/4.01  --fof                                   false
% 26.47/4.01  --time_out_real                         305.
% 26.47/4.01  --time_out_virtual                      -1.
% 26.47/4.01  --symbol_type_check                     false
% 26.47/4.01  --clausify_out                          false
% 26.47/4.01  --sig_cnt_out                           false
% 26.47/4.01  --trig_cnt_out                          false
% 26.47/4.01  --trig_cnt_out_tolerance                1.
% 26.47/4.01  --trig_cnt_out_sk_spl                   false
% 26.47/4.01  --abstr_cl_out                          false
% 26.47/4.01  
% 26.47/4.01  ------ Global Options
% 26.47/4.01  
% 26.47/4.01  --schedule                              default
% 26.47/4.01  --add_important_lit                     false
% 26.47/4.01  --prop_solver_per_cl                    1000
% 26.47/4.01  --min_unsat_core                        false
% 26.47/4.01  --soft_assumptions                      false
% 26.47/4.01  --soft_lemma_size                       3
% 26.47/4.01  --prop_impl_unit_size                   0
% 26.47/4.01  --prop_impl_unit                        []
% 26.47/4.01  --share_sel_clauses                     true
% 26.47/4.01  --reset_solvers                         false
% 26.47/4.01  --bc_imp_inh                            [conj_cone]
% 26.47/4.01  --conj_cone_tolerance                   3.
% 26.47/4.01  --extra_neg_conj                        none
% 26.47/4.01  --large_theory_mode                     true
% 26.47/4.01  --prolific_symb_bound                   200
% 26.47/4.01  --lt_threshold                          2000
% 26.47/4.01  --clause_weak_htbl                      true
% 26.47/4.01  --gc_record_bc_elim                     false
% 26.47/4.01  
% 26.47/4.01  ------ Preprocessing Options
% 26.47/4.01  
% 26.47/4.01  --preprocessing_flag                    true
% 26.47/4.01  --time_out_prep_mult                    0.1
% 26.47/4.01  --splitting_mode                        input
% 26.47/4.01  --splitting_grd                         true
% 26.47/4.01  --splitting_cvd                         false
% 26.47/4.01  --splitting_cvd_svl                     false
% 26.47/4.01  --splitting_nvd                         32
% 26.47/4.01  --sub_typing                            true
% 26.47/4.01  --prep_gs_sim                           true
% 26.47/4.01  --prep_unflatten                        true
% 26.47/4.01  --prep_res_sim                          true
% 26.47/4.01  --prep_upred                            true
% 26.47/4.01  --prep_sem_filter                       exhaustive
% 26.47/4.01  --prep_sem_filter_out                   false
% 26.47/4.01  --pred_elim                             true
% 26.47/4.01  --res_sim_input                         true
% 26.47/4.01  --eq_ax_congr_red                       true
% 26.47/4.01  --pure_diseq_elim                       true
% 26.47/4.01  --brand_transform                       false
% 26.47/4.01  --non_eq_to_eq                          false
% 26.47/4.01  --prep_def_merge                        true
% 26.47/4.01  --prep_def_merge_prop_impl              false
% 26.47/4.01  --prep_def_merge_mbd                    true
% 26.47/4.01  --prep_def_merge_tr_red                 false
% 26.47/4.01  --prep_def_merge_tr_cl                  false
% 26.47/4.01  --smt_preprocessing                     true
% 26.47/4.01  --smt_ac_axioms                         fast
% 26.47/4.01  --preprocessed_out                      false
% 26.47/4.01  --preprocessed_stats                    false
% 26.47/4.01  
% 26.47/4.01  ------ Abstraction refinement Options
% 26.47/4.01  
% 26.47/4.01  --abstr_ref                             []
% 26.47/4.01  --abstr_ref_prep                        false
% 26.47/4.01  --abstr_ref_until_sat                   false
% 26.47/4.01  --abstr_ref_sig_restrict                funpre
% 26.47/4.01  --abstr_ref_af_restrict_to_split_sk     false
% 26.47/4.01  --abstr_ref_under                       []
% 26.47/4.01  
% 26.47/4.01  ------ SAT Options
% 26.47/4.01  
% 26.47/4.01  --sat_mode                              false
% 26.47/4.01  --sat_fm_restart_options                ""
% 26.47/4.01  --sat_gr_def                            false
% 26.47/4.01  --sat_epr_types                         true
% 26.47/4.01  --sat_non_cyclic_types                  false
% 26.47/4.01  --sat_finite_models                     false
% 26.47/4.01  --sat_fm_lemmas                         false
% 26.47/4.01  --sat_fm_prep                           false
% 26.47/4.01  --sat_fm_uc_incr                        true
% 26.47/4.01  --sat_out_model                         small
% 26.47/4.01  --sat_out_clauses                       false
% 26.47/4.01  
% 26.47/4.01  ------ QBF Options
% 26.47/4.01  
% 26.47/4.01  --qbf_mode                              false
% 26.47/4.01  --qbf_elim_univ                         false
% 26.47/4.01  --qbf_dom_inst                          none
% 26.47/4.01  --qbf_dom_pre_inst                      false
% 26.47/4.01  --qbf_sk_in                             false
% 26.47/4.01  --qbf_pred_elim                         true
% 26.47/4.01  --qbf_split                             512
% 26.47/4.01  
% 26.47/4.01  ------ BMC1 Options
% 26.47/4.01  
% 26.47/4.01  --bmc1_incremental                      false
% 26.47/4.01  --bmc1_axioms                           reachable_all
% 26.47/4.01  --bmc1_min_bound                        0
% 26.47/4.01  --bmc1_max_bound                        -1
% 26.47/4.01  --bmc1_max_bound_default                -1
% 26.47/4.01  --bmc1_symbol_reachability              true
% 26.47/4.01  --bmc1_property_lemmas                  false
% 26.47/4.01  --bmc1_k_induction                      false
% 26.47/4.01  --bmc1_non_equiv_states                 false
% 26.47/4.01  --bmc1_deadlock                         false
% 26.47/4.01  --bmc1_ucm                              false
% 26.47/4.01  --bmc1_add_unsat_core                   none
% 26.47/4.01  --bmc1_unsat_core_children              false
% 26.47/4.01  --bmc1_unsat_core_extrapolate_axioms    false
% 26.47/4.01  --bmc1_out_stat                         full
% 26.47/4.01  --bmc1_ground_init                      false
% 26.47/4.01  --bmc1_pre_inst_next_state              false
% 26.47/4.01  --bmc1_pre_inst_state                   false
% 26.47/4.01  --bmc1_pre_inst_reach_state             false
% 26.47/4.01  --bmc1_out_unsat_core                   false
% 26.47/4.01  --bmc1_aig_witness_out                  false
% 26.47/4.01  --bmc1_verbose                          false
% 26.47/4.01  --bmc1_dump_clauses_tptp                false
% 26.47/4.01  --bmc1_dump_unsat_core_tptp             false
% 26.47/4.01  --bmc1_dump_file                        -
% 26.47/4.01  --bmc1_ucm_expand_uc_limit              128
% 26.47/4.01  --bmc1_ucm_n_expand_iterations          6
% 26.47/4.01  --bmc1_ucm_extend_mode                  1
% 26.47/4.01  --bmc1_ucm_init_mode                    2
% 26.47/4.01  --bmc1_ucm_cone_mode                    none
% 26.47/4.01  --bmc1_ucm_reduced_relation_type        0
% 26.47/4.01  --bmc1_ucm_relax_model                  4
% 26.47/4.01  --bmc1_ucm_full_tr_after_sat            true
% 26.47/4.01  --bmc1_ucm_expand_neg_assumptions       false
% 26.47/4.01  --bmc1_ucm_layered_model                none
% 26.47/4.01  --bmc1_ucm_max_lemma_size               10
% 26.47/4.01  
% 26.47/4.01  ------ AIG Options
% 26.47/4.01  
% 26.47/4.01  --aig_mode                              false
% 26.47/4.01  
% 26.47/4.01  ------ Instantiation Options
% 26.47/4.01  
% 26.47/4.01  --instantiation_flag                    true
% 26.47/4.01  --inst_sos_flag                         true
% 26.47/4.01  --inst_sos_phase                        true
% 26.47/4.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 26.47/4.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 26.47/4.01  --inst_lit_sel_side                     none
% 26.47/4.01  --inst_solver_per_active                1400
% 26.47/4.01  --inst_solver_calls_frac                1.
% 26.47/4.01  --inst_passive_queue_type               priority_queues
% 26.47/4.01  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 26.47/4.01  --inst_passive_queues_freq              [25;2]
% 26.47/4.01  --inst_dismatching                      true
% 26.47/4.01  --inst_eager_unprocessed_to_passive     true
% 26.47/4.01  --inst_prop_sim_given                   true
% 26.47/4.01  --inst_prop_sim_new                     false
% 26.47/4.01  --inst_subs_new                         false
% 26.47/4.01  --inst_eq_res_simp                      false
% 26.47/4.01  --inst_subs_given                       false
% 26.47/4.01  --inst_orphan_elimination               true
% 26.47/4.01  --inst_learning_loop_flag               true
% 26.47/4.01  --inst_learning_start                   3000
% 26.47/4.01  --inst_learning_factor                  2
% 26.47/4.01  --inst_start_prop_sim_after_learn       3
% 26.47/4.01  --inst_sel_renew                        solver
% 26.47/4.01  --inst_lit_activity_flag                true
% 26.47/4.01  --inst_restr_to_given                   false
% 26.47/4.01  --inst_activity_threshold               500
% 26.47/4.01  --inst_out_proof                        true
% 26.47/4.01  
% 26.47/4.01  ------ Resolution Options
% 26.47/4.01  
% 26.47/4.01  --resolution_flag                       false
% 26.47/4.01  --res_lit_sel                           adaptive
% 26.47/4.01  --res_lit_sel_side                      none
% 26.47/4.01  --res_ordering                          kbo
% 26.47/4.01  --res_to_prop_solver                    active
% 26.47/4.01  --res_prop_simpl_new                    false
% 26.47/4.01  --res_prop_simpl_given                  true
% 26.47/4.01  --res_passive_queue_type                priority_queues
% 26.47/4.01  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 26.47/4.01  --res_passive_queues_freq               [15;5]
% 26.47/4.01  --res_forward_subs                      full
% 26.47/4.01  --res_backward_subs                     full
% 26.47/4.01  --res_forward_subs_resolution           true
% 26.47/4.01  --res_backward_subs_resolution          true
% 26.47/4.01  --res_orphan_elimination                true
% 26.47/4.01  --res_time_limit                        2.
% 26.47/4.01  --res_out_proof                         true
% 26.47/4.01  
% 26.47/4.01  ------ Superposition Options
% 26.47/4.01  
% 26.47/4.01  --superposition_flag                    true
% 26.47/4.01  --sup_passive_queue_type                priority_queues
% 26.47/4.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 26.47/4.01  --sup_passive_queues_freq               [8;1;4]
% 26.47/4.01  --demod_completeness_check              fast
% 26.47/4.01  --demod_use_ground                      true
% 26.47/4.01  --sup_to_prop_solver                    passive
% 26.47/4.01  --sup_prop_simpl_new                    true
% 26.47/4.01  --sup_prop_simpl_given                  true
% 26.47/4.01  --sup_fun_splitting                     true
% 26.47/4.01  --sup_smt_interval                      50000
% 26.47/4.01  
% 26.47/4.01  ------ Superposition Simplification Setup
% 26.47/4.01  
% 26.47/4.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 26.47/4.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 26.47/4.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 26.47/4.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 26.47/4.01  --sup_full_triv                         [TrivRules;PropSubs]
% 26.47/4.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 26.47/4.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 26.47/4.01  --sup_immed_triv                        [TrivRules]
% 26.47/4.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 26.47/4.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 26.47/4.01  --sup_immed_bw_main                     []
% 26.47/4.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 26.47/4.01  --sup_input_triv                        [Unflattening;TrivRules]
% 26.47/4.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 26.47/4.01  --sup_input_bw                          []
% 26.47/4.01  
% 26.47/4.01  ------ Combination Options
% 26.47/4.01  
% 26.47/4.01  --comb_res_mult                         3
% 26.47/4.01  --comb_sup_mult                         2
% 26.47/4.01  --comb_inst_mult                        10
% 26.47/4.01  
% 26.47/4.01  ------ Debug Options
% 26.47/4.01  
% 26.47/4.01  --dbg_backtrace                         false
% 26.47/4.01  --dbg_dump_prop_clauses                 false
% 26.47/4.01  --dbg_dump_prop_clauses_file            -
% 26.47/4.01  --dbg_out_stat                          false
% 26.47/4.01  
% 26.47/4.01  
% 26.47/4.01  
% 26.47/4.01  
% 26.47/4.01  ------ Proving...
% 26.47/4.01  
% 26.47/4.01  
% 26.47/4.01  % SZS status Theorem for theBenchmark.p
% 26.47/4.01  
% 26.47/4.01   Resolution empty clause
% 26.47/4.01  
% 26.47/4.01  % SZS output start CNFRefutation for theBenchmark.p
% 26.47/4.01  
% 26.47/4.01  fof(f1,axiom,(
% 26.47/4.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 26.47/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 26.47/4.01  
% 26.47/4.01  fof(f11,plain,(
% 26.47/4.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 26.47/4.01    inference(nnf_transformation,[],[f1])).
% 26.47/4.01  
% 26.47/4.01  fof(f14,plain,(
% 26.47/4.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 26.47/4.01    inference(cnf_transformation,[],[f11])).
% 26.47/4.01  
% 26.47/4.01  fof(f6,axiom,(
% 26.47/4.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 26.47/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 26.47/4.01  
% 26.47/4.01  fof(f20,plain,(
% 26.47/4.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 26.47/4.01    inference(cnf_transformation,[],[f6])).
% 26.47/4.01  
% 26.47/4.01  fof(f25,plain,(
% 26.47/4.01    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 26.47/4.01    inference(definition_unfolding,[],[f14,f20])).
% 26.47/4.01  
% 26.47/4.01  fof(f8,conjecture,(
% 26.47/4.01    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 26.47/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 26.47/4.01  
% 26.47/4.01  fof(f9,negated_conjecture,(
% 26.47/4.01    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 26.47/4.01    inference(negated_conjecture,[],[f8])).
% 26.47/4.01  
% 26.47/4.01  fof(f10,plain,(
% 26.47/4.01    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1))),
% 26.47/4.01    inference(ennf_transformation,[],[f9])).
% 26.47/4.01  
% 26.47/4.01  fof(f12,plain,(
% 26.47/4.01    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X1,X2)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1))),
% 26.47/4.01    introduced(choice_axiom,[])).
% 26.47/4.01  
% 26.47/4.01  fof(f13,plain,(
% 26.47/4.01    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) & r1_xboole_0(sK0,sK1)),
% 26.47/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).
% 26.47/4.01  
% 26.47/4.01  fof(f22,plain,(
% 26.47/4.01    r1_xboole_0(sK0,sK1)),
% 26.47/4.01    inference(cnf_transformation,[],[f13])).
% 26.47/4.01  
% 26.47/4.01  fof(f5,axiom,(
% 26.47/4.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 26.47/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 26.47/4.01  
% 26.47/4.01  fof(f19,plain,(
% 26.47/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 26.47/4.01    inference(cnf_transformation,[],[f5])).
% 26.47/4.01  
% 26.47/4.01  fof(f26,plain,(
% 26.47/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 26.47/4.01    inference(definition_unfolding,[],[f19,f20])).
% 26.47/4.01  
% 26.47/4.01  fof(f3,axiom,(
% 26.47/4.01    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 26.47/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 26.47/4.01  
% 26.47/4.01  fof(f17,plain,(
% 26.47/4.01    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 26.47/4.01    inference(cnf_transformation,[],[f3])).
% 26.47/4.01  
% 26.47/4.01  fof(f7,axiom,(
% 26.47/4.01    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 26.47/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 26.47/4.01  
% 26.47/4.01  fof(f21,plain,(
% 26.47/4.01    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 26.47/4.01    inference(cnf_transformation,[],[f7])).
% 26.47/4.01  
% 26.47/4.01  fof(f4,axiom,(
% 26.47/4.01    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 26.47/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 26.47/4.01  
% 26.47/4.01  fof(f18,plain,(
% 26.47/4.01    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 26.47/4.01    inference(cnf_transformation,[],[f4])).
% 26.47/4.01  
% 26.47/4.01  fof(f2,axiom,(
% 26.47/4.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 26.47/4.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 26.47/4.01  
% 26.47/4.01  fof(f16,plain,(
% 26.47/4.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 26.47/4.01    inference(cnf_transformation,[],[f2])).
% 26.47/4.01  
% 26.47/4.01  fof(f23,plain,(
% 26.47/4.01    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 26.47/4.01    inference(cnf_transformation,[],[f13])).
% 26.47/4.01  
% 26.47/4.01  cnf(c_1,plain,
% 26.47/4.01      ( ~ r1_xboole_0(X0,X1)
% 26.47/4.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 26.47/4.01      inference(cnf_transformation,[],[f25]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_48,plain,
% 26.47/4.01      ( ~ r1_xboole_0(X0,X1)
% 26.47/4.01      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 26.47/4.01      inference(prop_impl,[status(thm)],[c_1]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_8,negated_conjecture,
% 26.47/4.01      ( r1_xboole_0(sK0,sK1) ),
% 26.47/4.01      inference(cnf_transformation,[],[f22]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_96,plain,
% 26.47/4.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 26.47/4.01      | sK1 != X1
% 26.47/4.01      | sK0 != X0 ),
% 26.47/4.01      inference(resolution_lifted,[status(thm)],[c_48,c_8]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_97,plain,
% 26.47/4.01      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 26.47/4.01      inference(unflattening,[status(thm)],[c_96]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_5,plain,
% 26.47/4.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 26.47/4.01      inference(cnf_transformation,[],[f26]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_291,plain,
% 26.47/4.01      ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK1) ),
% 26.47/4.01      inference(superposition,[status(thm)],[c_97,c_5]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_3,plain,
% 26.47/4.01      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 26.47/4.01      inference(cnf_transformation,[],[f17]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_306,plain,
% 26.47/4.01      ( k4_xboole_0(sK0,sK1) = sK0 ),
% 26.47/4.01      inference(demodulation,[status(thm)],[c_291,c_3]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_6,plain,
% 26.47/4.01      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 26.47/4.01      inference(cnf_transformation,[],[f21]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_85,plain,
% 26.47/4.01      ( X0 != X1
% 26.47/4.01      | k4_xboole_0(X2,X0) != X3
% 26.47/4.01      | k4_xboole_0(X3,k4_xboole_0(X3,X1)) = k1_xboole_0 ),
% 26.47/4.01      inference(resolution_lifted,[status(thm)],[c_48,c_6]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_86,plain,
% 26.47/4.01      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 26.47/4.01      inference(unflattening,[status(thm)],[c_85]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_4,plain,
% 26.47/4.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 26.47/4.01      inference(cnf_transformation,[],[f18]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_623,plain,
% 26.47/4.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,k2_xboole_0(X1,X1)))) = k1_xboole_0 ),
% 26.47/4.01      inference(demodulation,[status(thm)],[c_86,c_4]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_2,plain,
% 26.47/4.01      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 26.47/4.01      inference(cnf_transformation,[],[f16]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_253,plain,
% 26.47/4.01      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 26.47/4.01      inference(superposition,[status(thm)],[c_4,c_2]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_624,plain,
% 26.47/4.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 26.47/4.01      inference(demodulation,[status(thm)],[c_623,c_253]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_625,plain,
% 26.47/4.01      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 26.47/4.01      inference(demodulation,[status(thm)],[c_624,c_2]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_1140,plain,
% 26.47/4.01      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = k2_xboole_0(X0,k1_xboole_0) ),
% 26.47/4.01      inference(superposition,[status(thm)],[c_625,c_253]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_7,negated_conjecture,
% 26.47/4.01      ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 26.47/4.01      inference(cnf_transformation,[],[f23]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_101,plain,
% 26.47/4.01      ( k4_xboole_0(X0,X1) != sK0 | k4_xboole_0(sK1,sK2) != X1 ),
% 26.47/4.01      inference(resolution_lifted,[status(thm)],[c_6,c_7]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_102,plain,
% 26.47/4.01      ( k4_xboole_0(X0,k4_xboole_0(sK1,sK2)) != sK0 ),
% 26.47/4.01      inference(unflattening,[status(thm)],[c_101]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_255,plain,
% 26.47/4.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(sK1,sK2))) != sK0 ),
% 26.47/4.01      inference(superposition,[status(thm)],[c_4,c_102]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_41240,plain,
% 26.47/4.01      ( k4_xboole_0(X0,k2_xboole_0(sK1,k1_xboole_0)) != sK0 ),
% 26.47/4.01      inference(superposition,[status(thm)],[c_1140,c_255]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_254,plain,
% 26.47/4.01      ( k4_xboole_0(X0,k2_xboole_0(X1,k1_xboole_0)) = k4_xboole_0(X0,X1) ),
% 26.47/4.01      inference(superposition,[status(thm)],[c_4,c_3]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_41482,plain,
% 26.47/4.01      ( k4_xboole_0(X0,sK1) != sK0 ),
% 26.47/4.01      inference(demodulation,[status(thm)],[c_41240,c_254]) ).
% 26.47/4.01  
% 26.47/4.01  cnf(c_42346,plain,
% 26.47/4.01      ( $false ),
% 26.47/4.01      inference(superposition,[status(thm)],[c_306,c_41482]) ).
% 26.47/4.01  
% 26.47/4.01  
% 26.47/4.01  % SZS output end CNFRefutation for theBenchmark.p
% 26.47/4.01  
% 26.47/4.01  ------                               Statistics
% 26.47/4.01  
% 26.47/4.01  ------ General
% 26.47/4.01  
% 26.47/4.01  abstr_ref_over_cycles:                  0
% 26.47/4.01  abstr_ref_under_cycles:                 0
% 26.47/4.01  gc_basic_clause_elim:                   0
% 26.47/4.01  forced_gc_time:                         0
% 26.47/4.01  parsing_time:                           0.009
% 26.47/4.01  unif_index_cands_time:                  0.
% 26.47/4.01  unif_index_add_time:                    0.
% 26.47/4.01  orderings_time:                         0.
% 26.47/4.01  out_proof_time:                         0.009
% 26.47/4.01  total_time:                             3.218
% 26.47/4.01  num_of_symbols:                         38
% 26.47/4.01  num_of_terms:                           83698
% 26.47/4.01  
% 26.47/4.01  ------ Preprocessing
% 26.47/4.01  
% 26.47/4.01  num_of_splits:                          0
% 26.47/4.01  num_of_split_atoms:                     0
% 26.47/4.01  num_of_reused_defs:                     0
% 26.47/4.01  num_eq_ax_congr_red:                    2
% 26.47/4.01  num_of_sem_filtered_clauses:            0
% 26.47/4.01  num_of_subtypes:                        0
% 26.47/4.01  monotx_restored_types:                  0
% 26.47/4.01  sat_num_of_epr_types:                   0
% 26.47/4.01  sat_num_of_non_cyclic_types:            0
% 26.47/4.01  sat_guarded_non_collapsed_types:        0
% 26.47/4.01  num_pure_diseq_elim:                    0
% 26.47/4.01  simp_replaced_by:                       0
% 26.47/4.01  res_preprocessed:                       22
% 26.47/4.01  prep_upred:                             0
% 26.47/4.01  prep_unflattend:                        7
% 26.47/4.01  smt_new_axioms:                         0
% 26.47/4.01  pred_elim_cands:                        1
% 26.47/4.01  pred_elim:                              1
% 26.47/4.01  pred_elim_cl:                           0
% 26.47/4.01  pred_elim_cycles:                       2
% 26.47/4.01  merged_defs:                            2
% 26.47/4.01  merged_defs_ncl:                        0
% 26.47/4.01  bin_hyper_res:                          2
% 26.47/4.01  prep_cycles:                            2
% 26.47/4.01  pred_elim_time:                         0.001
% 26.47/4.01  splitting_time:                         0.
% 26.47/4.01  sem_filter_time:                        0.
% 26.47/4.01  monotx_time:                            0.
% 26.47/4.01  subtype_inf_time:                       0.
% 26.47/4.01  
% 26.47/4.01  ------ Problem properties
% 26.47/4.01  
% 26.47/4.01  clauses:                                9
% 26.47/4.01  conjectures:                            0
% 26.47/4.01  epr:                                    0
% 26.47/4.01  horn:                                   9
% 26.47/4.01  ground:                                 3
% 26.47/4.01  unary:                                  8
% 26.47/4.01  binary:                                 1
% 26.47/4.01  lits:                                   10
% 26.47/4.01  lits_eq:                                10
% 26.47/4.01  fd_pure:                                0
% 26.47/4.01  fd_pseudo:                              0
% 26.47/4.01  fd_cond:                                0
% 26.47/4.01  fd_pseudo_cond:                         0
% 26.47/4.01  ac_symbols:                             0
% 26.47/4.01  
% 26.47/4.01  ------ Propositional Solver
% 26.47/4.01  
% 26.47/4.01  prop_solver_calls:                      29
% 26.47/4.01  prop_fast_solver_calls:                 388
% 26.47/4.01  smt_solver_calls:                       0
% 26.47/4.01  smt_fast_solver_calls:                  0
% 26.47/4.01  prop_num_of_clauses:                    14494
% 26.47/4.01  prop_preprocess_simplified:             13118
% 26.47/4.01  prop_fo_subsumed:                       0
% 26.47/4.01  prop_solver_time:                       0.
% 26.47/4.01  smt_solver_time:                        0.
% 26.47/4.01  smt_fast_solver_time:                   0.
% 26.47/4.01  prop_fast_solver_time:                  0.
% 26.47/4.01  prop_unsat_core_time:                   0.
% 26.47/4.01  
% 26.47/4.01  ------ QBF
% 26.47/4.01  
% 26.47/4.01  qbf_q_res:                              0
% 26.47/4.01  qbf_num_tautologies:                    0
% 26.47/4.01  qbf_prep_cycles:                        0
% 26.47/4.01  
% 26.47/4.01  ------ BMC1
% 26.47/4.01  
% 26.47/4.01  bmc1_current_bound:                     -1
% 26.47/4.01  bmc1_last_solved_bound:                 -1
% 26.47/4.02  bmc1_unsat_core_size:                   -1
% 26.47/4.02  bmc1_unsat_core_parents_size:           -1
% 26.47/4.02  bmc1_merge_next_fun:                    0
% 26.47/4.02  bmc1_unsat_core_clauses_time:           0.
% 26.47/4.02  
% 26.47/4.02  ------ Instantiation
% 26.47/4.02  
% 26.47/4.02  inst_num_of_clauses:                    3692
% 26.47/4.02  inst_num_in_passive:                    2231
% 26.47/4.02  inst_num_in_active:                     1351
% 26.47/4.02  inst_num_in_unprocessed:                110
% 26.47/4.02  inst_num_of_loops:                      1460
% 26.47/4.02  inst_num_of_learning_restarts:          0
% 26.47/4.02  inst_num_moves_active_passive:          101
% 26.47/4.02  inst_lit_activity:                      0
% 26.47/4.02  inst_lit_activity_moves:                0
% 26.47/4.02  inst_num_tautologies:                   0
% 26.47/4.02  inst_num_prop_implied:                  0
% 26.47/4.02  inst_num_existing_simplified:           0
% 26.47/4.02  inst_num_eq_res_simplified:             0
% 26.47/4.02  inst_num_child_elim:                    0
% 26.47/4.02  inst_num_of_dismatching_blockings:      2458
% 26.47/4.02  inst_num_of_non_proper_insts:           5449
% 26.47/4.02  inst_num_of_duplicates:                 0
% 26.47/4.02  inst_inst_num_from_inst_to_res:         0
% 26.47/4.02  inst_dismatching_checking_time:         0.
% 26.47/4.02  
% 26.47/4.02  ------ Resolution
% 26.47/4.02  
% 26.47/4.02  res_num_of_clauses:                     0
% 26.47/4.02  res_num_in_passive:                     0
% 26.47/4.02  res_num_in_active:                      0
% 26.47/4.02  res_num_of_loops:                       24
% 26.47/4.02  res_forward_subset_subsumed:            867
% 26.47/4.02  res_backward_subset_subsumed:           2
% 26.47/4.02  res_forward_subsumed:                   0
% 26.47/4.02  res_backward_subsumed:                  0
% 26.47/4.02  res_forward_subsumption_resolution:     0
% 26.47/4.02  res_backward_subsumption_resolution:    0
% 26.47/4.02  res_clause_to_clause_subsumption:       93526
% 26.47/4.02  res_orphan_elimination:                 0
% 26.47/4.02  res_tautology_del:                      278
% 26.47/4.02  res_num_eq_res_simplified:              1
% 26.47/4.02  res_num_sel_changes:                    0
% 26.47/4.02  res_moves_from_active_to_pass:          0
% 26.47/4.02  
% 26.47/4.02  ------ Superposition
% 26.47/4.02  
% 26.47/4.02  sup_time_total:                         0.
% 26.47/4.02  sup_time_generating:                    0.
% 26.47/4.02  sup_time_sim_full:                      0.
% 26.47/4.02  sup_time_sim_immed:                     0.
% 26.47/4.02  
% 26.47/4.02  sup_num_of_clauses:                     6376
% 26.47/4.02  sup_num_in_active:                      250
% 26.47/4.02  sup_num_in_passive:                     6126
% 26.47/4.02  sup_num_of_loops:                       290
% 26.47/4.02  sup_fw_superposition:                   8551
% 26.47/4.02  sup_bw_superposition:                   10353
% 26.47/4.02  sup_immediate_simplified:               9930
% 26.47/4.02  sup_given_eliminated:                   7
% 26.47/4.02  comparisons_done:                       0
% 26.47/4.02  comparisons_avoided:                    0
% 26.47/4.02  
% 26.47/4.02  ------ Simplifications
% 26.47/4.02  
% 26.47/4.02  
% 26.47/4.02  sim_fw_subset_subsumed:                 0
% 26.47/4.02  sim_bw_subset_subsumed:                 0
% 26.47/4.02  sim_fw_subsumed:                        4262
% 26.47/4.02  sim_bw_subsumed:                        56
% 26.47/4.02  sim_fw_subsumption_res:                 0
% 26.47/4.02  sim_bw_subsumption_res:                 0
% 26.47/4.02  sim_tautology_del:                      0
% 26.47/4.02  sim_eq_tautology_del:                   1724
% 26.47/4.02  sim_eq_res_simp:                        1
% 26.47/4.02  sim_fw_demodulated:                     5028
% 26.47/4.02  sim_bw_demodulated:                     136
% 26.47/4.02  sim_light_normalised:                   2496
% 26.47/4.02  sim_joinable_taut:                      0
% 26.47/4.02  sim_joinable_simp:                      0
% 26.47/4.02  sim_ac_normalised:                      0
% 26.47/4.02  sim_smt_subsumption:                    0
% 26.47/4.02  
%------------------------------------------------------------------------------
