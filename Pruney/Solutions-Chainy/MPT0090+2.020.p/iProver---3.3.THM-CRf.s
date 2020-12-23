%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:41 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 121 expanded)
%              Number of clauses        :   26 (  49 expanded)
%              Number of leaves         :    7 (  26 expanded)
%              Depth                    :   16
%              Number of atoms          :   86 ( 250 expanded)
%              Number of equality atoms :   58 ( 150 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_xboole_0(X0,X1)
      <=> k4_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ? [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <~> k4_xboole_0(X0,X1) = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( k4_xboole_0(X0,X1) != X0
        | ~ r1_xboole_0(X0,X1) )
      & ( k4_xboole_0(X0,X1) = X0
        | r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f11,plain,
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

fof(f12,plain,
    ( ( k4_xboole_0(sK0,sK1) != sK0
      | ~ r1_xboole_0(sK0,sK1) )
    & ( k4_xboole_0(sK0,sK1) = sK0
      | r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).

fof(f20,plain,
    ( k4_xboole_0(sK0,sK1) != sK0
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f13,f16])).

fof(f19,plain,
    ( k4_xboole_0(sK0,sK1) = sK0
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f17,f16,f16])).

cnf(c_4,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_5,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,sK1) != sK0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_48,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,sK1) != sK0 ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_111,plain,
    ( k4_xboole_0(X0,X1) != sK0
    | k4_xboole_0(sK0,sK1) != sK0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_48])).

cnf(c_112,plain,
    ( k4_xboole_0(X0,sK1) != sK0
    | k4_xboole_0(sK0,sK1) != sK0 ),
    inference(unflattening,[status(thm)],[c_111])).

cnf(c_113,plain,
    ( k4_xboole_0(sK0,sK1) != sK0 ),
    inference(instantiation,[status(thm)],[c_112])).

cnf(c_114,plain,
    ( k4_xboole_0(sK0,sK1) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_112,c_113])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_46,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_6,negated_conjecture,
    ( r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_50,plain,
    ( r1_xboole_0(sK0,sK1)
    | k4_xboole_0(sK0,sK1) = sK0 ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_103,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | k4_xboole_0(sK0,sK1) = sK0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_46,c_50])).

cnf(c_104,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
    | k4_xboole_0(sK0,sK1) = sK0 ),
    inference(unflattening,[status(thm)],[c_103])).

cnf(c_119,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_114,c_104])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f15])).

cnf(c_89,plain,
    ( X0 != X1
    | k4_xboole_0(X2,X0) != X3
    | k4_xboole_0(X3,k4_xboole_0(X3,X1)) = k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_46,c_4])).

cnf(c_90,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_89])).

cnf(c_135,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_90])).

cnf(c_140,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_135,c_2])).

cnf(c_3,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_163,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) ),
    inference(superposition,[status(thm)],[c_140,c_3])).

cnf(c_179,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_163,c_2])).

cnf(c_199,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_119,c_179])).

cnf(c_226,plain,
    ( k4_xboole_0(sK0,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_199,c_2])).

cnf(c_230,plain,
    ( sK0 != sK0 ),
    inference(demodulation,[status(thm)],[c_226,c_114])).

cnf(c_231,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_230])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:24:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.70/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/0.99  
% 1.70/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.70/0.99  
% 1.70/0.99  ------  iProver source info
% 1.70/0.99  
% 1.70/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.70/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.70/0.99  git: non_committed_changes: false
% 1.70/0.99  git: last_make_outside_of_git: false
% 1.70/0.99  
% 1.70/0.99  ------ 
% 1.70/0.99  
% 1.70/0.99  ------ Input Options
% 1.70/0.99  
% 1.70/0.99  --out_options                           all
% 1.70/0.99  --tptp_safe_out                         true
% 1.70/0.99  --problem_path                          ""
% 1.70/0.99  --include_path                          ""
% 1.70/0.99  --clausifier                            res/vclausify_rel
% 1.70/0.99  --clausifier_options                    --mode clausify
% 1.70/0.99  --stdin                                 false
% 1.70/0.99  --stats_out                             all
% 1.70/0.99  
% 1.70/0.99  ------ General Options
% 1.70/0.99  
% 1.70/0.99  --fof                                   false
% 1.70/0.99  --time_out_real                         305.
% 1.70/0.99  --time_out_virtual                      -1.
% 1.70/0.99  --symbol_type_check                     false
% 1.70/0.99  --clausify_out                          false
% 1.70/0.99  --sig_cnt_out                           false
% 1.70/0.99  --trig_cnt_out                          false
% 1.70/0.99  --trig_cnt_out_tolerance                1.
% 1.70/0.99  --trig_cnt_out_sk_spl                   false
% 1.70/0.99  --abstr_cl_out                          false
% 1.70/0.99  
% 1.70/0.99  ------ Global Options
% 1.70/0.99  
% 1.70/0.99  --schedule                              default
% 1.70/0.99  --add_important_lit                     false
% 1.70/0.99  --prop_solver_per_cl                    1000
% 1.70/0.99  --min_unsat_core                        false
% 1.70/0.99  --soft_assumptions                      false
% 1.70/0.99  --soft_lemma_size                       3
% 1.70/0.99  --prop_impl_unit_size                   0
% 1.70/0.99  --prop_impl_unit                        []
% 1.70/0.99  --share_sel_clauses                     true
% 1.70/0.99  --reset_solvers                         false
% 1.70/0.99  --bc_imp_inh                            [conj_cone]
% 1.70/0.99  --conj_cone_tolerance                   3.
% 1.70/0.99  --extra_neg_conj                        none
% 1.70/0.99  --large_theory_mode                     true
% 1.70/0.99  --prolific_symb_bound                   200
% 1.70/0.99  --lt_threshold                          2000
% 1.70/0.99  --clause_weak_htbl                      true
% 1.70/0.99  --gc_record_bc_elim                     false
% 1.70/0.99  
% 1.70/0.99  ------ Preprocessing Options
% 1.70/0.99  
% 1.70/0.99  --preprocessing_flag                    true
% 1.70/0.99  --time_out_prep_mult                    0.1
% 1.70/0.99  --splitting_mode                        input
% 1.70/0.99  --splitting_grd                         true
% 1.70/0.99  --splitting_cvd                         false
% 1.70/0.99  --splitting_cvd_svl                     false
% 1.70/0.99  --splitting_nvd                         32
% 1.70/0.99  --sub_typing                            true
% 1.70/0.99  --prep_gs_sim                           true
% 1.70/0.99  --prep_unflatten                        true
% 1.70/0.99  --prep_res_sim                          true
% 1.70/0.99  --prep_upred                            true
% 1.70/0.99  --prep_sem_filter                       exhaustive
% 1.70/0.99  --prep_sem_filter_out                   false
% 1.70/0.99  --pred_elim                             true
% 1.70/0.99  --res_sim_input                         true
% 1.70/0.99  --eq_ax_congr_red                       true
% 1.70/0.99  --pure_diseq_elim                       true
% 1.70/0.99  --brand_transform                       false
% 1.70/0.99  --non_eq_to_eq                          false
% 1.70/0.99  --prep_def_merge                        true
% 1.70/0.99  --prep_def_merge_prop_impl              false
% 1.70/0.99  --prep_def_merge_mbd                    true
% 1.70/0.99  --prep_def_merge_tr_red                 false
% 1.70/0.99  --prep_def_merge_tr_cl                  false
% 1.70/0.99  --smt_preprocessing                     true
% 1.70/0.99  --smt_ac_axioms                         fast
% 1.70/0.99  --preprocessed_out                      false
% 1.70/0.99  --preprocessed_stats                    false
% 1.70/0.99  
% 1.70/0.99  ------ Abstraction refinement Options
% 1.70/0.99  
% 1.70/0.99  --abstr_ref                             []
% 1.70/0.99  --abstr_ref_prep                        false
% 1.70/0.99  --abstr_ref_until_sat                   false
% 1.70/0.99  --abstr_ref_sig_restrict                funpre
% 1.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.70/0.99  --abstr_ref_under                       []
% 1.70/0.99  
% 1.70/0.99  ------ SAT Options
% 1.70/0.99  
% 1.70/0.99  --sat_mode                              false
% 1.70/0.99  --sat_fm_restart_options                ""
% 1.70/0.99  --sat_gr_def                            false
% 1.70/0.99  --sat_epr_types                         true
% 1.70/0.99  --sat_non_cyclic_types                  false
% 1.70/0.99  --sat_finite_models                     false
% 1.70/0.99  --sat_fm_lemmas                         false
% 1.70/0.99  --sat_fm_prep                           false
% 1.70/0.99  --sat_fm_uc_incr                        true
% 1.70/0.99  --sat_out_model                         small
% 1.70/0.99  --sat_out_clauses                       false
% 1.70/0.99  
% 1.70/0.99  ------ QBF Options
% 1.70/0.99  
% 1.70/0.99  --qbf_mode                              false
% 1.70/0.99  --qbf_elim_univ                         false
% 1.70/0.99  --qbf_dom_inst                          none
% 1.70/0.99  --qbf_dom_pre_inst                      false
% 1.70/0.99  --qbf_sk_in                             false
% 1.70/0.99  --qbf_pred_elim                         true
% 1.70/0.99  --qbf_split                             512
% 1.70/0.99  
% 1.70/0.99  ------ BMC1 Options
% 1.70/0.99  
% 1.70/0.99  --bmc1_incremental                      false
% 1.70/0.99  --bmc1_axioms                           reachable_all
% 1.70/0.99  --bmc1_min_bound                        0
% 1.70/0.99  --bmc1_max_bound                        -1
% 1.70/0.99  --bmc1_max_bound_default                -1
% 1.70/0.99  --bmc1_symbol_reachability              true
% 1.70/0.99  --bmc1_property_lemmas                  false
% 1.70/0.99  --bmc1_k_induction                      false
% 1.70/0.99  --bmc1_non_equiv_states                 false
% 1.70/0.99  --bmc1_deadlock                         false
% 1.70/0.99  --bmc1_ucm                              false
% 1.70/0.99  --bmc1_add_unsat_core                   none
% 1.70/0.99  --bmc1_unsat_core_children              false
% 1.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.70/0.99  --bmc1_out_stat                         full
% 1.70/0.99  --bmc1_ground_init                      false
% 1.70/0.99  --bmc1_pre_inst_next_state              false
% 1.70/0.99  --bmc1_pre_inst_state                   false
% 1.70/0.99  --bmc1_pre_inst_reach_state             false
% 1.70/0.99  --bmc1_out_unsat_core                   false
% 1.70/0.99  --bmc1_aig_witness_out                  false
% 1.70/0.99  --bmc1_verbose                          false
% 1.70/0.99  --bmc1_dump_clauses_tptp                false
% 1.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.70/0.99  --bmc1_dump_file                        -
% 1.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.70/0.99  --bmc1_ucm_extend_mode                  1
% 1.70/0.99  --bmc1_ucm_init_mode                    2
% 1.70/0.99  --bmc1_ucm_cone_mode                    none
% 1.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.70/0.99  --bmc1_ucm_relax_model                  4
% 1.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.70/0.99  --bmc1_ucm_layered_model                none
% 1.70/0.99  --bmc1_ucm_max_lemma_size               10
% 1.70/0.99  
% 1.70/0.99  ------ AIG Options
% 1.70/0.99  
% 1.70/0.99  --aig_mode                              false
% 1.70/0.99  
% 1.70/0.99  ------ Instantiation Options
% 1.70/0.99  
% 1.70/0.99  --instantiation_flag                    true
% 1.70/0.99  --inst_sos_flag                         false
% 1.70/0.99  --inst_sos_phase                        true
% 1.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.70/0.99  --inst_lit_sel_side                     num_symb
% 1.70/0.99  --inst_solver_per_active                1400
% 1.70/0.99  --inst_solver_calls_frac                1.
% 1.70/0.99  --inst_passive_queue_type               priority_queues
% 1.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.70/0.99  --inst_passive_queues_freq              [25;2]
% 1.70/0.99  --inst_dismatching                      true
% 1.70/0.99  --inst_eager_unprocessed_to_passive     true
% 1.70/0.99  --inst_prop_sim_given                   true
% 1.70/0.99  --inst_prop_sim_new                     false
% 1.70/0.99  --inst_subs_new                         false
% 1.70/0.99  --inst_eq_res_simp                      false
% 1.70/0.99  --inst_subs_given                       false
% 1.70/0.99  --inst_orphan_elimination               true
% 1.70/0.99  --inst_learning_loop_flag               true
% 1.70/0.99  --inst_learning_start                   3000
% 1.70/0.99  --inst_learning_factor                  2
% 1.70/0.99  --inst_start_prop_sim_after_learn       3
% 1.70/0.99  --inst_sel_renew                        solver
% 1.70/0.99  --inst_lit_activity_flag                true
% 1.70/0.99  --inst_restr_to_given                   false
% 1.70/0.99  --inst_activity_threshold               500
% 1.70/0.99  --inst_out_proof                        true
% 1.70/0.99  
% 1.70/0.99  ------ Resolution Options
% 1.70/0.99  
% 1.70/0.99  --resolution_flag                       true
% 1.70/0.99  --res_lit_sel                           adaptive
% 1.70/0.99  --res_lit_sel_side                      none
% 1.70/0.99  --res_ordering                          kbo
% 1.70/0.99  --res_to_prop_solver                    active
% 1.70/0.99  --res_prop_simpl_new                    false
% 1.70/0.99  --res_prop_simpl_given                  true
% 1.70/0.99  --res_passive_queue_type                priority_queues
% 1.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.70/0.99  --res_passive_queues_freq               [15;5]
% 1.70/0.99  --res_forward_subs                      full
% 1.70/0.99  --res_backward_subs                     full
% 1.70/0.99  --res_forward_subs_resolution           true
% 1.70/0.99  --res_backward_subs_resolution          true
% 1.70/0.99  --res_orphan_elimination                true
% 1.70/0.99  --res_time_limit                        2.
% 1.70/0.99  --res_out_proof                         true
% 1.70/0.99  
% 1.70/0.99  ------ Superposition Options
% 1.70/0.99  
% 1.70/0.99  --superposition_flag                    true
% 1.70/0.99  --sup_passive_queue_type                priority_queues
% 1.70/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.70/0.99  --demod_completeness_check              fast
% 1.70/0.99  --demod_use_ground                      true
% 1.70/0.99  --sup_to_prop_solver                    passive
% 1.70/0.99  --sup_prop_simpl_new                    true
% 1.70/0.99  --sup_prop_simpl_given                  true
% 1.70/0.99  --sup_fun_splitting                     false
% 1.70/0.99  --sup_smt_interval                      50000
% 1.70/0.99  
% 1.70/0.99  ------ Superposition Simplification Setup
% 1.70/0.99  
% 1.70/0.99  --sup_indices_passive                   []
% 1.70/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.99  --sup_full_bw                           [BwDemod]
% 1.70/0.99  --sup_immed_triv                        [TrivRules]
% 1.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.99  --sup_immed_bw_main                     []
% 1.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.70/0.99  
% 1.70/0.99  ------ Combination Options
% 1.70/0.99  
% 1.70/0.99  --comb_res_mult                         3
% 1.70/0.99  --comb_sup_mult                         2
% 1.70/0.99  --comb_inst_mult                        10
% 1.70/0.99  
% 1.70/0.99  ------ Debug Options
% 1.70/0.99  
% 1.70/0.99  --dbg_backtrace                         false
% 1.70/0.99  --dbg_dump_prop_clauses                 false
% 1.70/0.99  --dbg_dump_prop_clauses_file            -
% 1.70/0.99  --dbg_out_stat                          false
% 1.70/0.99  ------ Parsing...
% 1.70/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.70/0.99  
% 1.70/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.70/0.99  
% 1.70/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.70/0.99  
% 1.70/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 1.70/0.99  ------ Proving...
% 1.70/0.99  ------ Problem Properties 
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  clauses                                 5
% 1.70/0.99  conjectures                             0
% 1.70/0.99  EPR                                     0
% 1.70/0.99  Horn                                    5
% 1.70/0.99  unary                                   5
% 1.70/0.99  binary                                  0
% 1.70/0.99  lits                                    5
% 1.70/0.99  lits eq                                 5
% 1.70/0.99  fd_pure                                 0
% 1.70/0.99  fd_pseudo                               0
% 1.70/0.99  fd_cond                                 0
% 1.70/0.99  fd_pseudo_cond                          0
% 1.70/0.99  AC symbols                              0
% 1.70/0.99  
% 1.70/0.99  ------ Schedule UEQ
% 1.70/0.99  
% 1.70/0.99  ------ pure equality problem: resolution off 
% 1.70/0.99  
% 1.70/0.99  ------ Option_UEQ Time Limit: Unbounded
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  ------ 
% 1.70/0.99  Current options:
% 1.70/0.99  ------ 
% 1.70/0.99  
% 1.70/0.99  ------ Input Options
% 1.70/0.99  
% 1.70/0.99  --out_options                           all
% 1.70/0.99  --tptp_safe_out                         true
% 1.70/0.99  --problem_path                          ""
% 1.70/0.99  --include_path                          ""
% 1.70/0.99  --clausifier                            res/vclausify_rel
% 1.70/0.99  --clausifier_options                    --mode clausify
% 1.70/0.99  --stdin                                 false
% 1.70/0.99  --stats_out                             all
% 1.70/0.99  
% 1.70/0.99  ------ General Options
% 1.70/0.99  
% 1.70/0.99  --fof                                   false
% 1.70/0.99  --time_out_real                         305.
% 1.70/0.99  --time_out_virtual                      -1.
% 1.70/0.99  --symbol_type_check                     false
% 1.70/0.99  --clausify_out                          false
% 1.70/0.99  --sig_cnt_out                           false
% 1.70/0.99  --trig_cnt_out                          false
% 1.70/0.99  --trig_cnt_out_tolerance                1.
% 1.70/0.99  --trig_cnt_out_sk_spl                   false
% 1.70/0.99  --abstr_cl_out                          false
% 1.70/0.99  
% 1.70/0.99  ------ Global Options
% 1.70/0.99  
% 1.70/0.99  --schedule                              default
% 1.70/0.99  --add_important_lit                     false
% 1.70/0.99  --prop_solver_per_cl                    1000
% 1.70/0.99  --min_unsat_core                        false
% 1.70/0.99  --soft_assumptions                      false
% 1.70/0.99  --soft_lemma_size                       3
% 1.70/0.99  --prop_impl_unit_size                   0
% 1.70/0.99  --prop_impl_unit                        []
% 1.70/0.99  --share_sel_clauses                     true
% 1.70/0.99  --reset_solvers                         false
% 1.70/0.99  --bc_imp_inh                            [conj_cone]
% 1.70/0.99  --conj_cone_tolerance                   3.
% 1.70/0.99  --extra_neg_conj                        none
% 1.70/0.99  --large_theory_mode                     true
% 1.70/0.99  --prolific_symb_bound                   200
% 1.70/0.99  --lt_threshold                          2000
% 1.70/0.99  --clause_weak_htbl                      true
% 1.70/0.99  --gc_record_bc_elim                     false
% 1.70/0.99  
% 1.70/0.99  ------ Preprocessing Options
% 1.70/0.99  
% 1.70/0.99  --preprocessing_flag                    true
% 1.70/0.99  --time_out_prep_mult                    0.1
% 1.70/0.99  --splitting_mode                        input
% 1.70/0.99  --splitting_grd                         true
% 1.70/0.99  --splitting_cvd                         false
% 1.70/0.99  --splitting_cvd_svl                     false
% 1.70/0.99  --splitting_nvd                         32
% 1.70/0.99  --sub_typing                            true
% 1.70/0.99  --prep_gs_sim                           true
% 1.70/0.99  --prep_unflatten                        true
% 1.70/0.99  --prep_res_sim                          true
% 1.70/0.99  --prep_upred                            true
% 1.70/0.99  --prep_sem_filter                       exhaustive
% 1.70/0.99  --prep_sem_filter_out                   false
% 1.70/0.99  --pred_elim                             true
% 1.70/0.99  --res_sim_input                         true
% 1.70/0.99  --eq_ax_congr_red                       true
% 1.70/0.99  --pure_diseq_elim                       true
% 1.70/0.99  --brand_transform                       false
% 1.70/0.99  --non_eq_to_eq                          false
% 1.70/0.99  --prep_def_merge                        true
% 1.70/0.99  --prep_def_merge_prop_impl              false
% 1.70/0.99  --prep_def_merge_mbd                    true
% 1.70/0.99  --prep_def_merge_tr_red                 false
% 1.70/0.99  --prep_def_merge_tr_cl                  false
% 1.70/0.99  --smt_preprocessing                     true
% 1.70/0.99  --smt_ac_axioms                         fast
% 1.70/0.99  --preprocessed_out                      false
% 1.70/0.99  --preprocessed_stats                    false
% 1.70/0.99  
% 1.70/0.99  ------ Abstraction refinement Options
% 1.70/0.99  
% 1.70/0.99  --abstr_ref                             []
% 1.70/0.99  --abstr_ref_prep                        false
% 1.70/0.99  --abstr_ref_until_sat                   false
% 1.70/0.99  --abstr_ref_sig_restrict                funpre
% 1.70/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.70/0.99  --abstr_ref_under                       []
% 1.70/0.99  
% 1.70/0.99  ------ SAT Options
% 1.70/0.99  
% 1.70/0.99  --sat_mode                              false
% 1.70/0.99  --sat_fm_restart_options                ""
% 1.70/0.99  --sat_gr_def                            false
% 1.70/0.99  --sat_epr_types                         true
% 1.70/0.99  --sat_non_cyclic_types                  false
% 1.70/0.99  --sat_finite_models                     false
% 1.70/0.99  --sat_fm_lemmas                         false
% 1.70/0.99  --sat_fm_prep                           false
% 1.70/0.99  --sat_fm_uc_incr                        true
% 1.70/0.99  --sat_out_model                         small
% 1.70/0.99  --sat_out_clauses                       false
% 1.70/0.99  
% 1.70/0.99  ------ QBF Options
% 1.70/0.99  
% 1.70/0.99  --qbf_mode                              false
% 1.70/0.99  --qbf_elim_univ                         false
% 1.70/0.99  --qbf_dom_inst                          none
% 1.70/0.99  --qbf_dom_pre_inst                      false
% 1.70/0.99  --qbf_sk_in                             false
% 1.70/0.99  --qbf_pred_elim                         true
% 1.70/0.99  --qbf_split                             512
% 1.70/0.99  
% 1.70/0.99  ------ BMC1 Options
% 1.70/0.99  
% 1.70/0.99  --bmc1_incremental                      false
% 1.70/0.99  --bmc1_axioms                           reachable_all
% 1.70/0.99  --bmc1_min_bound                        0
% 1.70/0.99  --bmc1_max_bound                        -1
% 1.70/0.99  --bmc1_max_bound_default                -1
% 1.70/0.99  --bmc1_symbol_reachability              true
% 1.70/0.99  --bmc1_property_lemmas                  false
% 1.70/0.99  --bmc1_k_induction                      false
% 1.70/0.99  --bmc1_non_equiv_states                 false
% 1.70/0.99  --bmc1_deadlock                         false
% 1.70/0.99  --bmc1_ucm                              false
% 1.70/0.99  --bmc1_add_unsat_core                   none
% 1.70/0.99  --bmc1_unsat_core_children              false
% 1.70/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.70/0.99  --bmc1_out_stat                         full
% 1.70/0.99  --bmc1_ground_init                      false
% 1.70/0.99  --bmc1_pre_inst_next_state              false
% 1.70/0.99  --bmc1_pre_inst_state                   false
% 1.70/0.99  --bmc1_pre_inst_reach_state             false
% 1.70/0.99  --bmc1_out_unsat_core                   false
% 1.70/0.99  --bmc1_aig_witness_out                  false
% 1.70/0.99  --bmc1_verbose                          false
% 1.70/0.99  --bmc1_dump_clauses_tptp                false
% 1.70/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.70/0.99  --bmc1_dump_file                        -
% 1.70/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.70/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.70/0.99  --bmc1_ucm_extend_mode                  1
% 1.70/0.99  --bmc1_ucm_init_mode                    2
% 1.70/0.99  --bmc1_ucm_cone_mode                    none
% 1.70/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.70/0.99  --bmc1_ucm_relax_model                  4
% 1.70/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.70/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.70/0.99  --bmc1_ucm_layered_model                none
% 1.70/0.99  --bmc1_ucm_max_lemma_size               10
% 1.70/0.99  
% 1.70/0.99  ------ AIG Options
% 1.70/0.99  
% 1.70/0.99  --aig_mode                              false
% 1.70/0.99  
% 1.70/0.99  ------ Instantiation Options
% 1.70/0.99  
% 1.70/0.99  --instantiation_flag                    false
% 1.70/0.99  --inst_sos_flag                         false
% 1.70/0.99  --inst_sos_phase                        true
% 1.70/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.70/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.70/0.99  --inst_lit_sel_side                     num_symb
% 1.70/0.99  --inst_solver_per_active                1400
% 1.70/0.99  --inst_solver_calls_frac                1.
% 1.70/0.99  --inst_passive_queue_type               priority_queues
% 1.70/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.70/0.99  --inst_passive_queues_freq              [25;2]
% 1.70/0.99  --inst_dismatching                      true
% 1.70/0.99  --inst_eager_unprocessed_to_passive     true
% 1.70/0.99  --inst_prop_sim_given                   true
% 1.70/0.99  --inst_prop_sim_new                     false
% 1.70/0.99  --inst_subs_new                         false
% 1.70/0.99  --inst_eq_res_simp                      false
% 1.70/0.99  --inst_subs_given                       false
% 1.70/0.99  --inst_orphan_elimination               true
% 1.70/0.99  --inst_learning_loop_flag               true
% 1.70/0.99  --inst_learning_start                   3000
% 1.70/0.99  --inst_learning_factor                  2
% 1.70/0.99  --inst_start_prop_sim_after_learn       3
% 1.70/0.99  --inst_sel_renew                        solver
% 1.70/0.99  --inst_lit_activity_flag                true
% 1.70/0.99  --inst_restr_to_given                   false
% 1.70/0.99  --inst_activity_threshold               500
% 1.70/0.99  --inst_out_proof                        true
% 1.70/0.99  
% 1.70/0.99  ------ Resolution Options
% 1.70/0.99  
% 1.70/0.99  --resolution_flag                       false
% 1.70/0.99  --res_lit_sel                           adaptive
% 1.70/0.99  --res_lit_sel_side                      none
% 1.70/0.99  --res_ordering                          kbo
% 1.70/0.99  --res_to_prop_solver                    active
% 1.70/0.99  --res_prop_simpl_new                    false
% 1.70/0.99  --res_prop_simpl_given                  true
% 1.70/0.99  --res_passive_queue_type                priority_queues
% 1.70/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.70/0.99  --res_passive_queues_freq               [15;5]
% 1.70/0.99  --res_forward_subs                      full
% 1.70/0.99  --res_backward_subs                     full
% 1.70/0.99  --res_forward_subs_resolution           true
% 1.70/0.99  --res_backward_subs_resolution          true
% 1.70/0.99  --res_orphan_elimination                true
% 1.70/0.99  --res_time_limit                        2.
% 1.70/0.99  --res_out_proof                         true
% 1.70/0.99  
% 1.70/0.99  ------ Superposition Options
% 1.70/0.99  
% 1.70/0.99  --superposition_flag                    true
% 1.70/0.99  --sup_passive_queue_type                priority_queues
% 1.70/0.99  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.70/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.70/0.99  --demod_completeness_check              fast
% 1.70/0.99  --demod_use_ground                      true
% 1.70/0.99  --sup_to_prop_solver                    active
% 1.70/0.99  --sup_prop_simpl_new                    false
% 1.70/0.99  --sup_prop_simpl_given                  false
% 1.70/0.99  --sup_fun_splitting                     true
% 1.70/0.99  --sup_smt_interval                      10000
% 1.70/0.99  
% 1.70/0.99  ------ Superposition Simplification Setup
% 1.70/0.99  
% 1.70/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 1.70/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 1.70/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.70/0.99  --sup_full_triv                         [TrivRules]
% 1.70/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 1.70/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 1.70/0.99  --sup_immed_triv                        [TrivRules]
% 1.70/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.70/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 1.70/0.99  --sup_immed_bw_main                     []
% 1.70/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 1.70/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.70/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 1.70/0.99  --sup_input_bw                          [BwDemod;BwSubsumption]
% 1.70/0.99  
% 1.70/0.99  ------ Combination Options
% 1.70/0.99  
% 1.70/0.99  --comb_res_mult                         1
% 1.70/0.99  --comb_sup_mult                         1
% 1.70/0.99  --comb_inst_mult                        1000000
% 1.70/0.99  
% 1.70/0.99  ------ Debug Options
% 1.70/0.99  
% 1.70/0.99  --dbg_backtrace                         false
% 1.70/0.99  --dbg_dump_prop_clauses                 false
% 1.70/0.99  --dbg_dump_prop_clauses_file            -
% 1.70/0.99  --dbg_out_stat                          false
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  ------ Proving...
% 1.70/0.99  
% 1.70/0.99  
% 1.70/0.99  % SZS status Theorem for theBenchmark.p
% 1.70/0.99  
% 1.70/0.99   Resolution empty clause
% 1.70/0.99  
% 1.70/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 1.70/0.99  
% 1.70/0.99  fof(f5,axiom,(
% 1.70/0.99    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f18,plain,(
% 1.70/0.99    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.70/0.99    inference(cnf_transformation,[],[f5])).
% 1.70/0.99  
% 1.70/0.99  fof(f6,conjecture,(
% 1.70/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f7,negated_conjecture,(
% 1.70/0.99    ~! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.70/0.99    inference(negated_conjecture,[],[f6])).
% 1.70/0.99  
% 1.70/0.99  fof(f8,plain,(
% 1.70/0.99    ? [X0,X1] : (r1_xboole_0(X0,X1) <~> k4_xboole_0(X0,X1) = X0)),
% 1.70/0.99    inference(ennf_transformation,[],[f7])).
% 1.70/0.99  
% 1.70/0.99  fof(f10,plain,(
% 1.70/0.99    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1)))),
% 1.70/0.99    inference(nnf_transformation,[],[f8])).
% 1.70/0.99  
% 1.70/0.99  fof(f11,plain,(
% 1.70/0.99    ? [X0,X1] : ((k4_xboole_0(X0,X1) != X0 | ~r1_xboole_0(X0,X1)) & (k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1))) => ((k4_xboole_0(sK0,sK1) != sK0 | ~r1_xboole_0(sK0,sK1)) & (k4_xboole_0(sK0,sK1) = sK0 | r1_xboole_0(sK0,sK1)))),
% 1.70/0.99    introduced(choice_axiom,[])).
% 1.70/0.99  
% 1.70/0.99  fof(f12,plain,(
% 1.70/0.99    (k4_xboole_0(sK0,sK1) != sK0 | ~r1_xboole_0(sK0,sK1)) & (k4_xboole_0(sK0,sK1) = sK0 | r1_xboole_0(sK0,sK1))),
% 1.70/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f11])).
% 1.70/0.99  
% 1.70/0.99  fof(f20,plain,(
% 1.70/0.99    k4_xboole_0(sK0,sK1) != sK0 | ~r1_xboole_0(sK0,sK1)),
% 1.70/0.99    inference(cnf_transformation,[],[f12])).
% 1.70/0.99  
% 1.70/0.99  fof(f1,axiom,(
% 1.70/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f9,plain,(
% 1.70/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.70/0.99    inference(nnf_transformation,[],[f1])).
% 1.70/0.99  
% 1.70/0.99  fof(f13,plain,(
% 1.70/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.70/0.99    inference(cnf_transformation,[],[f9])).
% 1.70/0.99  
% 1.70/0.99  fof(f3,axiom,(
% 1.70/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f16,plain,(
% 1.70/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.70/0.99    inference(cnf_transformation,[],[f3])).
% 1.70/0.99  
% 1.70/0.99  fof(f22,plain,(
% 1.70/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.70/0.99    inference(definition_unfolding,[],[f13,f16])).
% 1.70/0.99  
% 1.70/0.99  fof(f19,plain,(
% 1.70/0.99    k4_xboole_0(sK0,sK1) = sK0 | r1_xboole_0(sK0,sK1)),
% 1.70/0.99    inference(cnf_transformation,[],[f12])).
% 1.70/0.99  
% 1.70/0.99  fof(f2,axiom,(
% 1.70/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f15,plain,(
% 1.70/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.70/0.99    inference(cnf_transformation,[],[f2])).
% 1.70/0.99  
% 1.70/0.99  fof(f4,axiom,(
% 1.70/0.99    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.70/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.70/0.99  
% 1.70/0.99  fof(f17,plain,(
% 1.70/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.70/0.99    inference(cnf_transformation,[],[f4])).
% 1.70/0.99  
% 1.70/0.99  fof(f23,plain,(
% 1.70/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.70/0.99    inference(definition_unfolding,[],[f17,f16,f16])).
% 1.70/0.99  
% 1.70/0.99  cnf(c_4,plain,
% 1.70/0.99      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 1.70/0.99      inference(cnf_transformation,[],[f18]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_5,negated_conjecture,
% 1.70/0.99      ( ~ r1_xboole_0(sK0,sK1) | k4_xboole_0(sK0,sK1) != sK0 ),
% 1.70/0.99      inference(cnf_transformation,[],[f20]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_48,plain,
% 1.70/0.99      ( ~ r1_xboole_0(sK0,sK1) | k4_xboole_0(sK0,sK1) != sK0 ),
% 1.70/0.99      inference(prop_impl,[status(thm)],[c_5]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_111,plain,
% 1.70/0.99      ( k4_xboole_0(X0,X1) != sK0 | k4_xboole_0(sK0,sK1) != sK0 | sK1 != X1 ),
% 1.70/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_48]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_112,plain,
% 1.70/0.99      ( k4_xboole_0(X0,sK1) != sK0 | k4_xboole_0(sK0,sK1) != sK0 ),
% 1.70/0.99      inference(unflattening,[status(thm)],[c_111]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_113,plain,
% 1.70/0.99      ( k4_xboole_0(sK0,sK1) != sK0 ),
% 1.70/0.99      inference(instantiation,[status(thm)],[c_112]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_114,plain,
% 1.70/0.99      ( k4_xboole_0(sK0,sK1) != sK0 ),
% 1.70/0.99      inference(global_propositional_subsumption,[status(thm)],[c_112,c_113]) ).
% 1.70/0.99  
% 1.70/0.99  cnf(c_1,plain,
% 1.70/0.99      ( ~ r1_xboole_0(X0,X1)
% 1.70/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 1.70/1.00      inference(cnf_transformation,[],[f22]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_46,plain,
% 1.70/1.00      ( ~ r1_xboole_0(X0,X1)
% 1.70/1.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 1.70/1.00      inference(prop_impl,[status(thm)],[c_1]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_6,negated_conjecture,
% 1.70/1.00      ( r1_xboole_0(sK0,sK1) | k4_xboole_0(sK0,sK1) = sK0 ),
% 1.70/1.00      inference(cnf_transformation,[],[f19]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_50,plain,
% 1.70/1.00      ( r1_xboole_0(sK0,sK1) | k4_xboole_0(sK0,sK1) = sK0 ),
% 1.70/1.00      inference(prop_impl,[status(thm)],[c_6]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_103,plain,
% 1.70/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 1.70/1.00      | k4_xboole_0(sK0,sK1) = sK0
% 1.70/1.00      | sK1 != X1
% 1.70/1.00      | sK0 != X0 ),
% 1.70/1.00      inference(resolution_lifted,[status(thm)],[c_46,c_50]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_104,plain,
% 1.70/1.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0
% 1.70/1.00      | k4_xboole_0(sK0,sK1) = sK0 ),
% 1.70/1.00      inference(unflattening,[status(thm)],[c_103]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_119,plain,
% 1.70/1.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k1_xboole_0 ),
% 1.70/1.00      inference(backward_subsumption_resolution,[status(thm)],[c_114,c_104]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_2,plain,
% 1.70/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 1.70/1.00      inference(cnf_transformation,[],[f15]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_89,plain,
% 1.70/1.00      ( X0 != X1
% 1.70/1.00      | k4_xboole_0(X2,X0) != X3
% 1.70/1.00      | k4_xboole_0(X3,k4_xboole_0(X3,X1)) = k1_xboole_0 ),
% 1.70/1.00      inference(resolution_lifted,[status(thm)],[c_46,c_4]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_90,plain,
% 1.70/1.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),X1)) = k1_xboole_0 ),
% 1.70/1.00      inference(unflattening,[status(thm)],[c_89]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_135,plain,
% 1.70/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 1.70/1.00      inference(superposition,[status(thm)],[c_2,c_90]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_140,plain,
% 1.70/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 1.70/1.00      inference(light_normalisation,[status(thm)],[c_135,c_2]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_3,plain,
% 1.70/1.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 1.70/1.00      inference(cnf_transformation,[],[f23]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_163,plain,
% 1.70/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_xboole_0(X0,k1_xboole_0),X1) ),
% 1.70/1.00      inference(superposition,[status(thm)],[c_140,c_3]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_179,plain,
% 1.70/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 1.70/1.00      inference(light_normalisation,[status(thm)],[c_163,c_2]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_199,plain,
% 1.70/1.00      ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,sK1) ),
% 1.70/1.00      inference(superposition,[status(thm)],[c_119,c_179]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_226,plain,
% 1.70/1.00      ( k4_xboole_0(sK0,sK1) = sK0 ),
% 1.70/1.00      inference(demodulation,[status(thm)],[c_199,c_2]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_230,plain,
% 1.70/1.00      ( sK0 != sK0 ),
% 1.70/1.00      inference(demodulation,[status(thm)],[c_226,c_114]) ).
% 1.70/1.00  
% 1.70/1.00  cnf(c_231,plain,
% 1.70/1.00      ( $false ),
% 1.70/1.00      inference(equality_resolution_simp,[status(thm)],[c_230]) ).
% 1.70/1.00  
% 1.70/1.00  
% 1.70/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.70/1.00  
% 1.70/1.00  ------                               Statistics
% 1.70/1.00  
% 1.70/1.00  ------ General
% 1.70/1.00  
% 1.70/1.00  abstr_ref_over_cycles:                  0
% 1.70/1.00  abstr_ref_under_cycles:                 0
% 1.70/1.00  gc_basic_clause_elim:                   0
% 1.70/1.00  forced_gc_time:                         0
% 1.70/1.00  parsing_time:                           0.017
% 1.70/1.00  unif_index_cands_time:                  0.
% 1.70/1.00  unif_index_add_time:                    0.
% 1.70/1.00  orderings_time:                         0.
% 1.70/1.00  out_proof_time:                         0.008
% 1.70/1.00  total_time:                             0.073
% 1.70/1.00  num_of_symbols:                         36
% 1.70/1.00  num_of_terms:                           390
% 1.70/1.00  
% 1.70/1.00  ------ Preprocessing
% 1.70/1.00  
% 1.70/1.00  num_of_splits:                          0
% 1.70/1.00  num_of_split_atoms:                     0
% 1.70/1.00  num_of_reused_defs:                     0
% 1.70/1.00  num_eq_ax_congr_red:                    0
% 1.70/1.00  num_of_sem_filtered_clauses:            0
% 1.70/1.00  num_of_subtypes:                        0
% 1.70/1.00  monotx_restored_types:                  0
% 1.70/1.00  sat_num_of_epr_types:                   0
% 1.70/1.00  sat_num_of_non_cyclic_types:            0
% 1.70/1.00  sat_guarded_non_collapsed_types:        0
% 1.70/1.00  num_pure_diseq_elim:                    0
% 1.70/1.00  simp_replaced_by:                       0
% 1.70/1.00  res_preprocessed:                       20
% 1.70/1.00  prep_upred:                             0
% 1.70/1.00  prep_unflattend:                        7
% 1.70/1.00  smt_new_axioms:                         0
% 1.70/1.00  pred_elim_cands:                        0
% 1.70/1.00  pred_elim:                              1
% 1.70/1.00  pred_elim_cl:                           2
% 1.70/1.00  pred_elim_cycles:                       2
% 1.70/1.00  merged_defs:                            4
% 1.70/1.00  merged_defs_ncl:                        0
% 1.70/1.00  bin_hyper_res:                          4
% 1.70/1.00  prep_cycles:                            3
% 1.70/1.00  pred_elim_time:                         0.001
% 1.70/1.00  splitting_time:                         0.
% 1.70/1.00  sem_filter_time:                        0.
% 1.70/1.00  monotx_time:                            0.
% 1.70/1.00  subtype_inf_time:                       0.
% 1.70/1.00  
% 1.70/1.00  ------ Problem properties
% 1.70/1.00  
% 1.70/1.00  clauses:                                5
% 1.70/1.00  conjectures:                            0
% 1.70/1.00  epr:                                    0
% 1.70/1.00  horn:                                   5
% 1.70/1.00  ground:                                 2
% 1.70/1.00  unary:                                  5
% 1.70/1.00  binary:                                 0
% 1.70/1.00  lits:                                   5
% 1.70/1.00  lits_eq:                                5
% 1.70/1.00  fd_pure:                                0
% 1.70/1.00  fd_pseudo:                              0
% 1.70/1.00  fd_cond:                                0
% 1.70/1.00  fd_pseudo_cond:                         0
% 1.70/1.00  ac_symbols:                             0
% 1.70/1.00  
% 1.70/1.00  ------ Propositional Solver
% 1.70/1.00  
% 1.70/1.00  prop_solver_calls:                      17
% 1.70/1.00  prop_fast_solver_calls:                 64
% 1.70/1.00  smt_solver_calls:                       0
% 1.70/1.00  smt_fast_solver_calls:                  0
% 1.70/1.00  prop_num_of_clauses:                    40
% 1.70/1.00  prop_preprocess_simplified:             312
% 1.70/1.00  prop_fo_subsumed:                       1
% 1.70/1.00  prop_solver_time:                       0.
% 1.70/1.00  smt_solver_time:                        0.
% 1.70/1.00  smt_fast_solver_time:                   0.
% 1.70/1.00  prop_fast_solver_time:                  0.
% 1.70/1.00  prop_unsat_core_time:                   0.
% 1.70/1.00  
% 1.70/1.00  ------ QBF
% 1.70/1.00  
% 1.70/1.00  qbf_q_res:                              0
% 1.70/1.00  qbf_num_tautologies:                    0
% 1.70/1.00  qbf_prep_cycles:                        0
% 1.70/1.00  
% 1.70/1.00  ------ BMC1
% 1.70/1.00  
% 1.70/1.00  bmc1_current_bound:                     -1
% 1.70/1.00  bmc1_last_solved_bound:                 -1
% 1.70/1.00  bmc1_unsat_core_size:                   -1
% 1.70/1.00  bmc1_unsat_core_parents_size:           -1
% 1.70/1.00  bmc1_merge_next_fun:                    0
% 1.70/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.70/1.00  
% 1.70/1.00  ------ Instantiation
% 1.70/1.00  
% 1.70/1.00  inst_num_of_clauses:                    0
% 1.70/1.00  inst_num_in_passive:                    0
% 1.70/1.00  inst_num_in_active:                     0
% 1.70/1.00  inst_num_in_unprocessed:                0
% 1.70/1.00  inst_num_of_loops:                      0
% 1.70/1.00  inst_num_of_learning_restarts:          0
% 1.70/1.00  inst_num_moves_active_passive:          0
% 1.70/1.00  inst_lit_activity:                      0
% 1.70/1.00  inst_lit_activity_moves:                0
% 1.70/1.00  inst_num_tautologies:                   0
% 1.70/1.00  inst_num_prop_implied:                  0
% 1.70/1.00  inst_num_existing_simplified:           0
% 1.70/1.00  inst_num_eq_res_simplified:             0
% 1.70/1.00  inst_num_child_elim:                    0
% 1.70/1.00  inst_num_of_dismatching_blockings:      0
% 1.70/1.00  inst_num_of_non_proper_insts:           0
% 1.70/1.00  inst_num_of_duplicates:                 0
% 1.70/1.00  inst_inst_num_from_inst_to_res:         0
% 1.70/1.00  inst_dismatching_checking_time:         0.
% 1.70/1.00  
% 1.70/1.00  ------ Resolution
% 1.70/1.00  
% 1.70/1.00  res_num_of_clauses:                     0
% 1.70/1.00  res_num_in_passive:                     0
% 1.70/1.00  res_num_in_active:                      0
% 1.70/1.00  res_num_of_loops:                       23
% 1.70/1.00  res_forward_subset_subsumed:            0
% 1.70/1.00  res_backward_subset_subsumed:           0
% 1.70/1.00  res_forward_subsumed:                   0
% 1.70/1.00  res_backward_subsumed:                  1
% 1.70/1.00  res_forward_subsumption_resolution:     0
% 1.70/1.00  res_backward_subsumption_resolution:    1
% 1.70/1.00  res_clause_to_clause_subsumption:       107
% 1.70/1.00  res_orphan_elimination:                 0
% 1.70/1.00  res_tautology_del:                      10
% 1.70/1.00  res_num_eq_res_simplified:              0
% 1.70/1.00  res_num_sel_changes:                    0
% 1.70/1.00  res_moves_from_active_to_pass:          0
% 1.70/1.00  
% 1.70/1.00  ------ Superposition
% 1.70/1.00  
% 1.70/1.00  sup_time_total:                         0.
% 1.70/1.00  sup_time_generating:                    0.
% 1.70/1.00  sup_time_sim_full:                      0.
% 1.70/1.00  sup_time_sim_immed:                     0.
% 1.70/1.00  
% 1.70/1.00  sup_num_of_clauses:                     23
% 1.70/1.00  sup_num_in_active:                      6
% 1.70/1.00  sup_num_in_passive:                     17
% 1.70/1.00  sup_num_of_loops:                       9
% 1.70/1.00  sup_fw_superposition:                   35
% 1.70/1.00  sup_bw_superposition:                   25
% 1.70/1.00  sup_immediate_simplified:               31
% 1.70/1.00  sup_given_eliminated:                   0
% 1.70/1.00  comparisons_done:                       0
% 1.70/1.00  comparisons_avoided:                    0
% 1.70/1.00  
% 1.70/1.00  ------ Simplifications
% 1.70/1.00  
% 1.70/1.00  
% 1.70/1.00  sim_fw_subset_subsumed:                 0
% 1.70/1.00  sim_bw_subset_subsumed:                 0
% 1.70/1.00  sim_fw_subsumed:                        5
% 1.70/1.00  sim_bw_subsumed:                        0
% 1.70/1.00  sim_fw_subsumption_res:                 0
% 1.70/1.00  sim_bw_subsumption_res:                 0
% 1.70/1.00  sim_tautology_del:                      0
% 1.70/1.00  sim_eq_tautology_del:                   8
% 1.70/1.00  sim_eq_res_simp:                        0
% 1.70/1.00  sim_fw_demodulated:                     21
% 1.70/1.00  sim_bw_demodulated:                     3
% 1.70/1.00  sim_light_normalised:                   12
% 1.70/1.00  sim_joinable_taut:                      0
% 1.70/1.00  sim_joinable_simp:                      0
% 1.70/1.00  sim_ac_normalised:                      0
% 1.70/1.00  sim_smt_subsumption:                    0
% 1.70/1.00  
%------------------------------------------------------------------------------
