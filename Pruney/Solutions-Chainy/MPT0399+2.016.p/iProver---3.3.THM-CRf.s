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
% DateTime   : Thu Dec  3 11:41:56 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of clauses        :   14 (  14 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :   10
%              Number of atoms          :  107 ( 119 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f20])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] : ~ r2_hidden(X3,X1)
            & r2_hidden(X2,X0) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] : r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X1] :
      ( ? [X3] : r2_hidden(X3,X1)
     => r2_hidden(sK2(X1),X1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(sK2(X1),X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f24])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X1),X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f19,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_setfam_1(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK3
      & r1_setfam_1(sK3,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( k1_xboole_0 != sK3
    & r1_setfam_1(sK3,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f26])).

fof(f38,plain,(
    r1_setfam_1(sK3,k1_xboole_0) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f22])).

fof(f31,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f39,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | ~ r1_xboole_0(X2,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_560,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),X0)
    | ~ r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ r1_xboole_0(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_567,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_560])).

cnf(c_8,plain,
    ( ~ r1_setfam_1(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(sK2(X1),X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_11,negated_conjecture,
    ( r1_setfam_1(sK3,k1_xboole_0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_135,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2(X2),X2)
    | sK3 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_11])).

cnf(c_136,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(sK2(k1_xboole_0),k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_135])).

cnf(c_520,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ r2_hidden(sK1(sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_136])).

cnf(c_3,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_493,plain,
    ( r2_hidden(sK1(sK3),sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_27,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_10,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f39])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_567,c_520,c_493,c_27,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:46:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 0.75/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.75/1.06  
% 0.75/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.75/1.06  
% 0.75/1.06  ------  iProver source info
% 0.75/1.06  
% 0.75/1.06  git: date: 2020-06-30 10:37:57 +0100
% 0.75/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.75/1.06  git: non_committed_changes: false
% 0.75/1.06  git: last_make_outside_of_git: false
% 0.75/1.06  
% 0.75/1.06  ------ 
% 0.75/1.06  
% 0.75/1.06  ------ Input Options
% 0.75/1.06  
% 0.75/1.06  --out_options                           all
% 0.75/1.06  --tptp_safe_out                         true
% 0.75/1.06  --problem_path                          ""
% 0.75/1.06  --include_path                          ""
% 0.75/1.06  --clausifier                            res/vclausify_rel
% 0.75/1.06  --clausifier_options                    --mode clausify
% 0.75/1.06  --stdin                                 false
% 0.75/1.06  --stats_out                             all
% 0.75/1.06  
% 0.75/1.06  ------ General Options
% 0.75/1.06  
% 0.75/1.06  --fof                                   false
% 0.75/1.06  --time_out_real                         305.
% 0.75/1.06  --time_out_virtual                      -1.
% 0.75/1.06  --symbol_type_check                     false
% 0.75/1.06  --clausify_out                          false
% 0.75/1.06  --sig_cnt_out                           false
% 0.75/1.06  --trig_cnt_out                          false
% 0.75/1.06  --trig_cnt_out_tolerance                1.
% 0.75/1.06  --trig_cnt_out_sk_spl                   false
% 0.75/1.06  --abstr_cl_out                          false
% 0.75/1.06  
% 0.75/1.06  ------ Global Options
% 0.75/1.06  
% 0.75/1.06  --schedule                              default
% 0.75/1.06  --add_important_lit                     false
% 0.75/1.06  --prop_solver_per_cl                    1000
% 0.75/1.06  --min_unsat_core                        false
% 0.75/1.06  --soft_assumptions                      false
% 0.75/1.06  --soft_lemma_size                       3
% 0.75/1.06  --prop_impl_unit_size                   0
% 0.75/1.06  --prop_impl_unit                        []
% 0.75/1.06  --share_sel_clauses                     true
% 0.75/1.06  --reset_solvers                         false
% 0.75/1.06  --bc_imp_inh                            [conj_cone]
% 0.75/1.06  --conj_cone_tolerance                   3.
% 0.75/1.06  --extra_neg_conj                        none
% 0.75/1.06  --large_theory_mode                     true
% 0.75/1.06  --prolific_symb_bound                   200
% 0.75/1.06  --lt_threshold                          2000
% 0.75/1.06  --clause_weak_htbl                      true
% 0.75/1.06  --gc_record_bc_elim                     false
% 0.75/1.06  
% 0.75/1.06  ------ Preprocessing Options
% 0.75/1.06  
% 0.75/1.06  --preprocessing_flag                    true
% 0.75/1.06  --time_out_prep_mult                    0.1
% 0.75/1.06  --splitting_mode                        input
% 0.75/1.06  --splitting_grd                         true
% 0.75/1.06  --splitting_cvd                         false
% 0.75/1.06  --splitting_cvd_svl                     false
% 0.75/1.06  --splitting_nvd                         32
% 0.75/1.06  --sub_typing                            true
% 0.75/1.06  --prep_gs_sim                           true
% 0.75/1.06  --prep_unflatten                        true
% 0.75/1.06  --prep_res_sim                          true
% 0.75/1.06  --prep_upred                            true
% 0.75/1.06  --prep_sem_filter                       exhaustive
% 0.75/1.06  --prep_sem_filter_out                   false
% 0.75/1.06  --pred_elim                             true
% 0.75/1.06  --res_sim_input                         true
% 0.75/1.06  --eq_ax_congr_red                       true
% 0.75/1.06  --pure_diseq_elim                       true
% 0.75/1.06  --brand_transform                       false
% 0.75/1.06  --non_eq_to_eq                          false
% 0.75/1.06  --prep_def_merge                        true
% 0.75/1.06  --prep_def_merge_prop_impl              false
% 0.75/1.06  --prep_def_merge_mbd                    true
% 0.75/1.06  --prep_def_merge_tr_red                 false
% 0.75/1.06  --prep_def_merge_tr_cl                  false
% 0.75/1.06  --smt_preprocessing                     true
% 0.75/1.06  --smt_ac_axioms                         fast
% 0.75/1.06  --preprocessed_out                      false
% 0.75/1.06  --preprocessed_stats                    false
% 0.75/1.06  
% 0.75/1.06  ------ Abstraction refinement Options
% 0.75/1.06  
% 0.75/1.06  --abstr_ref                             []
% 0.75/1.06  --abstr_ref_prep                        false
% 0.75/1.06  --abstr_ref_until_sat                   false
% 0.75/1.06  --abstr_ref_sig_restrict                funpre
% 0.75/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 0.75/1.06  --abstr_ref_under                       []
% 0.75/1.06  
% 0.75/1.06  ------ SAT Options
% 0.75/1.06  
% 0.75/1.06  --sat_mode                              false
% 0.75/1.06  --sat_fm_restart_options                ""
% 0.75/1.06  --sat_gr_def                            false
% 0.75/1.06  --sat_epr_types                         true
% 0.75/1.06  --sat_non_cyclic_types                  false
% 0.75/1.06  --sat_finite_models                     false
% 0.75/1.06  --sat_fm_lemmas                         false
% 0.75/1.06  --sat_fm_prep                           false
% 0.75/1.06  --sat_fm_uc_incr                        true
% 0.75/1.06  --sat_out_model                         small
% 0.75/1.06  --sat_out_clauses                       false
% 0.75/1.06  
% 0.75/1.06  ------ QBF Options
% 0.75/1.06  
% 0.75/1.06  --qbf_mode                              false
% 0.75/1.06  --qbf_elim_univ                         false
% 0.75/1.06  --qbf_dom_inst                          none
% 0.75/1.06  --qbf_dom_pre_inst                      false
% 0.75/1.06  --qbf_sk_in                             false
% 0.75/1.06  --qbf_pred_elim                         true
% 0.75/1.06  --qbf_split                             512
% 0.75/1.06  
% 0.75/1.06  ------ BMC1 Options
% 0.75/1.06  
% 0.75/1.06  --bmc1_incremental                      false
% 0.75/1.06  --bmc1_axioms                           reachable_all
% 0.75/1.06  --bmc1_min_bound                        0
% 0.75/1.06  --bmc1_max_bound                        -1
% 0.75/1.06  --bmc1_max_bound_default                -1
% 0.75/1.06  --bmc1_symbol_reachability              true
% 0.75/1.06  --bmc1_property_lemmas                  false
% 0.75/1.06  --bmc1_k_induction                      false
% 0.75/1.06  --bmc1_non_equiv_states                 false
% 0.75/1.06  --bmc1_deadlock                         false
% 0.75/1.06  --bmc1_ucm                              false
% 0.75/1.06  --bmc1_add_unsat_core                   none
% 0.75/1.06  --bmc1_unsat_core_children              false
% 0.75/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 0.75/1.06  --bmc1_out_stat                         full
% 0.75/1.06  --bmc1_ground_init                      false
% 0.75/1.06  --bmc1_pre_inst_next_state              false
% 0.75/1.06  --bmc1_pre_inst_state                   false
% 0.75/1.06  --bmc1_pre_inst_reach_state             false
% 0.75/1.06  --bmc1_out_unsat_core                   false
% 0.75/1.06  --bmc1_aig_witness_out                  false
% 0.75/1.06  --bmc1_verbose                          false
% 0.75/1.06  --bmc1_dump_clauses_tptp                false
% 0.75/1.06  --bmc1_dump_unsat_core_tptp             false
% 0.75/1.06  --bmc1_dump_file                        -
% 0.75/1.06  --bmc1_ucm_expand_uc_limit              128
% 0.75/1.06  --bmc1_ucm_n_expand_iterations          6
% 0.75/1.06  --bmc1_ucm_extend_mode                  1
% 0.75/1.06  --bmc1_ucm_init_mode                    2
% 0.75/1.06  --bmc1_ucm_cone_mode                    none
% 0.75/1.06  --bmc1_ucm_reduced_relation_type        0
% 0.75/1.06  --bmc1_ucm_relax_model                  4
% 0.75/1.06  --bmc1_ucm_full_tr_after_sat            true
% 0.75/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 0.75/1.06  --bmc1_ucm_layered_model                none
% 0.75/1.06  --bmc1_ucm_max_lemma_size               10
% 0.75/1.06  
% 0.75/1.06  ------ AIG Options
% 0.75/1.06  
% 0.75/1.06  --aig_mode                              false
% 0.75/1.06  
% 0.75/1.06  ------ Instantiation Options
% 0.75/1.06  
% 0.75/1.06  --instantiation_flag                    true
% 0.75/1.06  --inst_sos_flag                         false
% 0.75/1.06  --inst_sos_phase                        true
% 0.75/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.75/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.75/1.06  --inst_lit_sel_side                     num_symb
% 0.75/1.06  --inst_solver_per_active                1400
% 0.75/1.06  --inst_solver_calls_frac                1.
% 0.75/1.06  --inst_passive_queue_type               priority_queues
% 0.75/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.75/1.06  --inst_passive_queues_freq              [25;2]
% 0.75/1.06  --inst_dismatching                      true
% 0.75/1.06  --inst_eager_unprocessed_to_passive     true
% 0.75/1.06  --inst_prop_sim_given                   true
% 0.75/1.06  --inst_prop_sim_new                     false
% 0.75/1.06  --inst_subs_new                         false
% 0.75/1.06  --inst_eq_res_simp                      false
% 0.75/1.06  --inst_subs_given                       false
% 0.75/1.06  --inst_orphan_elimination               true
% 0.75/1.06  --inst_learning_loop_flag               true
% 0.75/1.06  --inst_learning_start                   3000
% 0.75/1.06  --inst_learning_factor                  2
% 0.75/1.06  --inst_start_prop_sim_after_learn       3
% 0.75/1.06  --inst_sel_renew                        solver
% 0.75/1.06  --inst_lit_activity_flag                true
% 0.75/1.06  --inst_restr_to_given                   false
% 0.75/1.06  --inst_activity_threshold               500
% 0.75/1.06  --inst_out_proof                        true
% 0.75/1.06  
% 0.75/1.06  ------ Resolution Options
% 0.75/1.06  
% 0.75/1.06  --resolution_flag                       true
% 0.75/1.06  --res_lit_sel                           adaptive
% 0.75/1.06  --res_lit_sel_side                      none
% 0.75/1.06  --res_ordering                          kbo
% 0.75/1.06  --res_to_prop_solver                    active
% 0.75/1.06  --res_prop_simpl_new                    false
% 0.75/1.06  --res_prop_simpl_given                  true
% 0.75/1.06  --res_passive_queue_type                priority_queues
% 0.75/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.75/1.06  --res_passive_queues_freq               [15;5]
% 0.75/1.06  --res_forward_subs                      full
% 0.75/1.06  --res_backward_subs                     full
% 0.75/1.06  --res_forward_subs_resolution           true
% 0.75/1.06  --res_backward_subs_resolution          true
% 0.75/1.06  --res_orphan_elimination                true
% 0.75/1.06  --res_time_limit                        2.
% 0.75/1.06  --res_out_proof                         true
% 0.75/1.06  
% 0.75/1.06  ------ Superposition Options
% 0.75/1.06  
% 0.75/1.06  --superposition_flag                    true
% 0.75/1.06  --sup_passive_queue_type                priority_queues
% 0.75/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.75/1.06  --sup_passive_queues_freq               [8;1;4]
% 0.75/1.06  --demod_completeness_check              fast
% 0.75/1.06  --demod_use_ground                      true
% 0.75/1.06  --sup_to_prop_solver                    passive
% 0.75/1.06  --sup_prop_simpl_new                    true
% 0.75/1.06  --sup_prop_simpl_given                  true
% 0.75/1.06  --sup_fun_splitting                     false
% 0.75/1.06  --sup_smt_interval                      50000
% 0.75/1.06  
% 0.75/1.06  ------ Superposition Simplification Setup
% 0.75/1.06  
% 0.75/1.06  --sup_indices_passive                   []
% 0.75/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.75/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.75/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.75/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 0.75/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.75/1.06  --sup_full_bw                           [BwDemod]
% 0.75/1.06  --sup_immed_triv                        [TrivRules]
% 0.75/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.75/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.75/1.06  --sup_immed_bw_main                     []
% 0.75/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.75/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 0.75/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.75/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.75/1.06  
% 0.75/1.06  ------ Combination Options
% 0.75/1.06  
% 0.75/1.06  --comb_res_mult                         3
% 0.75/1.06  --comb_sup_mult                         2
% 0.75/1.06  --comb_inst_mult                        10
% 0.75/1.06  
% 0.75/1.06  ------ Debug Options
% 0.75/1.06  
% 0.75/1.06  --dbg_backtrace                         false
% 0.75/1.06  --dbg_dump_prop_clauses                 false
% 0.75/1.06  --dbg_dump_prop_clauses_file            -
% 0.75/1.06  --dbg_out_stat                          false
% 0.75/1.06  ------ Parsing...
% 0.75/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.75/1.06  
% 0.75/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 0.75/1.06  
% 0.75/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.75/1.06  
% 0.75/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.75/1.06  ------ Proving...
% 0.75/1.06  ------ Problem Properties 
% 0.75/1.06  
% 0.75/1.06  
% 0.75/1.06  clauses                                 9
% 0.75/1.06  conjectures                             1
% 0.75/1.06  EPR                                     3
% 0.75/1.06  Horn                                    6
% 0.75/1.06  unary                                   4
% 0.75/1.06  binary                                  4
% 0.75/1.06  lits                                    15
% 0.75/1.06  lits eq                                 3
% 0.75/1.06  fd_pure                                 0
% 0.75/1.06  fd_pseudo                               0
% 0.75/1.06  fd_cond                                 1
% 0.75/1.06  fd_pseudo_cond                          0
% 0.75/1.06  AC symbols                              0
% 0.75/1.06  
% 0.75/1.06  ------ Schedule dynamic 5 is on 
% 0.75/1.06  
% 0.75/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.75/1.06  
% 0.75/1.06  
% 0.75/1.06  ------ 
% 0.75/1.06  Current options:
% 0.75/1.06  ------ 
% 0.75/1.06  
% 0.75/1.06  ------ Input Options
% 0.75/1.06  
% 0.75/1.06  --out_options                           all
% 0.75/1.06  --tptp_safe_out                         true
% 0.75/1.06  --problem_path                          ""
% 0.75/1.06  --include_path                          ""
% 0.75/1.06  --clausifier                            res/vclausify_rel
% 0.75/1.06  --clausifier_options                    --mode clausify
% 0.75/1.06  --stdin                                 false
% 0.75/1.06  --stats_out                             all
% 0.91/1.06  
% 0.91/1.06  ------ General Options
% 0.91/1.06  
% 0.91/1.06  --fof                                   false
% 0.91/1.06  --time_out_real                         305.
% 0.91/1.06  --time_out_virtual                      -1.
% 0.91/1.06  --symbol_type_check                     false
% 0.91/1.06  --clausify_out                          false
% 0.91/1.06  --sig_cnt_out                           false
% 0.91/1.06  --trig_cnt_out                          false
% 0.91/1.06  --trig_cnt_out_tolerance                1.
% 0.91/1.06  --trig_cnt_out_sk_spl                   false
% 0.91/1.06  --abstr_cl_out                          false
% 0.91/1.06  
% 0.91/1.06  ------ Global Options
% 0.91/1.06  
% 0.91/1.06  --schedule                              default
% 0.91/1.06  --add_important_lit                     false
% 0.91/1.06  --prop_solver_per_cl                    1000
% 0.91/1.06  --min_unsat_core                        false
% 0.91/1.06  --soft_assumptions                      false
% 0.91/1.06  --soft_lemma_size                       3
% 0.91/1.06  --prop_impl_unit_size                   0
% 0.91/1.06  --prop_impl_unit                        []
% 0.91/1.06  --share_sel_clauses                     true
% 0.91/1.06  --reset_solvers                         false
% 0.91/1.06  --bc_imp_inh                            [conj_cone]
% 0.91/1.06  --conj_cone_tolerance                   3.
% 0.91/1.06  --extra_neg_conj                        none
% 0.91/1.06  --large_theory_mode                     true
% 0.91/1.06  --prolific_symb_bound                   200
% 0.91/1.06  --lt_threshold                          2000
% 0.91/1.06  --clause_weak_htbl                      true
% 0.91/1.06  --gc_record_bc_elim                     false
% 0.91/1.06  
% 0.91/1.06  ------ Preprocessing Options
% 0.91/1.06  
% 0.91/1.06  --preprocessing_flag                    true
% 0.91/1.06  --time_out_prep_mult                    0.1
% 0.91/1.06  --splitting_mode                        input
% 0.91/1.06  --splitting_grd                         true
% 0.91/1.06  --splitting_cvd                         false
% 0.91/1.06  --splitting_cvd_svl                     false
% 0.91/1.06  --splitting_nvd                         32
% 0.91/1.06  --sub_typing                            true
% 0.91/1.06  --prep_gs_sim                           true
% 0.91/1.06  --prep_unflatten                        true
% 0.91/1.06  --prep_res_sim                          true
% 0.91/1.06  --prep_upred                            true
% 0.91/1.06  --prep_sem_filter                       exhaustive
% 0.91/1.06  --prep_sem_filter_out                   false
% 0.91/1.06  --pred_elim                             true
% 0.91/1.06  --res_sim_input                         true
% 0.91/1.06  --eq_ax_congr_red                       true
% 0.91/1.06  --pure_diseq_elim                       true
% 0.91/1.06  --brand_transform                       false
% 0.91/1.06  --non_eq_to_eq                          false
% 0.91/1.06  --prep_def_merge                        true
% 0.91/1.06  --prep_def_merge_prop_impl              false
% 0.91/1.06  --prep_def_merge_mbd                    true
% 0.91/1.06  --prep_def_merge_tr_red                 false
% 0.91/1.06  --prep_def_merge_tr_cl                  false
% 0.91/1.06  --smt_preprocessing                     true
% 0.91/1.06  --smt_ac_axioms                         fast
% 0.91/1.06  --preprocessed_out                      false
% 0.91/1.06  --preprocessed_stats                    false
% 0.91/1.06  
% 0.91/1.06  ------ Abstraction refinement Options
% 0.91/1.06  
% 0.91/1.06  --abstr_ref                             []
% 0.91/1.06  --abstr_ref_prep                        false
% 0.91/1.06  --abstr_ref_until_sat                   false
% 0.91/1.06  --abstr_ref_sig_restrict                funpre
% 0.91/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 0.91/1.06  --abstr_ref_under                       []
% 0.91/1.06  
% 0.91/1.06  ------ SAT Options
% 0.91/1.06  
% 0.91/1.06  --sat_mode                              false
% 0.91/1.06  --sat_fm_restart_options                ""
% 0.91/1.06  --sat_gr_def                            false
% 0.91/1.06  --sat_epr_types                         true
% 0.91/1.06  --sat_non_cyclic_types                  false
% 0.91/1.06  --sat_finite_models                     false
% 0.91/1.06  --sat_fm_lemmas                         false
% 0.91/1.06  --sat_fm_prep                           false
% 0.91/1.06  --sat_fm_uc_incr                        true
% 0.91/1.06  --sat_out_model                         small
% 0.91/1.06  --sat_out_clauses                       false
% 0.91/1.06  
% 0.91/1.06  ------ QBF Options
% 0.91/1.06  
% 0.91/1.06  --qbf_mode                              false
% 0.91/1.06  --qbf_elim_univ                         false
% 0.91/1.06  --qbf_dom_inst                          none
% 0.91/1.06  --qbf_dom_pre_inst                      false
% 0.91/1.06  --qbf_sk_in                             false
% 0.91/1.06  --qbf_pred_elim                         true
% 0.91/1.06  --qbf_split                             512
% 0.91/1.06  
% 0.91/1.06  ------ BMC1 Options
% 0.91/1.06  
% 0.91/1.06  --bmc1_incremental                      false
% 0.91/1.06  --bmc1_axioms                           reachable_all
% 0.91/1.06  --bmc1_min_bound                        0
% 0.91/1.06  --bmc1_max_bound                        -1
% 0.91/1.06  --bmc1_max_bound_default                -1
% 0.91/1.06  --bmc1_symbol_reachability              true
% 0.91/1.06  --bmc1_property_lemmas                  false
% 0.91/1.06  --bmc1_k_induction                      false
% 0.91/1.06  --bmc1_non_equiv_states                 false
% 0.91/1.06  --bmc1_deadlock                         false
% 0.91/1.06  --bmc1_ucm                              false
% 0.91/1.06  --bmc1_add_unsat_core                   none
% 0.91/1.06  --bmc1_unsat_core_children              false
% 0.91/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 0.91/1.06  --bmc1_out_stat                         full
% 0.91/1.06  --bmc1_ground_init                      false
% 0.91/1.06  --bmc1_pre_inst_next_state              false
% 0.91/1.06  --bmc1_pre_inst_state                   false
% 0.91/1.06  --bmc1_pre_inst_reach_state             false
% 0.91/1.06  --bmc1_out_unsat_core                   false
% 0.91/1.06  --bmc1_aig_witness_out                  false
% 0.91/1.06  --bmc1_verbose                          false
% 0.91/1.06  --bmc1_dump_clauses_tptp                false
% 0.91/1.06  --bmc1_dump_unsat_core_tptp             false
% 0.91/1.06  --bmc1_dump_file                        -
% 0.91/1.06  --bmc1_ucm_expand_uc_limit              128
% 0.91/1.06  --bmc1_ucm_n_expand_iterations          6
% 0.91/1.06  --bmc1_ucm_extend_mode                  1
% 0.91/1.06  --bmc1_ucm_init_mode                    2
% 0.91/1.06  --bmc1_ucm_cone_mode                    none
% 0.91/1.06  --bmc1_ucm_reduced_relation_type        0
% 0.91/1.06  --bmc1_ucm_relax_model                  4
% 0.91/1.06  --bmc1_ucm_full_tr_after_sat            true
% 0.91/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 0.91/1.06  --bmc1_ucm_layered_model                none
% 0.91/1.06  --bmc1_ucm_max_lemma_size               10
% 0.91/1.06  
% 0.91/1.06  ------ AIG Options
% 0.91/1.06  
% 0.91/1.06  --aig_mode                              false
% 0.91/1.06  
% 0.91/1.06  ------ Instantiation Options
% 0.91/1.06  
% 0.91/1.06  --instantiation_flag                    true
% 0.91/1.06  --inst_sos_flag                         false
% 0.91/1.06  --inst_sos_phase                        true
% 0.91/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.91/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.91/1.06  --inst_lit_sel_side                     none
% 0.91/1.06  --inst_solver_per_active                1400
% 0.91/1.06  --inst_solver_calls_frac                1.
% 0.91/1.06  --inst_passive_queue_type               priority_queues
% 0.91/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.91/1.06  --inst_passive_queues_freq              [25;2]
% 0.91/1.06  --inst_dismatching                      true
% 0.91/1.06  --inst_eager_unprocessed_to_passive     true
% 0.91/1.06  --inst_prop_sim_given                   true
% 0.91/1.06  --inst_prop_sim_new                     false
% 0.91/1.06  --inst_subs_new                         false
% 0.91/1.06  --inst_eq_res_simp                      false
% 0.91/1.06  --inst_subs_given                       false
% 0.91/1.06  --inst_orphan_elimination               true
% 0.91/1.06  --inst_learning_loop_flag               true
% 0.91/1.06  --inst_learning_start                   3000
% 0.91/1.06  --inst_learning_factor                  2
% 0.91/1.06  --inst_start_prop_sim_after_learn       3
% 0.91/1.06  --inst_sel_renew                        solver
% 0.91/1.06  --inst_lit_activity_flag                true
% 0.91/1.06  --inst_restr_to_given                   false
% 0.91/1.06  --inst_activity_threshold               500
% 0.91/1.06  --inst_out_proof                        true
% 0.91/1.06  
% 0.91/1.06  ------ Resolution Options
% 0.91/1.06  
% 0.91/1.06  --resolution_flag                       false
% 0.91/1.06  --res_lit_sel                           adaptive
% 0.91/1.06  --res_lit_sel_side                      none
% 0.91/1.06  --res_ordering                          kbo
% 0.91/1.06  --res_to_prop_solver                    active
% 0.91/1.06  --res_prop_simpl_new                    false
% 0.91/1.06  --res_prop_simpl_given                  true
% 0.91/1.06  --res_passive_queue_type                priority_queues
% 0.91/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.91/1.06  --res_passive_queues_freq               [15;5]
% 0.91/1.06  --res_forward_subs                      full
% 0.91/1.06  --res_backward_subs                     full
% 0.91/1.06  --res_forward_subs_resolution           true
% 0.91/1.06  --res_backward_subs_resolution          true
% 0.91/1.06  --res_orphan_elimination                true
% 0.91/1.06  --res_time_limit                        2.
% 0.91/1.06  --res_out_proof                         true
% 0.91/1.06  
% 0.91/1.06  ------ Superposition Options
% 0.91/1.06  
% 0.91/1.06  --superposition_flag                    true
% 0.91/1.06  --sup_passive_queue_type                priority_queues
% 0.91/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.91/1.06  --sup_passive_queues_freq               [8;1;4]
% 0.91/1.06  --demod_completeness_check              fast
% 0.91/1.06  --demod_use_ground                      true
% 0.91/1.06  --sup_to_prop_solver                    passive
% 0.91/1.06  --sup_prop_simpl_new                    true
% 0.91/1.06  --sup_prop_simpl_given                  true
% 0.91/1.06  --sup_fun_splitting                     false
% 0.91/1.06  --sup_smt_interval                      50000
% 0.91/1.06  
% 0.91/1.06  ------ Superposition Simplification Setup
% 0.91/1.06  
% 0.91/1.06  --sup_indices_passive                   []
% 0.91/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.91/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.91/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.91/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 0.91/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.91/1.06  --sup_full_bw                           [BwDemod]
% 0.91/1.06  --sup_immed_triv                        [TrivRules]
% 0.91/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.91/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.91/1.06  --sup_immed_bw_main                     []
% 0.91/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.91/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 0.91/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.91/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.91/1.06  
% 0.91/1.06  ------ Combination Options
% 0.91/1.06  
% 0.91/1.06  --comb_res_mult                         3
% 0.91/1.06  --comb_sup_mult                         2
% 0.91/1.06  --comb_inst_mult                        10
% 0.91/1.06  
% 0.91/1.06  ------ Debug Options
% 0.91/1.06  
% 0.91/1.06  --dbg_backtrace                         false
% 0.91/1.06  --dbg_dump_prop_clauses                 false
% 0.91/1.06  --dbg_dump_prop_clauses_file            -
% 0.91/1.06  --dbg_out_stat                          false
% 0.91/1.06  
% 0.91/1.06  
% 0.91/1.06  
% 0.91/1.06  
% 0.91/1.06  ------ Proving...
% 0.91/1.06  
% 0.91/1.06  
% 0.91/1.06  % SZS status Theorem for theBenchmark.p
% 0.91/1.06  
% 0.91/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 0.91/1.06  
% 0.91/1.06  fof(f1,axiom,(
% 0.91/1.06    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.91/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.06  
% 0.91/1.06  fof(f11,plain,(
% 0.91/1.06    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.91/1.06    inference(rectify,[],[f1])).
% 0.91/1.06  
% 0.91/1.06  fof(f14,plain,(
% 0.91/1.06    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.91/1.06    inference(ennf_transformation,[],[f11])).
% 0.91/1.06  
% 0.91/1.06  fof(f20,plain,(
% 0.91/1.06    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 0.91/1.06    introduced(choice_axiom,[])).
% 0.91/1.06  
% 0.91/1.06  fof(f21,plain,(
% 0.91/1.06    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.91/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f20])).
% 0.91/1.06  
% 0.91/1.06  fof(f30,plain,(
% 0.91/1.06    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.91/1.06    inference(cnf_transformation,[],[f21])).
% 0.91/1.06  
% 0.91/1.06  fof(f7,axiom,(
% 0.91/1.06    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.91/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.06  
% 0.91/1.06  fof(f12,plain,(
% 0.91/1.06    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.91/1.06    inference(unused_predicate_definition_removal,[],[f7])).
% 0.91/1.06  
% 0.91/1.06  fof(f13,plain,(
% 0.91/1.06    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~r2_hidden(X3,X1) & r2_hidden(X2,X0)))),
% 0.91/1.06    inference(pure_predicate_removal,[],[f12])).
% 0.91/1.06  
% 0.91/1.06  fof(f16,plain,(
% 0.91/1.06    ! [X0,X1] : (! [X2] : (? [X3] : r2_hidden(X3,X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.91/1.06    inference(ennf_transformation,[],[f13])).
% 0.91/1.06  
% 0.91/1.06  fof(f24,plain,(
% 0.91/1.06    ! [X1] : (? [X3] : r2_hidden(X3,X1) => r2_hidden(sK2(X1),X1))),
% 0.91/1.06    introduced(choice_axiom,[])).
% 0.91/1.06  
% 0.91/1.06  fof(f25,plain,(
% 0.91/1.06    ! [X0,X1] : (! [X2] : (r2_hidden(sK2(X1),X1) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.91/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f24])).
% 0.91/1.06  
% 0.91/1.06  fof(f36,plain,(
% 0.91/1.06    ( ! [X2,X0,X1] : (r2_hidden(sK2(X1),X1) | ~r2_hidden(X2,X0) | ~r1_setfam_1(X0,X1)) )),
% 0.91/1.06    inference(cnf_transformation,[],[f25])).
% 0.91/1.06  
% 0.91/1.06  fof(f9,conjecture,(
% 0.91/1.06    ! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.91/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.06  
% 0.91/1.06  fof(f10,negated_conjecture,(
% 0.91/1.06    ~! [X0] : (r1_setfam_1(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.91/1.06    inference(negated_conjecture,[],[f9])).
% 0.91/1.06  
% 0.91/1.06  fof(f19,plain,(
% 0.91/1.06    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0))),
% 0.91/1.06    inference(ennf_transformation,[],[f10])).
% 0.91/1.06  
% 0.91/1.06  fof(f26,plain,(
% 0.91/1.06    ? [X0] : (k1_xboole_0 != X0 & r1_setfam_1(X0,k1_xboole_0)) => (k1_xboole_0 != sK3 & r1_setfam_1(sK3,k1_xboole_0))),
% 0.91/1.06    introduced(choice_axiom,[])).
% 0.91/1.06  
% 0.91/1.06  fof(f27,plain,(
% 0.91/1.06    k1_xboole_0 != sK3 & r1_setfam_1(sK3,k1_xboole_0)),
% 0.91/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f26])).
% 0.91/1.06  
% 0.91/1.06  fof(f38,plain,(
% 0.91/1.06    r1_setfam_1(sK3,k1_xboole_0)),
% 0.91/1.06    inference(cnf_transformation,[],[f27])).
% 0.91/1.06  
% 0.91/1.06  fof(f2,axiom,(
% 0.91/1.06    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.91/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.06  
% 0.91/1.06  fof(f15,plain,(
% 0.91/1.06    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.91/1.06    inference(ennf_transformation,[],[f2])).
% 0.91/1.06  
% 0.91/1.06  fof(f22,plain,(
% 0.91/1.06    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.91/1.06    introduced(choice_axiom,[])).
% 0.91/1.06  
% 0.91/1.06  fof(f23,plain,(
% 0.91/1.06    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 0.91/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f15,f22])).
% 0.91/1.06  
% 0.91/1.06  fof(f31,plain,(
% 0.91/1.06    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 0.91/1.06    inference(cnf_transformation,[],[f23])).
% 0.91/1.06  
% 0.91/1.06  fof(f3,axiom,(
% 0.91/1.06    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.91/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/1.06  
% 0.91/1.06  fof(f32,plain,(
% 0.91/1.06    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.91/1.06    inference(cnf_transformation,[],[f3])).
% 0.91/1.06  
% 0.91/1.06  fof(f39,plain,(
% 0.91/1.06    k1_xboole_0 != sK3),
% 0.91/1.06    inference(cnf_transformation,[],[f27])).
% 0.91/1.06  
% 0.91/1.06  cnf(c_0,plain,
% 0.91/1.06      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,X2) | ~ r1_xboole_0(X2,X1) ),
% 0.91/1.06      inference(cnf_transformation,[],[f30]) ).
% 0.91/1.06  
% 0.91/1.06  cnf(c_560,plain,
% 0.91/1.06      ( ~ r2_hidden(sK2(k1_xboole_0),X0)
% 0.91/1.06      | ~ r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
% 0.91/1.06      | ~ r1_xboole_0(X0,k1_xboole_0) ),
% 0.91/1.06      inference(instantiation,[status(thm)],[c_0]) ).
% 0.91/1.06  
% 0.91/1.06  cnf(c_567,plain,
% 0.91/1.06      ( ~ r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
% 0.91/1.06      | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 0.91/1.06      inference(instantiation,[status(thm)],[c_560]) ).
% 0.91/1.06  
% 0.91/1.06  cnf(c_8,plain,
% 0.91/1.06      ( ~ r1_setfam_1(X0,X1)
% 0.91/1.06      | ~ r2_hidden(X2,X0)
% 0.91/1.06      | r2_hidden(sK2(X1),X1) ),
% 0.91/1.06      inference(cnf_transformation,[],[f36]) ).
% 0.91/1.06  
% 0.91/1.06  cnf(c_11,negated_conjecture,
% 0.91/1.06      ( r1_setfam_1(sK3,k1_xboole_0) ),
% 0.91/1.06      inference(cnf_transformation,[],[f38]) ).
% 0.91/1.06  
% 0.91/1.06  cnf(c_135,plain,
% 0.91/1.06      ( ~ r2_hidden(X0,X1)
% 0.91/1.06      | r2_hidden(sK2(X2),X2)
% 0.91/1.06      | sK3 != X1
% 0.91/1.06      | k1_xboole_0 != X2 ),
% 0.91/1.06      inference(resolution_lifted,[status(thm)],[c_8,c_11]) ).
% 0.91/1.06  
% 0.91/1.06  cnf(c_136,plain,
% 0.91/1.06      ( ~ r2_hidden(X0,sK3) | r2_hidden(sK2(k1_xboole_0),k1_xboole_0) ),
% 0.91/1.06      inference(unflattening,[status(thm)],[c_135]) ).
% 0.91/1.06  
% 0.91/1.06  cnf(c_520,plain,
% 0.91/1.06      ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
% 0.91/1.06      | ~ r2_hidden(sK1(sK3),sK3) ),
% 0.91/1.06      inference(instantiation,[status(thm)],[c_136]) ).
% 0.91/1.06  
% 0.91/1.06  cnf(c_3,plain,
% 0.91/1.06      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 0.91/1.06      inference(cnf_transformation,[],[f31]) ).
% 0.91/1.06  
% 0.91/1.06  cnf(c_493,plain,
% 0.91/1.06      ( r2_hidden(sK1(sK3),sK3) | k1_xboole_0 = sK3 ),
% 0.91/1.06      inference(instantiation,[status(thm)],[c_3]) ).
% 0.91/1.06  
% 0.91/1.06  cnf(c_4,plain,
% 0.91/1.06      ( r1_xboole_0(X0,k1_xboole_0) ),
% 0.91/1.06      inference(cnf_transformation,[],[f32]) ).
% 0.91/1.06  
% 0.91/1.06  cnf(c_27,plain,
% 0.91/1.06      ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 0.91/1.06      inference(instantiation,[status(thm)],[c_4]) ).
% 0.91/1.06  
% 0.91/1.06  cnf(c_10,negated_conjecture,
% 0.91/1.06      ( k1_xboole_0 != sK3 ),
% 0.91/1.06      inference(cnf_transformation,[],[f39]) ).
% 0.91/1.06  
% 0.91/1.06  cnf(contradiction,plain,
% 0.91/1.06      ( $false ),
% 0.91/1.06      inference(minisat,[status(thm)],[c_567,c_520,c_493,c_27,c_10]) ).
% 0.91/1.06  
% 0.91/1.06  
% 0.91/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 0.91/1.06  
% 0.91/1.06  ------                               Statistics
% 0.91/1.06  
% 0.91/1.06  ------ General
% 0.91/1.06  
% 0.91/1.06  abstr_ref_over_cycles:                  0
% 0.91/1.06  abstr_ref_under_cycles:                 0
% 0.91/1.06  gc_basic_clause_elim:                   0
% 0.91/1.06  forced_gc_time:                         0
% 0.91/1.06  parsing_time:                           0.018
% 0.91/1.06  unif_index_cands_time:                  0.
% 0.91/1.06  unif_index_add_time:                    0.
% 0.91/1.06  orderings_time:                         0.
% 0.91/1.06  out_proof_time:                         0.02
% 0.91/1.06  total_time:                             0.075
% 0.91/1.06  num_of_symbols:                         43
% 0.91/1.06  num_of_terms:                           438
% 0.91/1.06  
% 0.91/1.06  ------ Preprocessing
% 0.91/1.06  
% 0.91/1.06  num_of_splits:                          0
% 0.91/1.06  num_of_split_atoms:                     0
% 0.91/1.06  num_of_reused_defs:                     0
% 0.91/1.06  num_eq_ax_congr_red:                    20
% 0.91/1.06  num_of_sem_filtered_clauses:            1
% 0.91/1.06  num_of_subtypes:                        0
% 0.91/1.06  monotx_restored_types:                  0
% 0.91/1.06  sat_num_of_epr_types:                   0
% 0.91/1.06  sat_num_of_non_cyclic_types:            0
% 0.91/1.06  sat_guarded_non_collapsed_types:        0
% 0.91/1.06  num_pure_diseq_elim:                    0
% 0.91/1.06  simp_replaced_by:                       0
% 0.91/1.06  res_preprocessed:                       50
% 0.91/1.06  prep_upred:                             0
% 0.91/1.06  prep_unflattend:                        16
% 0.91/1.06  smt_new_axioms:                         0
% 0.91/1.06  pred_elim_cands:                        2
% 0.91/1.06  pred_elim:                              3
% 0.91/1.06  pred_elim_cl:                           3
% 0.91/1.06  pred_elim_cycles:                       5
% 0.91/1.06  merged_defs:                            0
% 0.91/1.06  merged_defs_ncl:                        0
% 0.91/1.06  bin_hyper_res:                          0
% 0.91/1.06  prep_cycles:                            4
% 0.91/1.06  pred_elim_time:                         0.001
% 0.91/1.06  splitting_time:                         0.
% 0.91/1.06  sem_filter_time:                        0.
% 0.91/1.06  monotx_time:                            0.
% 0.91/1.06  subtype_inf_time:                       0.
% 0.91/1.06  
% 0.91/1.06  ------ Problem properties
% 0.91/1.06  
% 0.91/1.06  clauses:                                9
% 0.91/1.06  conjectures:                            1
% 0.91/1.06  epr:                                    3
% 0.91/1.06  horn:                                   6
% 0.91/1.06  ground:                                 1
% 0.91/1.06  unary:                                  4
% 0.91/1.06  binary:                                 4
% 0.91/1.06  lits:                                   15
% 0.91/1.06  lits_eq:                                3
% 0.91/1.06  fd_pure:                                0
% 0.91/1.06  fd_pseudo:                              0
% 0.91/1.06  fd_cond:                                1
% 0.91/1.06  fd_pseudo_cond:                         0
% 0.91/1.06  ac_symbols:                             0
% 0.91/1.06  
% 0.91/1.06  ------ Propositional Solver
% 0.91/1.06  
% 0.91/1.06  prop_solver_calls:                      24
% 0.91/1.06  prop_fast_solver_calls:                 210
% 0.91/1.06  smt_solver_calls:                       0
% 0.91/1.06  smt_fast_solver_calls:                  0
% 0.91/1.06  prop_num_of_clauses:                    122
% 0.91/1.06  prop_preprocess_simplified:             1406
% 0.91/1.06  prop_fo_subsumed:                       1
% 0.91/1.06  prop_solver_time:                       0.
% 0.91/1.06  smt_solver_time:                        0.
% 0.91/1.06  smt_fast_solver_time:                   0.
% 0.91/1.06  prop_fast_solver_time:                  0.
% 0.91/1.06  prop_unsat_core_time:                   0.
% 0.91/1.06  
% 0.91/1.06  ------ QBF
% 0.91/1.06  
% 0.91/1.06  qbf_q_res:                              0
% 0.91/1.06  qbf_num_tautologies:                    0
% 0.91/1.06  qbf_prep_cycles:                        0
% 0.91/1.06  
% 0.91/1.06  ------ BMC1
% 0.91/1.06  
% 0.91/1.06  bmc1_current_bound:                     -1
% 0.91/1.06  bmc1_last_solved_bound:                 -1
% 0.91/1.06  bmc1_unsat_core_size:                   -1
% 0.91/1.06  bmc1_unsat_core_parents_size:           -1
% 0.91/1.06  bmc1_merge_next_fun:                    0
% 0.91/1.06  bmc1_unsat_core_clauses_time:           0.
% 0.91/1.06  
% 0.91/1.06  ------ Instantiation
% 0.91/1.06  
% 0.91/1.06  inst_num_of_clauses:                    31
% 0.91/1.06  inst_num_in_passive:                    11
% 0.91/1.06  inst_num_in_active:                     18
% 0.91/1.06  inst_num_in_unprocessed:                1
% 0.91/1.06  inst_num_of_loops:                      20
% 0.91/1.06  inst_num_of_learning_restarts:          0
% 0.91/1.06  inst_num_moves_active_passive:          0
% 0.91/1.06  inst_lit_activity:                      0
% 0.91/1.06  inst_lit_activity_moves:                0
% 0.91/1.06  inst_num_tautologies:                   0
% 0.91/1.06  inst_num_prop_implied:                  0
% 0.91/1.06  inst_num_existing_simplified:           0
% 0.91/1.06  inst_num_eq_res_simplified:             0
% 0.91/1.06  inst_num_child_elim:                    0
% 0.91/1.06  inst_num_of_dismatching_blockings:      0
% 0.91/1.06  inst_num_of_non_proper_insts:           10
% 0.91/1.06  inst_num_of_duplicates:                 0
% 0.91/1.06  inst_inst_num_from_inst_to_res:         0
% 0.91/1.06  inst_dismatching_checking_time:         0.
% 0.91/1.06  
% 0.91/1.06  ------ Resolution
% 0.91/1.06  
% 0.91/1.06  res_num_of_clauses:                     0
% 0.91/1.06  res_num_in_passive:                     0
% 0.91/1.06  res_num_in_active:                      0
% 0.91/1.06  res_num_of_loops:                       54
% 0.91/1.06  res_forward_subset_subsumed:            1
% 0.91/1.06  res_backward_subset_subsumed:           0
% 0.91/1.06  res_forward_subsumed:                   0
% 0.91/1.06  res_backward_subsumed:                  0
% 0.91/1.06  res_forward_subsumption_resolution:     0
% 0.91/1.06  res_backward_subsumption_resolution:    0
% 0.91/1.06  res_clause_to_clause_subsumption:       17
% 0.91/1.06  res_orphan_elimination:                 0
% 0.91/1.06  res_tautology_del:                      0
% 0.91/1.06  res_num_eq_res_simplified:              0
% 0.91/1.06  res_num_sel_changes:                    0
% 0.91/1.06  res_moves_from_active_to_pass:          0
% 0.91/1.06  
% 0.91/1.06  ------ Superposition
% 0.91/1.06  
% 0.91/1.06  sup_time_total:                         0.
% 0.91/1.06  sup_time_generating:                    0.
% 0.91/1.06  sup_time_sim_full:                      0.
% 0.91/1.06  sup_time_sim_immed:                     0.
% 0.91/1.06  
% 0.91/1.06  sup_num_of_clauses:                     9
% 0.91/1.06  sup_num_in_active:                      2
% 0.91/1.06  sup_num_in_passive:                     7
% 0.91/1.06  sup_num_of_loops:                       2
% 0.91/1.06  sup_fw_superposition:                   0
% 0.91/1.06  sup_bw_superposition:                   0
% 0.91/1.06  sup_immediate_simplified:               0
% 0.91/1.06  sup_given_eliminated:                   0
% 0.91/1.06  comparisons_done:                       0
% 0.91/1.06  comparisons_avoided:                    0
% 0.91/1.06  
% 0.91/1.06  ------ Simplifications
% 0.91/1.06  
% 0.91/1.06  
% 0.91/1.06  sim_fw_subset_subsumed:                 0
% 0.91/1.06  sim_bw_subset_subsumed:                 0
% 0.91/1.06  sim_fw_subsumed:                        0
% 0.91/1.06  sim_bw_subsumed:                        0
% 0.91/1.06  sim_fw_subsumption_res:                 0
% 0.91/1.06  sim_bw_subsumption_res:                 0
% 0.91/1.06  sim_tautology_del:                      0
% 0.91/1.06  sim_eq_tautology_del:                   0
% 0.91/1.06  sim_eq_res_simp:                        0
% 0.91/1.06  sim_fw_demodulated:                     0
% 0.91/1.06  sim_bw_demodulated:                     0
% 0.91/1.06  sim_light_normalised:                   1
% 0.91/1.06  sim_joinable_taut:                      0
% 0.91/1.06  sim_joinable_simp:                      0
% 0.91/1.06  sim_ac_normalised:                      0
% 0.91/1.06  sim_smt_subsumption:                    0
% 0.91/1.06  
%------------------------------------------------------------------------------
