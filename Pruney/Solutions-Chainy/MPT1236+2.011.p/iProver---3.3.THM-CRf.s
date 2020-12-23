%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:45 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   45 (  57 expanded)
%              Number of clauses        :   24 (  25 expanded)
%              Number of leaves         :    8 (  12 expanded)
%              Depth                    :   12
%              Number of atoms          :   90 ( 116 expanded)
%              Number of equality atoms :   43 (  55 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    5 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f14,plain,(
    ? [X0] :
      ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,
    ( ? [X0] :
        ( k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0))
        & l1_pre_topc(X0) )
   => ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f23,plain,(
    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_1,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_77,plain,
    ( r1_tarski(k1_tops_1(X0,X1),X1)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(X2)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_4])).

cnf(c_78,plain,
    ( r1_tarski(k1_tops_1(X0,k1_xboole_0),k1_xboole_0)
    | ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(X1) ),
    inference(unflattening,[status(thm)],[c_77])).

cnf(c_110,plain,
    ( ~ l1_pre_topc(X0)
    | k1_tops_1(X0,k1_xboole_0) != X1
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(X2)
    | k1_xboole_0 = X1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_78])).

cnf(c_111,plain,
    ( ~ l1_pre_topc(X0)
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(X1)
    | k1_xboole_0 = k1_tops_1(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_110])).

cnf(c_6,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_129,plain,
    ( k1_tops_1(X0,k1_xboole_0) = k1_xboole_0
    | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(X1)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_111,c_6])).

cnf(c_130,plain,
    ( k1_tops_1(sK0,k1_xboole_0) = k1_xboole_0
    | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_129])).

cnf(c_153,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_41)
    | k1_tops_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_130])).

cnf(c_175,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
    | k1_tops_1(sK0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_153])).

cnf(c_156,plain,
    ( X0_40 = X0_40 ),
    theory(equality)).

cnf(c_174,plain,
    ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_156])).

cnf(c_5,negated_conjecture,
    ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_154,negated_conjecture,
    ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_2,plain,
    ( ~ l1_struct_0(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_96,plain,
    ( ~ l1_pre_topc(X0)
    | k1_struct_0(X0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3,c_2])).

cnf(c_138,plain,
    ( k1_struct_0(X0) = k1_xboole_0
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_96,c_6])).

cnf(c_139,plain,
    ( k1_struct_0(sK0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_138])).

cnf(c_152,plain,
    ( k1_struct_0(sK0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_139])).

cnf(c_166,plain,
    ( k1_tops_1(sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_154,c_152])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_175,c_174,c_166])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:50:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 0.59/0.94  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.59/0.94  
% 0.59/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.59/0.94  
% 0.59/0.94  ------  iProver source info
% 0.59/0.94  
% 0.59/0.94  git: date: 2020-06-30 10:37:57 +0100
% 0.59/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.59/0.94  git: non_committed_changes: false
% 0.59/0.94  git: last_make_outside_of_git: false
% 0.59/0.94  
% 0.59/0.94  ------ 
% 0.59/0.94  
% 0.59/0.94  ------ Input Options
% 0.59/0.94  
% 0.59/0.94  --out_options                           all
% 0.59/0.94  --tptp_safe_out                         true
% 0.59/0.94  --problem_path                          ""
% 0.59/0.94  --include_path                          ""
% 0.59/0.94  --clausifier                            res/vclausify_rel
% 0.59/0.94  --clausifier_options                    --mode clausify
% 0.59/0.94  --stdin                                 false
% 0.59/0.94  --stats_out                             all
% 0.59/0.94  
% 0.59/0.94  ------ General Options
% 0.59/0.94  
% 0.59/0.94  --fof                                   false
% 0.59/0.94  --time_out_real                         305.
% 0.59/0.94  --time_out_virtual                      -1.
% 0.59/0.94  --symbol_type_check                     false
% 0.59/0.94  --clausify_out                          false
% 0.59/0.94  --sig_cnt_out                           false
% 0.59/0.94  --trig_cnt_out                          false
% 0.59/0.94  --trig_cnt_out_tolerance                1.
% 0.59/0.94  --trig_cnt_out_sk_spl                   false
% 0.59/0.94  --abstr_cl_out                          false
% 0.59/0.94  
% 0.59/0.94  ------ Global Options
% 0.59/0.94  
% 0.59/0.94  --schedule                              default
% 0.59/0.94  --add_important_lit                     false
% 0.59/0.94  --prop_solver_per_cl                    1000
% 0.59/0.94  --min_unsat_core                        false
% 0.59/0.94  --soft_assumptions                      false
% 0.59/0.94  --soft_lemma_size                       3
% 0.59/0.94  --prop_impl_unit_size                   0
% 0.59/0.94  --prop_impl_unit                        []
% 0.59/0.94  --share_sel_clauses                     true
% 0.59/0.94  --reset_solvers                         false
% 0.59/0.94  --bc_imp_inh                            [conj_cone]
% 0.59/0.94  --conj_cone_tolerance                   3.
% 0.59/0.94  --extra_neg_conj                        none
% 0.59/0.94  --large_theory_mode                     true
% 0.59/0.94  --prolific_symb_bound                   200
% 0.59/0.94  --lt_threshold                          2000
% 0.59/0.94  --clause_weak_htbl                      true
% 0.59/0.94  --gc_record_bc_elim                     false
% 0.59/0.94  
% 0.59/0.94  ------ Preprocessing Options
% 0.59/0.94  
% 0.59/0.94  --preprocessing_flag                    true
% 0.59/0.94  --time_out_prep_mult                    0.1
% 0.59/0.94  --splitting_mode                        input
% 0.59/0.94  --splitting_grd                         true
% 0.59/0.94  --splitting_cvd                         false
% 0.59/0.94  --splitting_cvd_svl                     false
% 0.59/0.94  --splitting_nvd                         32
% 0.59/0.94  --sub_typing                            true
% 0.59/0.94  --prep_gs_sim                           true
% 0.59/0.94  --prep_unflatten                        true
% 0.59/0.94  --prep_res_sim                          true
% 0.59/0.94  --prep_upred                            true
% 0.59/0.94  --prep_sem_filter                       exhaustive
% 0.59/0.94  --prep_sem_filter_out                   false
% 0.59/0.94  --pred_elim                             true
% 0.59/0.94  --res_sim_input                         true
% 0.59/0.94  --eq_ax_congr_red                       true
% 0.59/0.94  --pure_diseq_elim                       true
% 0.59/0.94  --brand_transform                       false
% 0.59/0.94  --non_eq_to_eq                          false
% 0.59/0.94  --prep_def_merge                        true
% 0.59/0.94  --prep_def_merge_prop_impl              false
% 0.59/0.94  --prep_def_merge_mbd                    true
% 0.59/0.94  --prep_def_merge_tr_red                 false
% 0.59/0.94  --prep_def_merge_tr_cl                  false
% 0.59/0.94  --smt_preprocessing                     true
% 0.59/0.94  --smt_ac_axioms                         fast
% 0.59/0.94  --preprocessed_out                      false
% 0.59/0.94  --preprocessed_stats                    false
% 0.59/0.94  
% 0.59/0.94  ------ Abstraction refinement Options
% 0.59/0.94  
% 0.59/0.94  --abstr_ref                             []
% 0.59/0.94  --abstr_ref_prep                        false
% 0.59/0.94  --abstr_ref_until_sat                   false
% 0.59/0.94  --abstr_ref_sig_restrict                funpre
% 0.59/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 0.59/0.94  --abstr_ref_under                       []
% 0.59/0.94  
% 0.59/0.94  ------ SAT Options
% 0.59/0.94  
% 0.59/0.94  --sat_mode                              false
% 0.59/0.94  --sat_fm_restart_options                ""
% 0.59/0.94  --sat_gr_def                            false
% 0.59/0.94  --sat_epr_types                         true
% 0.59/0.94  --sat_non_cyclic_types                  false
% 0.59/0.94  --sat_finite_models                     false
% 0.59/0.94  --sat_fm_lemmas                         false
% 0.59/0.94  --sat_fm_prep                           false
% 0.59/0.94  --sat_fm_uc_incr                        true
% 0.59/0.94  --sat_out_model                         small
% 0.59/0.94  --sat_out_clauses                       false
% 0.59/0.94  
% 0.59/0.94  ------ QBF Options
% 0.59/0.94  
% 0.59/0.94  --qbf_mode                              false
% 0.59/0.94  --qbf_elim_univ                         false
% 0.59/0.94  --qbf_dom_inst                          none
% 0.59/0.94  --qbf_dom_pre_inst                      false
% 0.59/0.94  --qbf_sk_in                             false
% 0.59/0.94  --qbf_pred_elim                         true
% 0.59/0.94  --qbf_split                             512
% 0.59/0.94  
% 0.59/0.94  ------ BMC1 Options
% 0.59/0.94  
% 0.59/0.94  --bmc1_incremental                      false
% 0.59/0.94  --bmc1_axioms                           reachable_all
% 0.59/0.94  --bmc1_min_bound                        0
% 0.59/0.94  --bmc1_max_bound                        -1
% 0.59/0.94  --bmc1_max_bound_default                -1
% 0.59/0.94  --bmc1_symbol_reachability              true
% 0.59/0.94  --bmc1_property_lemmas                  false
% 0.59/0.94  --bmc1_k_induction                      false
% 0.59/0.94  --bmc1_non_equiv_states                 false
% 0.59/0.94  --bmc1_deadlock                         false
% 0.59/0.94  --bmc1_ucm                              false
% 0.59/0.94  --bmc1_add_unsat_core                   none
% 0.59/0.94  --bmc1_unsat_core_children              false
% 0.59/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 0.59/0.94  --bmc1_out_stat                         full
% 0.59/0.94  --bmc1_ground_init                      false
% 0.59/0.94  --bmc1_pre_inst_next_state              false
% 0.59/0.94  --bmc1_pre_inst_state                   false
% 0.59/0.94  --bmc1_pre_inst_reach_state             false
% 0.59/0.94  --bmc1_out_unsat_core                   false
% 0.59/0.94  --bmc1_aig_witness_out                  false
% 0.59/0.94  --bmc1_verbose                          false
% 0.59/0.94  --bmc1_dump_clauses_tptp                false
% 0.59/0.94  --bmc1_dump_unsat_core_tptp             false
% 0.59/0.94  --bmc1_dump_file                        -
% 0.59/0.94  --bmc1_ucm_expand_uc_limit              128
% 0.59/0.94  --bmc1_ucm_n_expand_iterations          6
% 0.59/0.94  --bmc1_ucm_extend_mode                  1
% 0.59/0.94  --bmc1_ucm_init_mode                    2
% 0.59/0.94  --bmc1_ucm_cone_mode                    none
% 0.59/0.94  --bmc1_ucm_reduced_relation_type        0
% 0.59/0.94  --bmc1_ucm_relax_model                  4
% 0.59/0.94  --bmc1_ucm_full_tr_after_sat            true
% 0.59/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 0.59/0.94  --bmc1_ucm_layered_model                none
% 0.59/0.94  --bmc1_ucm_max_lemma_size               10
% 0.59/0.94  
% 0.59/0.94  ------ AIG Options
% 0.59/0.94  
% 0.59/0.94  --aig_mode                              false
% 0.59/0.94  
% 0.59/0.94  ------ Instantiation Options
% 0.59/0.94  
% 0.59/0.94  --instantiation_flag                    true
% 0.59/0.94  --inst_sos_flag                         false
% 0.59/0.94  --inst_sos_phase                        true
% 0.59/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.59/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.59/0.94  --inst_lit_sel_side                     num_symb
% 0.59/0.94  --inst_solver_per_active                1400
% 0.59/0.94  --inst_solver_calls_frac                1.
% 0.59/0.94  --inst_passive_queue_type               priority_queues
% 0.59/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.59/0.94  --inst_passive_queues_freq              [25;2]
% 0.59/0.94  --inst_dismatching                      true
% 0.59/0.94  --inst_eager_unprocessed_to_passive     true
% 0.59/0.94  --inst_prop_sim_given                   true
% 0.59/0.94  --inst_prop_sim_new                     false
% 0.59/0.94  --inst_subs_new                         false
% 0.59/0.94  --inst_eq_res_simp                      false
% 0.59/0.94  --inst_subs_given                       false
% 0.59/0.94  --inst_orphan_elimination               true
% 0.59/0.94  --inst_learning_loop_flag               true
% 0.59/0.94  --inst_learning_start                   3000
% 0.59/0.94  --inst_learning_factor                  2
% 0.59/0.94  --inst_start_prop_sim_after_learn       3
% 0.59/0.94  --inst_sel_renew                        solver
% 0.59/0.94  --inst_lit_activity_flag                true
% 0.59/0.94  --inst_restr_to_given                   false
% 0.59/0.94  --inst_activity_threshold               500
% 0.59/0.94  --inst_out_proof                        true
% 0.59/0.94  
% 0.59/0.94  ------ Resolution Options
% 0.59/0.94  
% 0.59/0.94  --resolution_flag                       true
% 0.59/0.94  --res_lit_sel                           adaptive
% 0.59/0.94  --res_lit_sel_side                      none
% 0.59/0.94  --res_ordering                          kbo
% 0.59/0.94  --res_to_prop_solver                    active
% 0.59/0.94  --res_prop_simpl_new                    false
% 0.59/0.94  --res_prop_simpl_given                  true
% 0.59/0.94  --res_passive_queue_type                priority_queues
% 0.59/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.59/0.94  --res_passive_queues_freq               [15;5]
% 0.59/0.94  --res_forward_subs                      full
% 0.59/0.94  --res_backward_subs                     full
% 0.59/0.94  --res_forward_subs_resolution           true
% 0.59/0.94  --res_backward_subs_resolution          true
% 0.59/0.94  --res_orphan_elimination                true
% 0.59/0.94  --res_time_limit                        2.
% 0.59/0.94  --res_out_proof                         true
% 0.59/0.94  
% 0.59/0.94  ------ Superposition Options
% 0.59/0.94  
% 0.59/0.94  --superposition_flag                    true
% 0.59/0.94  --sup_passive_queue_type                priority_queues
% 0.59/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.59/0.94  --sup_passive_queues_freq               [8;1;4]
% 0.59/0.94  --demod_completeness_check              fast
% 0.59/0.94  --demod_use_ground                      true
% 0.59/0.94  --sup_to_prop_solver                    passive
% 0.59/0.94  --sup_prop_simpl_new                    true
% 0.59/0.94  --sup_prop_simpl_given                  true
% 0.59/0.94  --sup_fun_splitting                     false
% 0.59/0.94  --sup_smt_interval                      50000
% 0.59/0.94  
% 0.59/0.94  ------ Superposition Simplification Setup
% 0.59/0.94  
% 0.59/0.94  --sup_indices_passive                   []
% 0.59/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.59/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.59/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.59/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 0.59/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.59/0.94  --sup_full_bw                           [BwDemod]
% 0.59/0.94  --sup_immed_triv                        [TrivRules]
% 0.59/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.59/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.59/0.94  --sup_immed_bw_main                     []
% 0.59/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.59/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 0.59/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.59/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.59/0.94  
% 0.59/0.94  ------ Combination Options
% 0.59/0.94  
% 0.59/0.94  --comb_res_mult                         3
% 0.59/0.94  --comb_sup_mult                         2
% 0.59/0.94  --comb_inst_mult                        10
% 0.59/0.94  
% 0.59/0.94  ------ Debug Options
% 0.59/0.94  
% 0.59/0.94  --dbg_backtrace                         false
% 0.59/0.94  --dbg_dump_prop_clauses                 false
% 0.59/0.94  --dbg_dump_prop_clauses_file            -
% 0.59/0.94  --dbg_out_stat                          false
% 0.59/0.94  ------ Parsing...
% 0.59/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.59/0.94  
% 0.59/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 0.59/0.94  
% 0.59/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.59/0.94  
% 0.59/0.94  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 0.59/0.94  ------ Proving...
% 0.59/0.94  ------ Problem Properties 
% 0.59/0.94  
% 0.59/0.94  
% 0.59/0.94  clauses                                 3
% 0.59/0.94  conjectures                             1
% 0.59/0.94  EPR                                     0
% 0.59/0.94  Horn                                    3
% 0.59/0.94  unary                                   2
% 0.59/0.94  binary                                  1
% 0.59/0.94  lits                                    4
% 0.59/0.94  lits eq                                 4
% 0.59/0.94  fd_pure                                 0
% 0.59/0.94  fd_pseudo                               0
% 0.59/0.94  fd_cond                                 0
% 0.59/0.94  fd_pseudo_cond                          0
% 0.59/0.94  AC symbols                              0
% 0.59/0.94  
% 0.59/0.94  ------ Schedule dynamic 5 is on 
% 0.59/0.94  
% 0.59/0.94  ------ pure equality problem: resolution off 
% 0.59/0.94  
% 0.59/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.59/0.94  
% 0.59/0.94  
% 0.59/0.94  ------ 
% 0.59/0.94  Current options:
% 0.59/0.94  ------ 
% 0.59/0.94  
% 0.59/0.94  ------ Input Options
% 0.59/0.94  
% 0.59/0.94  --out_options                           all
% 0.59/0.94  --tptp_safe_out                         true
% 0.59/0.94  --problem_path                          ""
% 0.59/0.94  --include_path                          ""
% 0.59/0.94  --clausifier                            res/vclausify_rel
% 0.59/0.94  --clausifier_options                    --mode clausify
% 0.59/0.94  --stdin                                 false
% 0.59/0.94  --stats_out                             all
% 0.59/0.94  
% 0.59/0.94  ------ General Options
% 0.59/0.94  
% 0.59/0.94  --fof                                   false
% 0.59/0.94  --time_out_real                         305.
% 0.59/0.94  --time_out_virtual                      -1.
% 0.59/0.94  --symbol_type_check                     false
% 0.59/0.94  --clausify_out                          false
% 0.59/0.94  --sig_cnt_out                           false
% 0.59/0.94  --trig_cnt_out                          false
% 0.59/0.94  --trig_cnt_out_tolerance                1.
% 0.59/0.94  --trig_cnt_out_sk_spl                   false
% 0.59/0.94  --abstr_cl_out                          false
% 0.59/0.94  
% 0.59/0.94  ------ Global Options
% 0.59/0.94  
% 0.59/0.94  --schedule                              default
% 0.59/0.94  --add_important_lit                     false
% 0.59/0.94  --prop_solver_per_cl                    1000
% 0.59/0.94  --min_unsat_core                        false
% 0.59/0.94  --soft_assumptions                      false
% 0.59/0.94  --soft_lemma_size                       3
% 0.59/0.94  --prop_impl_unit_size                   0
% 0.59/0.94  --prop_impl_unit                        []
% 0.59/0.94  --share_sel_clauses                     true
% 0.59/0.94  --reset_solvers                         false
% 0.59/0.94  --bc_imp_inh                            [conj_cone]
% 0.59/0.94  --conj_cone_tolerance                   3.
% 0.59/0.94  --extra_neg_conj                        none
% 0.59/0.94  --large_theory_mode                     true
% 0.59/0.94  --prolific_symb_bound                   200
% 0.59/0.94  --lt_threshold                          2000
% 0.59/0.94  --clause_weak_htbl                      true
% 0.59/0.94  --gc_record_bc_elim                     false
% 0.59/0.94  
% 0.59/0.94  ------ Preprocessing Options
% 0.59/0.94  
% 0.59/0.94  --preprocessing_flag                    true
% 0.59/0.94  --time_out_prep_mult                    0.1
% 0.59/0.94  --splitting_mode                        input
% 0.59/0.94  --splitting_grd                         true
% 0.59/0.94  --splitting_cvd                         false
% 0.59/0.94  --splitting_cvd_svl                     false
% 0.59/0.94  --splitting_nvd                         32
% 0.59/0.94  --sub_typing                            true
% 0.59/0.94  --prep_gs_sim                           true
% 0.59/0.94  --prep_unflatten                        true
% 0.59/0.94  --prep_res_sim                          true
% 0.59/0.94  --prep_upred                            true
% 0.59/0.94  --prep_sem_filter                       exhaustive
% 0.59/0.94  --prep_sem_filter_out                   false
% 0.59/0.94  --pred_elim                             true
% 0.59/0.94  --res_sim_input                         true
% 0.59/0.94  --eq_ax_congr_red                       true
% 0.59/0.94  --pure_diseq_elim                       true
% 0.59/0.94  --brand_transform                       false
% 0.59/0.94  --non_eq_to_eq                          false
% 0.59/0.94  --prep_def_merge                        true
% 0.59/0.94  --prep_def_merge_prop_impl              false
% 0.59/0.94  --prep_def_merge_mbd                    true
% 0.59/0.94  --prep_def_merge_tr_red                 false
% 0.59/0.94  --prep_def_merge_tr_cl                  false
% 0.59/0.94  --smt_preprocessing                     true
% 0.59/0.94  --smt_ac_axioms                         fast
% 0.59/0.94  --preprocessed_out                      false
% 0.59/0.94  --preprocessed_stats                    false
% 0.59/0.94  
% 0.59/0.94  ------ Abstraction refinement Options
% 0.59/0.94  
% 0.59/0.94  --abstr_ref                             []
% 0.59/0.94  --abstr_ref_prep                        false
% 0.59/0.94  --abstr_ref_until_sat                   false
% 0.59/0.94  --abstr_ref_sig_restrict                funpre
% 0.59/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 0.59/0.94  --abstr_ref_under                       []
% 0.59/0.94  
% 0.59/0.94  ------ SAT Options
% 0.59/0.94  
% 0.59/0.94  --sat_mode                              false
% 0.59/0.94  --sat_fm_restart_options                ""
% 0.59/0.94  --sat_gr_def                            false
% 0.59/0.94  --sat_epr_types                         true
% 0.59/0.94  --sat_non_cyclic_types                  false
% 0.59/0.94  --sat_finite_models                     false
% 0.59/0.94  --sat_fm_lemmas                         false
% 0.59/0.94  --sat_fm_prep                           false
% 0.59/0.94  --sat_fm_uc_incr                        true
% 0.59/0.94  --sat_out_model                         small
% 0.59/0.94  --sat_out_clauses                       false
% 0.59/0.94  
% 0.59/0.94  ------ QBF Options
% 0.59/0.94  
% 0.59/0.94  --qbf_mode                              false
% 0.59/0.94  --qbf_elim_univ                         false
% 0.59/0.94  --qbf_dom_inst                          none
% 0.59/0.94  --qbf_dom_pre_inst                      false
% 0.59/0.94  --qbf_sk_in                             false
% 0.59/0.94  --qbf_pred_elim                         true
% 0.59/0.94  --qbf_split                             512
% 0.59/0.94  
% 0.59/0.94  ------ BMC1 Options
% 0.59/0.94  
% 0.59/0.94  --bmc1_incremental                      false
% 0.59/0.94  --bmc1_axioms                           reachable_all
% 0.59/0.94  --bmc1_min_bound                        0
% 0.59/0.94  --bmc1_max_bound                        -1
% 0.59/0.94  --bmc1_max_bound_default                -1
% 0.59/0.94  --bmc1_symbol_reachability              true
% 0.59/0.94  --bmc1_property_lemmas                  false
% 0.59/0.94  --bmc1_k_induction                      false
% 0.59/0.94  --bmc1_non_equiv_states                 false
% 0.59/0.94  --bmc1_deadlock                         false
% 0.59/0.94  --bmc1_ucm                              false
% 0.59/0.94  --bmc1_add_unsat_core                   none
% 0.59/0.94  --bmc1_unsat_core_children              false
% 0.59/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 0.59/0.94  --bmc1_out_stat                         full
% 0.59/0.94  --bmc1_ground_init                      false
% 0.59/0.94  --bmc1_pre_inst_next_state              false
% 0.59/0.94  --bmc1_pre_inst_state                   false
% 0.59/0.94  --bmc1_pre_inst_reach_state             false
% 0.59/0.94  --bmc1_out_unsat_core                   false
% 0.59/0.94  --bmc1_aig_witness_out                  false
% 0.59/0.94  --bmc1_verbose                          false
% 0.59/0.94  --bmc1_dump_clauses_tptp                false
% 0.59/0.94  --bmc1_dump_unsat_core_tptp             false
% 0.59/0.94  --bmc1_dump_file                        -
% 0.59/0.94  --bmc1_ucm_expand_uc_limit              128
% 0.59/0.94  --bmc1_ucm_n_expand_iterations          6
% 0.59/0.94  --bmc1_ucm_extend_mode                  1
% 0.59/0.94  --bmc1_ucm_init_mode                    2
% 0.59/0.94  --bmc1_ucm_cone_mode                    none
% 0.59/0.94  --bmc1_ucm_reduced_relation_type        0
% 0.59/0.94  --bmc1_ucm_relax_model                  4
% 0.59/0.94  --bmc1_ucm_full_tr_after_sat            true
% 0.59/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 0.59/0.94  --bmc1_ucm_layered_model                none
% 0.59/0.94  --bmc1_ucm_max_lemma_size               10
% 0.59/0.94  
% 0.59/0.94  ------ AIG Options
% 0.59/0.94  
% 0.59/0.94  --aig_mode                              false
% 0.59/0.94  
% 0.59/0.94  ------ Instantiation Options
% 0.59/0.94  
% 0.59/0.94  --instantiation_flag                    true
% 0.59/0.94  --inst_sos_flag                         false
% 0.59/0.94  --inst_sos_phase                        true
% 0.59/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.59/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.59/0.94  --inst_lit_sel_side                     none
% 0.59/0.94  --inst_solver_per_active                1400
% 0.59/0.94  --inst_solver_calls_frac                1.
% 0.59/0.94  --inst_passive_queue_type               priority_queues
% 0.59/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.59/0.94  --inst_passive_queues_freq              [25;2]
% 0.59/0.94  --inst_dismatching                      true
% 0.59/0.94  --inst_eager_unprocessed_to_passive     true
% 0.59/0.94  --inst_prop_sim_given                   true
% 0.59/0.94  --inst_prop_sim_new                     false
% 0.59/0.94  --inst_subs_new                         false
% 0.59/0.94  --inst_eq_res_simp                      false
% 0.59/0.94  --inst_subs_given                       false
% 0.59/0.94  --inst_orphan_elimination               true
% 0.59/0.94  --inst_learning_loop_flag               true
% 0.59/0.94  --inst_learning_start                   3000
% 0.59/0.94  --inst_learning_factor                  2
% 0.59/0.94  --inst_start_prop_sim_after_learn       3
% 0.59/0.94  --inst_sel_renew                        solver
% 0.59/0.94  --inst_lit_activity_flag                true
% 0.59/0.94  --inst_restr_to_given                   false
% 0.59/0.94  --inst_activity_threshold               500
% 0.59/0.94  --inst_out_proof                        true
% 0.59/0.94  
% 0.59/0.94  ------ Resolution Options
% 0.59/0.94  
% 0.59/0.94  --resolution_flag                       false
% 0.59/0.94  --res_lit_sel                           adaptive
% 0.59/0.94  --res_lit_sel_side                      none
% 0.59/0.94  --res_ordering                          kbo
% 0.59/0.94  --res_to_prop_solver                    active
% 0.59/0.94  --res_prop_simpl_new                    false
% 0.59/0.94  --res_prop_simpl_given                  true
% 0.59/0.94  --res_passive_queue_type                priority_queues
% 0.59/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.59/0.94  --res_passive_queues_freq               [15;5]
% 0.59/0.94  --res_forward_subs                      full
% 0.59/0.94  --res_backward_subs                     full
% 0.59/0.94  --res_forward_subs_resolution           true
% 0.59/0.94  --res_backward_subs_resolution          true
% 0.59/0.94  --res_orphan_elimination                true
% 0.59/0.94  --res_time_limit                        2.
% 0.59/0.94  --res_out_proof                         true
% 0.59/0.94  
% 0.59/0.94  ------ Superposition Options
% 0.59/0.94  
% 0.59/0.94  --superposition_flag                    true
% 0.59/0.94  --sup_passive_queue_type                priority_queues
% 0.59/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.59/0.94  --sup_passive_queues_freq               [8;1;4]
% 0.59/0.94  --demod_completeness_check              fast
% 0.59/0.94  --demod_use_ground                      true
% 0.59/0.94  --sup_to_prop_solver                    passive
% 0.59/0.94  --sup_prop_simpl_new                    true
% 0.59/0.94  --sup_prop_simpl_given                  true
% 0.59/0.94  --sup_fun_splitting                     false
% 0.59/0.94  --sup_smt_interval                      50000
% 0.59/0.94  
% 0.59/0.94  ------ Superposition Simplification Setup
% 0.59/0.94  
% 0.59/0.94  --sup_indices_passive                   []
% 0.59/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.59/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.59/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.59/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 0.59/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.59/0.94  --sup_full_bw                           [BwDemod]
% 0.59/0.94  --sup_immed_triv                        [TrivRules]
% 0.59/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.59/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.59/0.94  --sup_immed_bw_main                     []
% 0.59/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.59/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 0.59/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.59/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.59/0.94  
% 0.59/0.94  ------ Combination Options
% 0.59/0.94  
% 0.59/0.94  --comb_res_mult                         3
% 0.59/0.94  --comb_sup_mult                         2
% 0.59/0.94  --comb_inst_mult                        10
% 0.59/0.94  
% 0.59/0.94  ------ Debug Options
% 0.59/0.94  
% 0.59/0.94  --dbg_backtrace                         false
% 0.59/0.94  --dbg_dump_prop_clauses                 false
% 0.59/0.94  --dbg_dump_prop_clauses_file            -
% 0.59/0.94  --dbg_out_stat                          false
% 0.59/0.94  
% 0.59/0.94  
% 0.59/0.94  
% 0.59/0.94  
% 0.59/0.94  ------ Proving...
% 0.59/0.94  
% 0.59/0.94  
% 0.59/0.94  % SZS status Theorem for theBenchmark.p
% 0.59/0.94  
% 0.59/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 0.59/0.94  
% 0.59/0.94  fof(f1,axiom,(
% 0.59/0.94    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.59/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.59/0.94  
% 0.59/0.94  fof(f10,plain,(
% 0.59/0.94    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.59/0.94    inference(ennf_transformation,[],[f1])).
% 0.59/0.94  
% 0.59/0.94  fof(f17,plain,(
% 0.59/0.94    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.59/0.94    inference(cnf_transformation,[],[f10])).
% 0.59/0.94  
% 0.59/0.94  fof(f2,axiom,(
% 0.59/0.94    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.59/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.59/0.94  
% 0.59/0.94  fof(f18,plain,(
% 0.59/0.94    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.59/0.94    inference(cnf_transformation,[],[f2])).
% 0.59/0.94  
% 0.59/0.94  fof(f6,axiom,(
% 0.59/0.94    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.59/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.59/0.94  
% 0.59/0.94  fof(f13,plain,(
% 0.59/0.94    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.59/0.94    inference(ennf_transformation,[],[f6])).
% 0.59/0.94  
% 0.59/0.94  fof(f21,plain,(
% 0.59/0.94    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.59/0.94    inference(cnf_transformation,[],[f13])).
% 0.59/0.94  
% 0.59/0.94  fof(f7,conjecture,(
% 0.59/0.94    ! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 0.59/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.59/0.94  
% 0.59/0.94  fof(f8,negated_conjecture,(
% 0.59/0.94    ~! [X0] : (l1_pre_topc(X0) => k1_struct_0(X0) = k1_tops_1(X0,k1_struct_0(X0)))),
% 0.59/0.94    inference(negated_conjecture,[],[f7])).
% 0.59/0.94  
% 0.59/0.94  fof(f14,plain,(
% 0.59/0.94    ? [X0] : (k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0)) & l1_pre_topc(X0))),
% 0.59/0.94    inference(ennf_transformation,[],[f8])).
% 0.59/0.94  
% 0.59/0.94  fof(f15,plain,(
% 0.59/0.94    ? [X0] : (k1_struct_0(X0) != k1_tops_1(X0,k1_struct_0(X0)) & l1_pre_topc(X0)) => (k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) & l1_pre_topc(sK0))),
% 0.59/0.94    introduced(choice_axiom,[])).
% 0.59/0.94  
% 0.59/0.94  fof(f16,plain,(
% 0.59/0.94    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) & l1_pre_topc(sK0)),
% 0.59/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 0.59/0.94  
% 0.59/0.94  fof(f22,plain,(
% 0.59/0.94    l1_pre_topc(sK0)),
% 0.59/0.94    inference(cnf_transformation,[],[f16])).
% 0.59/0.94  
% 0.59/0.94  fof(f23,plain,(
% 0.59/0.94    k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0))),
% 0.59/0.94    inference(cnf_transformation,[],[f16])).
% 0.59/0.94  
% 0.59/0.94  fof(f5,axiom,(
% 0.59/0.94    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.59/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.59/0.94  
% 0.59/0.94  fof(f12,plain,(
% 0.59/0.94    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.59/0.94    inference(ennf_transformation,[],[f5])).
% 0.59/0.94  
% 0.59/0.94  fof(f20,plain,(
% 0.59/0.94    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.59/0.94    inference(cnf_transformation,[],[f12])).
% 0.59/0.94  
% 0.59/0.94  fof(f4,axiom,(
% 0.59/0.94    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 0.59/0.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.59/0.94  
% 0.59/0.94  fof(f11,plain,(
% 0.59/0.94    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.59/0.94    inference(ennf_transformation,[],[f4])).
% 0.59/0.94  
% 0.59/0.94  fof(f19,plain,(
% 0.59/0.94    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.59/0.94    inference(cnf_transformation,[],[f11])).
% 0.59/0.94  
% 0.59/0.94  cnf(c_0,plain,
% 0.59/0.94      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 0.59/0.94      inference(cnf_transformation,[],[f17]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_1,plain,
% 0.59/0.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 0.59/0.94      inference(cnf_transformation,[],[f18]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_4,plain,
% 0.59/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.59/0.94      | r1_tarski(k1_tops_1(X1,X0),X0)
% 0.59/0.94      | ~ l1_pre_topc(X1) ),
% 0.59/0.94      inference(cnf_transformation,[],[f21]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_77,plain,
% 0.59/0.94      ( r1_tarski(k1_tops_1(X0,X1),X1)
% 0.59/0.94      | ~ l1_pre_topc(X0)
% 0.59/0.94      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(X2)
% 0.59/0.94      | k1_xboole_0 != X1 ),
% 0.59/0.94      inference(resolution_lifted,[status(thm)],[c_1,c_4]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_78,plain,
% 0.59/0.94      ( r1_tarski(k1_tops_1(X0,k1_xboole_0),k1_xboole_0)
% 0.59/0.94      | ~ l1_pre_topc(X0)
% 0.59/0.94      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(X1) ),
% 0.59/0.94      inference(unflattening,[status(thm)],[c_77]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_110,plain,
% 0.59/0.94      ( ~ l1_pre_topc(X0)
% 0.59/0.94      | k1_tops_1(X0,k1_xboole_0) != X1
% 0.59/0.94      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(X2)
% 0.59/0.94      | k1_xboole_0 = X1
% 0.59/0.94      | k1_xboole_0 != k1_xboole_0 ),
% 0.59/0.94      inference(resolution_lifted,[status(thm)],[c_0,c_78]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_111,plain,
% 0.59/0.94      ( ~ l1_pre_topc(X0)
% 0.59/0.94      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(X1)
% 0.59/0.94      | k1_xboole_0 = k1_tops_1(X0,k1_xboole_0) ),
% 0.59/0.94      inference(unflattening,[status(thm)],[c_110]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_6,negated_conjecture,
% 0.59/0.94      ( l1_pre_topc(sK0) ),
% 0.59/0.94      inference(cnf_transformation,[],[f22]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_129,plain,
% 0.59/0.94      ( k1_tops_1(X0,k1_xboole_0) = k1_xboole_0
% 0.59/0.94      | k1_zfmisc_1(u1_struct_0(X0)) != k1_zfmisc_1(X1)
% 0.59/0.94      | sK0 != X0 ),
% 0.59/0.94      inference(resolution_lifted,[status(thm)],[c_111,c_6]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_130,plain,
% 0.59/0.94      ( k1_tops_1(sK0,k1_xboole_0) = k1_xboole_0
% 0.59/0.94      | k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0) ),
% 0.59/0.94      inference(unflattening,[status(thm)],[c_129]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_153,plain,
% 0.59/0.94      ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(X0_41)
% 0.59/0.94      | k1_tops_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 0.59/0.94      inference(subtyping,[status(esa)],[c_130]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_175,plain,
% 0.59/0.94      ( k1_zfmisc_1(u1_struct_0(sK0)) != k1_zfmisc_1(u1_struct_0(sK0))
% 0.59/0.94      | k1_tops_1(sK0,k1_xboole_0) = k1_xboole_0 ),
% 0.59/0.94      inference(instantiation,[status(thm)],[c_153]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_156,plain,( X0_40 = X0_40 ),theory(equality) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_174,plain,
% 0.59/0.94      ( k1_zfmisc_1(u1_struct_0(sK0)) = k1_zfmisc_1(u1_struct_0(sK0)) ),
% 0.59/0.94      inference(instantiation,[status(thm)],[c_156]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_5,negated_conjecture,
% 0.59/0.94      ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) ),
% 0.59/0.94      inference(cnf_transformation,[],[f23]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_154,negated_conjecture,
% 0.59/0.94      ( k1_struct_0(sK0) != k1_tops_1(sK0,k1_struct_0(sK0)) ),
% 0.59/0.94      inference(subtyping,[status(esa)],[c_5]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_3,plain,
% 0.59/0.94      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 0.59/0.94      inference(cnf_transformation,[],[f20]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_2,plain,
% 0.59/0.94      ( ~ l1_struct_0(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 0.59/0.94      inference(cnf_transformation,[],[f19]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_96,plain,
% 0.59/0.94      ( ~ l1_pre_topc(X0) | k1_struct_0(X0) = k1_xboole_0 ),
% 0.59/0.94      inference(resolution,[status(thm)],[c_3,c_2]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_138,plain,
% 0.59/0.94      ( k1_struct_0(X0) = k1_xboole_0 | sK0 != X0 ),
% 0.59/0.94      inference(resolution_lifted,[status(thm)],[c_96,c_6]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_139,plain,
% 0.59/0.94      ( k1_struct_0(sK0) = k1_xboole_0 ),
% 0.59/0.94      inference(unflattening,[status(thm)],[c_138]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_152,plain,
% 0.59/0.94      ( k1_struct_0(sK0) = k1_xboole_0 ),
% 0.59/0.94      inference(subtyping,[status(esa)],[c_139]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(c_166,plain,
% 0.59/0.94      ( k1_tops_1(sK0,k1_xboole_0) != k1_xboole_0 ),
% 0.59/0.94      inference(light_normalisation,[status(thm)],[c_154,c_152]) ).
% 0.59/0.94  
% 0.59/0.94  cnf(contradiction,plain,
% 0.59/0.94      ( $false ),
% 0.59/0.94      inference(minisat,[status(thm)],[c_175,c_174,c_166]) ).
% 0.59/0.94  
% 0.59/0.94  
% 0.59/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 0.59/0.94  
% 0.59/0.94  ------                               Statistics
% 0.59/0.94  
% 0.59/0.94  ------ General
% 0.59/0.94  
% 0.59/0.94  abstr_ref_over_cycles:                  0
% 0.59/0.94  abstr_ref_under_cycles:                 0
% 0.59/0.94  gc_basic_clause_elim:                   0
% 0.59/0.94  forced_gc_time:                         0
% 0.59/0.94  parsing_time:                           0.008
% 0.59/0.94  unif_index_cands_time:                  0.
% 0.59/0.94  unif_index_add_time:                    0.
% 0.59/0.94  orderings_time:                         0.
% 0.59/0.94  out_proof_time:                         0.006
% 0.59/0.94  total_time:                             0.037
% 0.59/0.94  num_of_symbols:                         42
% 0.59/0.94  num_of_terms:                           294
% 0.59/0.94  
% 0.59/0.94  ------ Preprocessing
% 0.59/0.94  
% 0.59/0.94  num_of_splits:                          0
% 0.59/0.94  num_of_split_atoms:                     0
% 0.59/0.94  num_of_reused_defs:                     0
% 0.59/0.94  num_eq_ax_congr_red:                    6
% 0.59/0.94  num_of_sem_filtered_clauses:            0
% 0.59/0.94  num_of_subtypes:                        4
% 0.59/0.94  monotx_restored_types:                  0
% 0.59/0.94  sat_num_of_epr_types:                   0
% 0.59/0.94  sat_num_of_non_cyclic_types:            0
% 0.59/0.94  sat_guarded_non_collapsed_types:        0
% 0.59/0.94  num_pure_diseq_elim:                    0
% 0.59/0.94  simp_replaced_by:                       0
% 0.59/0.94  res_preprocessed:                       18
% 0.59/0.94  prep_upred:                             0
% 0.59/0.94  prep_unflattend:                        4
% 0.59/0.94  smt_new_axioms:                         0
% 0.59/0.94  pred_elim_cands:                        0
% 0.59/0.94  pred_elim:                              4
% 0.59/0.94  pred_elim_cl:                           4
% 0.59/0.94  pred_elim_cycles:                       5
% 0.59/0.94  merged_defs:                            0
% 0.59/0.94  merged_defs_ncl:                        0
% 0.59/0.94  bin_hyper_res:                          0
% 0.59/0.94  prep_cycles:                            3
% 0.59/0.94  pred_elim_time:                         0.001
% 0.59/0.94  splitting_time:                         0.
% 0.59/0.94  sem_filter_time:                        0.
% 0.59/0.94  monotx_time:                            0.
% 0.59/0.94  subtype_inf_time:                       0.
% 0.59/0.94  
% 0.59/0.94  ------ Problem properties
% 0.59/0.94  
% 0.59/0.94  clauses:                                3
% 0.59/0.94  conjectures:                            1
% 0.59/0.94  epr:                                    0
% 0.59/0.94  horn:                                   3
% 0.59/0.94  ground:                                 2
% 0.59/0.94  unary:                                  2
% 0.59/0.94  binary:                                 1
% 0.59/0.94  lits:                                   4
% 0.59/0.94  lits_eq:                                4
% 0.59/0.94  fd_pure:                                0
% 0.59/0.94  fd_pseudo:                              0
% 0.59/0.94  fd_cond:                                0
% 0.59/0.94  fd_pseudo_cond:                         0
% 0.59/0.94  ac_symbols:                             0
% 0.59/0.94  
% 0.59/0.94  ------ Propositional Solver
% 0.59/0.94  
% 0.59/0.94  prop_solver_calls:                      18
% 0.59/0.94  prop_fast_solver_calls:                 71
% 0.59/0.94  smt_solver_calls:                       0
% 0.59/0.94  smt_fast_solver_calls:                  0
% 0.59/0.94  prop_num_of_clauses:                    54
% 0.59/0.94  prop_preprocess_simplified:             363
% 0.59/0.94  prop_fo_subsumed:                       0
% 0.59/0.94  prop_solver_time:                       0.
% 0.59/0.94  smt_solver_time:                        0.
% 0.59/0.94  smt_fast_solver_time:                   0.
% 0.59/0.94  prop_fast_solver_time:                  0.
% 0.59/0.94  prop_unsat_core_time:                   0.
% 0.59/0.94  
% 0.59/0.94  ------ QBF
% 0.59/0.94  
% 0.59/0.94  qbf_q_res:                              0
% 0.59/0.94  qbf_num_tautologies:                    0
% 0.59/0.94  qbf_prep_cycles:                        0
% 0.59/0.94  
% 0.59/0.94  ------ BMC1
% 0.59/0.94  
% 0.59/0.94  bmc1_current_bound:                     -1
% 0.59/0.94  bmc1_last_solved_bound:                 -1
% 0.59/0.94  bmc1_unsat_core_size:                   -1
% 0.59/0.94  bmc1_unsat_core_parents_size:           -1
% 0.59/0.94  bmc1_merge_next_fun:                    0
% 0.59/0.94  bmc1_unsat_core_clauses_time:           0.
% 0.59/0.94  
% 0.59/0.94  ------ Instantiation
% 0.59/0.94  
% 0.59/0.94  inst_num_of_clauses:                    9
% 0.59/0.94  inst_num_in_passive:                    3
% 0.59/0.94  inst_num_in_active:                     4
% 0.59/0.94  inst_num_in_unprocessed:                1
% 0.59/0.94  inst_num_of_loops:                      5
% 0.59/0.94  inst_num_of_learning_restarts:          0
% 0.59/0.94  inst_num_moves_active_passive:          0
% 0.59/0.94  inst_lit_activity:                      0
% 0.59/0.94  inst_lit_activity_moves:                0
% 0.59/0.94  inst_num_tautologies:                   0
% 0.59/0.94  inst_num_prop_implied:                  0
% 0.59/0.94  inst_num_existing_simplified:           0
% 0.59/0.94  inst_num_eq_res_simplified:             0
% 0.59/0.94  inst_num_child_elim:                    0
% 0.59/0.94  inst_num_of_dismatching_blockings:      0
% 0.59/0.94  inst_num_of_non_proper_insts:           0
% 0.59/0.94  inst_num_of_duplicates:                 0
% 0.59/0.94  inst_inst_num_from_inst_to_res:         0
% 0.59/0.94  inst_dismatching_checking_time:         0.
% 0.59/0.94  
% 0.59/0.94  ------ Resolution
% 0.59/0.94  
% 0.59/0.94  res_num_of_clauses:                     0
% 0.59/0.94  res_num_in_passive:                     0
% 0.59/0.94  res_num_in_active:                      0
% 0.59/0.94  res_num_of_loops:                       21
% 0.59/0.94  res_forward_subset_subsumed:            0
% 0.59/0.94  res_backward_subset_subsumed:           0
% 0.59/0.94  res_forward_subsumed:                   0
% 0.59/0.94  res_backward_subsumed:                  0
% 0.59/0.94  res_forward_subsumption_resolution:     0
% 0.59/0.94  res_backward_subsumption_resolution:    0
% 0.59/0.94  res_clause_to_clause_subsumption:       4
% 0.59/0.94  res_orphan_elimination:                 0
% 0.59/0.94  res_tautology_del:                      0
% 0.59/0.94  res_num_eq_res_simplified:              0
% 0.59/0.94  res_num_sel_changes:                    0
% 0.59/0.94  res_moves_from_active_to_pass:          0
% 0.59/0.94  
% 0.59/0.94  ------ Superposition
% 0.59/0.94  
% 0.59/0.94  sup_time_total:                         0.
% 0.59/0.94  sup_time_generating:                    0.
% 0.59/0.94  sup_time_sim_full:                      0.
% 0.59/0.94  sup_time_sim_immed:                     0.
% 0.59/0.94  
% 0.59/0.94  sup_num_of_clauses:                     3
% 0.59/0.94  sup_num_in_active:                      0
% 0.59/0.94  sup_num_in_passive:                     3
% 0.59/0.94  sup_num_of_loops:                       0
% 0.59/0.94  sup_fw_superposition:                   0
% 0.59/0.94  sup_bw_superposition:                   0
% 0.59/0.94  sup_immediate_simplified:               0
% 0.59/0.94  sup_given_eliminated:                   0
% 0.59/0.94  comparisons_done:                       0
% 0.59/0.94  comparisons_avoided:                    0
% 0.59/0.94  
% 0.59/0.94  ------ Simplifications
% 0.59/0.94  
% 0.59/0.94  
% 0.59/0.94  sim_fw_subset_subsumed:                 0
% 0.59/0.94  sim_bw_subset_subsumed:                 0
% 0.59/0.94  sim_fw_subsumed:                        0
% 0.59/0.94  sim_bw_subsumed:                        0
% 0.59/0.94  sim_fw_subsumption_res:                 1
% 0.59/0.94  sim_bw_subsumption_res:                 0
% 0.59/0.94  sim_tautology_del:                      0
% 0.59/0.94  sim_eq_tautology_del:                   0
% 0.59/0.94  sim_eq_res_simp:                        0
% 0.59/0.94  sim_fw_demodulated:                     0
% 0.59/0.94  sim_bw_demodulated:                     0
% 0.59/0.94  sim_light_normalised:                   1
% 0.59/0.94  sim_joinable_taut:                      0
% 0.59/0.94  sim_joinable_simp:                      0
% 0.59/0.94  sim_ac_normalised:                      0
% 0.59/0.94  sim_smt_subsumption:                    0
% 0.59/0.94  
%------------------------------------------------------------------------------
