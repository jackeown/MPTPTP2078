%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:42 EST 2020

% Result     : CounterSatisfiable 1.88s
% Output     : Model 1.88s
% Verified   : 
% Statistics : Number of formulae       :    8 (   8 expanded)
%              Number of leaves         :    8 (   8 expanded)
%              Depth                    :    0
%              Number of atoms          :  123 ( 123 expanded)
%              Number of equality atoms :  111 ( 111 expanded)
%              Maximal formula depth    :   33 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%------ Positive definition of equality_sorted 
fof(lit_def,axiom,(
    ! [X0_0,X0_2,X1_2] :
      ( equality_sorted(X0_0,X0_2,X1_2)
    <=> ( ( X0_0 = $o
          & X1_2 = X0_2 )
        | ( X0_0 = $i
          & X0 != k1_zfmisc_1(X0)
          & X0 != k2_struct_0(X0)
          & X0 != sK7
          & ( X0 != u1_struct_0(sK5)
            | X1 != u1_struct_0(sK6) )
          & X0 != sK6
          & X0 != u1_struct_0(sK6)
          & X0 != k2_struct_0(sK5)
          & X0 != k1_zfmisc_1(k2_struct_0(sK5))
          & X0 != k2_struct_0(sK6)
          & X0 != k1_zfmisc_1(k2_struct_0(X0))
          & X1 != k1_zfmisc_1(X1)
          & X1 != k2_struct_0(X1)
          & X1 != sK7
          & X1 != sK6
          & X1 != u1_struct_0(sK6)
          & X1 != k2_struct_0(sK5)
          & X1 != k1_zfmisc_1(k2_struct_0(X1))
          & X1 != k1_zfmisc_1(k2_struct_0(sK5))
          & X1 != k2_struct_0(sK6) )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = k1_zfmisc_1(X2)
            & X1 = k1_zfmisc_1(X2)
            & X2 != k2_struct_0(sK5)
            & X2 != k2_struct_0(X2) )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = k1_zfmisc_1(X2)
            & X1 = k1_zfmisc_1(X3)
            & X2 != k2_struct_0(sK5)
            & X2 != k2_struct_0(X2)
            & X3 != k2_struct_0(sK5)
            & X3 != k2_struct_0(X3) )
        | ( X0_0 = $i
          & X0 = sK7
          & X1 = sK7 )
        | ( X0_0 = $i
          & X0 = sK6
          & X1 = sK6 )
        | ( X0_0 = $i
          & X0 = u1_struct_0(sK6)
          & X1 = u1_struct_0(sK6) )
        | ( X0_0 = $i
          & X0 = k2_struct_0(sK5)
          & X1 = k2_struct_0(sK5) )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = k2_struct_0(X2)
            & X1 = k2_struct_0(X2)
            & X2 != sK5
            & X2 != sK6 )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = u1_struct_0(X2)
            & X1 = u1_struct_0(X3)
            & ( X2 != sK5
              | X3 != sK6 )
            & X2 != sK6
            & X3 != sK6 )
        | ( X0_0 = $i
          & X0 = k1_zfmisc_1(k2_struct_0(sK5))
          & X1 = k1_zfmisc_1(k2_struct_0(sK5)) )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = k1_zfmisc_1(k2_struct_0(sK5))
            & X1 = k1_zfmisc_1(k2_struct_0(X2))
            & X2 != sK5 )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = k1_zfmisc_1(k2_struct_0(X2))
            & X1 = k1_zfmisc_1(k2_struct_0(sK5))
            & X2 != sK5 )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = k1_zfmisc_1(k2_struct_0(X2))
            & X1 = k1_zfmisc_1(k2_struct_0(X2))
            & X2 != sK5 )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = k1_zfmisc_1(k2_struct_0(X2))
            & X1 = k1_zfmisc_1(k2_struct_0(X3))
            & X2 != sK5
            & X3 != sK5 )
        | ( X0_0 = $i
          & X0 = k2_struct_0(sK6)
          & X1 = k2_struct_0(sK6) )
        | ? [X2,X3,X4,X5,X6,X7] :
            ( X0_0 = $i
            & X0 = k9_subset_1(X2,X3,X4)
            & X1 = k9_subset_1(X5,X6,X7) )
        | ( X0_0 = $i
          & X1 = X0
          & X0 != k1_zfmisc_1(X0)
          & X0 != k2_struct_0(X0)
          & X0 != sK7
          & X0 != sK6
          & X0 != u1_struct_0(sK6)
          & X0 != k2_struct_0(sK5)
          & X0 != k1_zfmisc_1(k2_struct_0(sK5))
          & X0 != k2_struct_0(sK6)
          & X0 != k1_zfmisc_1(k2_struct_0(X0)) ) ) ) )).

%------ Positive definition of m1_subset_1 
fof(lit_def_001,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
    <=> ( ( X0 = sK7
          & X1 = u1_struct_0(sK6) )
        | ( X0 = k2_struct_0(sK6)
          & X1 = k1_zfmisc_1(k2_struct_0(sK5)) )
        | ? [X2] :
            ( X0 = k2_struct_0(sK6)
            & X1 = k1_zfmisc_1(k2_struct_0(X2)) ) ) ) )).

%------ Positive definition of v1_xboole_0 
fof(lit_def_002,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> $false ) )).

%------ Positive definition of r2_hidden 
fof(lit_def_003,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
    <=> ( ( X0 = sK7
          & X1 = u1_struct_0(sK6) )
        | ( X0 = k2_struct_0(sK6)
          & X1 = k1_zfmisc_1(k2_struct_0(sK5)) )
        | ? [X2] :
            ( X0 = k2_struct_0(sK6)
            & X1 = k1_zfmisc_1(k2_struct_0(X2)) ) ) ) )).

%------ Positive definition of r1_tarski 
fof(lit_def_004,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> $false ) )).

%------ Positive definition of m1_pre_topc 
fof(lit_def_005,axiom,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,X1)
    <=> $false ) )).

%------ Positive definition of sP0 
fof(lit_def_006,axiom,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ( X0 = sK6
        | ( X0 = sK6
          & X1 = sK5 ) ) ) )).

%------ Positive definition of l1_pre_topc 
fof(lit_def_007,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
    <=> $false ) )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.88/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/0.99  
% 1.88/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.88/0.99  
% 1.88/0.99  ------  iProver source info
% 1.88/0.99  
% 1.88/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.88/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.88/0.99  git: non_committed_changes: false
% 1.88/0.99  git: last_make_outside_of_git: false
% 1.88/0.99  
% 1.88/0.99  ------ 
% 1.88/0.99  
% 1.88/0.99  ------ Input Options
% 1.88/0.99  
% 1.88/0.99  --out_options                           all
% 1.88/0.99  --tptp_safe_out                         true
% 1.88/0.99  --problem_path                          ""
% 1.88/0.99  --include_path                          ""
% 1.88/0.99  --clausifier                            res/vclausify_rel
% 1.88/0.99  --clausifier_options                    --mode clausify
% 1.88/0.99  --stdin                                 false
% 1.88/0.99  --stats_out                             all
% 1.88/0.99  
% 1.88/0.99  ------ General Options
% 1.88/0.99  
% 1.88/0.99  --fof                                   false
% 1.88/0.99  --time_out_real                         305.
% 1.88/0.99  --time_out_virtual                      -1.
% 1.88/0.99  --symbol_type_check                     false
% 1.88/0.99  --clausify_out                          false
% 1.88/0.99  --sig_cnt_out                           false
% 1.88/0.99  --trig_cnt_out                          false
% 1.88/0.99  --trig_cnt_out_tolerance                1.
% 1.88/0.99  --trig_cnt_out_sk_spl                   false
% 1.88/0.99  --abstr_cl_out                          false
% 1.88/0.99  
% 1.88/0.99  ------ Global Options
% 1.88/0.99  
% 1.88/0.99  --schedule                              default
% 1.88/0.99  --add_important_lit                     false
% 1.88/0.99  --prop_solver_per_cl                    1000
% 1.88/0.99  --min_unsat_core                        false
% 1.88/0.99  --soft_assumptions                      false
% 1.88/0.99  --soft_lemma_size                       3
% 1.88/0.99  --prop_impl_unit_size                   0
% 1.88/0.99  --prop_impl_unit                        []
% 1.88/0.99  --share_sel_clauses                     true
% 1.88/0.99  --reset_solvers                         false
% 1.88/0.99  --bc_imp_inh                            [conj_cone]
% 1.88/0.99  --conj_cone_tolerance                   3.
% 1.88/0.99  --extra_neg_conj                        none
% 1.88/0.99  --large_theory_mode                     true
% 1.88/0.99  --prolific_symb_bound                   200
% 1.88/0.99  --lt_threshold                          2000
% 1.88/0.99  --clause_weak_htbl                      true
% 1.88/0.99  --gc_record_bc_elim                     false
% 1.88/0.99  
% 1.88/0.99  ------ Preprocessing Options
% 1.88/0.99  
% 1.88/0.99  --preprocessing_flag                    true
% 1.88/0.99  --time_out_prep_mult                    0.1
% 1.88/0.99  --splitting_mode                        input
% 1.88/0.99  --splitting_grd                         true
% 1.88/0.99  --splitting_cvd                         false
% 1.88/0.99  --splitting_cvd_svl                     false
% 1.88/0.99  --splitting_nvd                         32
% 1.88/0.99  --sub_typing                            true
% 1.88/0.99  --prep_gs_sim                           true
% 1.88/0.99  --prep_unflatten                        true
% 1.88/0.99  --prep_res_sim                          true
% 1.88/0.99  --prep_upred                            true
% 1.88/0.99  --prep_sem_filter                       exhaustive
% 1.88/0.99  --prep_sem_filter_out                   false
% 1.88/0.99  --pred_elim                             true
% 1.88/0.99  --res_sim_input                         true
% 1.88/0.99  --eq_ax_congr_red                       true
% 1.88/0.99  --pure_diseq_elim                       true
% 1.88/0.99  --brand_transform                       false
% 1.88/0.99  --non_eq_to_eq                          false
% 1.88/0.99  --prep_def_merge                        true
% 1.88/0.99  --prep_def_merge_prop_impl              false
% 1.88/0.99  --prep_def_merge_mbd                    true
% 1.88/0.99  --prep_def_merge_tr_red                 false
% 1.88/0.99  --prep_def_merge_tr_cl                  false
% 1.88/0.99  --smt_preprocessing                     true
% 1.88/0.99  --smt_ac_axioms                         fast
% 1.88/0.99  --preprocessed_out                      false
% 1.88/0.99  --preprocessed_stats                    false
% 1.88/0.99  
% 1.88/0.99  ------ Abstraction refinement Options
% 1.88/0.99  
% 1.88/0.99  --abstr_ref                             []
% 1.88/0.99  --abstr_ref_prep                        false
% 1.88/0.99  --abstr_ref_until_sat                   false
% 1.88/0.99  --abstr_ref_sig_restrict                funpre
% 1.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.88/0.99  --abstr_ref_under                       []
% 1.88/0.99  
% 1.88/0.99  ------ SAT Options
% 1.88/0.99  
% 1.88/0.99  --sat_mode                              false
% 1.88/0.99  --sat_fm_restart_options                ""
% 1.88/0.99  --sat_gr_def                            false
% 1.88/0.99  --sat_epr_types                         true
% 1.88/0.99  --sat_non_cyclic_types                  false
% 1.88/0.99  --sat_finite_models                     false
% 1.88/0.99  --sat_fm_lemmas                         false
% 1.88/0.99  --sat_fm_prep                           false
% 1.88/0.99  --sat_fm_uc_incr                        true
% 1.88/0.99  --sat_out_model                         small
% 1.88/0.99  --sat_out_clauses                       false
% 1.88/0.99  
% 1.88/0.99  ------ QBF Options
% 1.88/0.99  
% 1.88/0.99  --qbf_mode                              false
% 1.88/0.99  --qbf_elim_univ                         false
% 1.88/0.99  --qbf_dom_inst                          none
% 1.88/0.99  --qbf_dom_pre_inst                      false
% 1.88/0.99  --qbf_sk_in                             false
% 1.88/0.99  --qbf_pred_elim                         true
% 1.88/0.99  --qbf_split                             512
% 1.88/0.99  
% 1.88/0.99  ------ BMC1 Options
% 1.88/0.99  
% 1.88/0.99  --bmc1_incremental                      false
% 1.88/0.99  --bmc1_axioms                           reachable_all
% 1.88/0.99  --bmc1_min_bound                        0
% 1.88/0.99  --bmc1_max_bound                        -1
% 1.88/0.99  --bmc1_max_bound_default                -1
% 1.88/0.99  --bmc1_symbol_reachability              true
% 1.88/0.99  --bmc1_property_lemmas                  false
% 1.88/0.99  --bmc1_k_induction                      false
% 1.88/0.99  --bmc1_non_equiv_states                 false
% 1.88/0.99  --bmc1_deadlock                         false
% 1.88/0.99  --bmc1_ucm                              false
% 1.88/0.99  --bmc1_add_unsat_core                   none
% 1.88/0.99  --bmc1_unsat_core_children              false
% 1.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.88/0.99  --bmc1_out_stat                         full
% 1.88/0.99  --bmc1_ground_init                      false
% 1.88/0.99  --bmc1_pre_inst_next_state              false
% 1.88/0.99  --bmc1_pre_inst_state                   false
% 1.88/0.99  --bmc1_pre_inst_reach_state             false
% 1.88/0.99  --bmc1_out_unsat_core                   false
% 1.88/0.99  --bmc1_aig_witness_out                  false
% 1.88/0.99  --bmc1_verbose                          false
% 1.88/0.99  --bmc1_dump_clauses_tptp                false
% 1.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.88/0.99  --bmc1_dump_file                        -
% 1.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.88/0.99  --bmc1_ucm_extend_mode                  1
% 1.88/0.99  --bmc1_ucm_init_mode                    2
% 1.88/0.99  --bmc1_ucm_cone_mode                    none
% 1.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.88/0.99  --bmc1_ucm_relax_model                  4
% 1.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.88/0.99  --bmc1_ucm_layered_model                none
% 1.88/0.99  --bmc1_ucm_max_lemma_size               10
% 1.88/0.99  
% 1.88/0.99  ------ AIG Options
% 1.88/0.99  
% 1.88/0.99  --aig_mode                              false
% 1.88/0.99  
% 1.88/0.99  ------ Instantiation Options
% 1.88/0.99  
% 1.88/0.99  --instantiation_flag                    true
% 1.88/0.99  --inst_sos_flag                         false
% 1.88/0.99  --inst_sos_phase                        true
% 1.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.88/0.99  --inst_lit_sel_side                     num_symb
% 1.88/0.99  --inst_solver_per_active                1400
% 1.88/0.99  --inst_solver_calls_frac                1.
% 1.88/0.99  --inst_passive_queue_type               priority_queues
% 1.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.88/0.99  --inst_passive_queues_freq              [25;2]
% 1.88/0.99  --inst_dismatching                      true
% 1.88/0.99  --inst_eager_unprocessed_to_passive     true
% 1.88/0.99  --inst_prop_sim_given                   true
% 1.88/0.99  --inst_prop_sim_new                     false
% 1.88/0.99  --inst_subs_new                         false
% 1.88/0.99  --inst_eq_res_simp                      false
% 1.88/0.99  --inst_subs_given                       false
% 1.88/0.99  --inst_orphan_elimination               true
% 1.88/0.99  --inst_learning_loop_flag               true
% 1.88/0.99  --inst_learning_start                   3000
% 1.88/0.99  --inst_learning_factor                  2
% 1.88/0.99  --inst_start_prop_sim_after_learn       3
% 1.88/0.99  --inst_sel_renew                        solver
% 1.88/0.99  --inst_lit_activity_flag                true
% 1.88/0.99  --inst_restr_to_given                   false
% 1.88/0.99  --inst_activity_threshold               500
% 1.88/0.99  --inst_out_proof                        true
% 1.88/0.99  
% 1.88/0.99  ------ Resolution Options
% 1.88/0.99  
% 1.88/0.99  --resolution_flag                       true
% 1.88/0.99  --res_lit_sel                           adaptive
% 1.88/0.99  --res_lit_sel_side                      none
% 1.88/0.99  --res_ordering                          kbo
% 1.88/0.99  --res_to_prop_solver                    active
% 1.88/0.99  --res_prop_simpl_new                    false
% 1.88/0.99  --res_prop_simpl_given                  true
% 1.88/0.99  --res_passive_queue_type                priority_queues
% 1.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.88/0.99  --res_passive_queues_freq               [15;5]
% 1.88/0.99  --res_forward_subs                      full
% 1.88/0.99  --res_backward_subs                     full
% 1.88/0.99  --res_forward_subs_resolution           true
% 1.88/0.99  --res_backward_subs_resolution          true
% 1.88/0.99  --res_orphan_elimination                true
% 1.88/0.99  --res_time_limit                        2.
% 1.88/0.99  --res_out_proof                         true
% 1.88/0.99  
% 1.88/0.99  ------ Superposition Options
% 1.88/0.99  
% 1.88/0.99  --superposition_flag                    true
% 1.88/0.99  --sup_passive_queue_type                priority_queues
% 1.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.88/0.99  --demod_completeness_check              fast
% 1.88/0.99  --demod_use_ground                      true
% 1.88/0.99  --sup_to_prop_solver                    passive
% 1.88/0.99  --sup_prop_simpl_new                    true
% 1.88/0.99  --sup_prop_simpl_given                  true
% 1.88/0.99  --sup_fun_splitting                     false
% 1.88/0.99  --sup_smt_interval                      50000
% 1.88/0.99  
% 1.88/0.99  ------ Superposition Simplification Setup
% 1.88/0.99  
% 1.88/0.99  --sup_indices_passive                   []
% 1.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.99  --sup_full_bw                           [BwDemod]
% 1.88/0.99  --sup_immed_triv                        [TrivRules]
% 1.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.99  --sup_immed_bw_main                     []
% 1.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/0.99  
% 1.88/0.99  ------ Combination Options
% 1.88/0.99  
% 1.88/0.99  --comb_res_mult                         3
% 1.88/0.99  --comb_sup_mult                         2
% 1.88/0.99  --comb_inst_mult                        10
% 1.88/0.99  
% 1.88/0.99  ------ Debug Options
% 1.88/0.99  
% 1.88/0.99  --dbg_backtrace                         false
% 1.88/0.99  --dbg_dump_prop_clauses                 false
% 1.88/0.99  --dbg_dump_prop_clauses_file            -
% 1.88/0.99  --dbg_out_stat                          false
% 1.88/0.99  ------ Parsing...
% 1.88/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.88/0.99  
% 1.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.88/0.99  
% 1.88/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.88/0.99  
% 1.88/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.88/0.99  ------ Proving...
% 1.88/0.99  ------ Problem Properties 
% 1.88/0.99  
% 1.88/0.99  
% 1.88/0.99  clauses                                 18
% 1.88/0.99  conjectures                             2
% 1.88/0.99  EPR                                     5
% 1.88/0.99  Horn                                    12
% 1.88/0.99  unary                                   3
% 1.88/0.99  binary                                  1
% 1.88/0.99  lits                                    58
% 1.88/0.99  lits eq                                 3
% 1.88/0.99  fd_pure                                 0
% 1.88/0.99  fd_pseudo                               0
% 1.88/0.99  fd_cond                                 0
% 1.88/0.99  fd_pseudo_cond                          0
% 1.88/0.99  AC symbols                              0
% 1.88/0.99  
% 1.88/0.99  ------ Schedule dynamic 5 is on 
% 1.88/0.99  
% 1.88/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.88/0.99  
% 1.88/0.99  
% 1.88/0.99  ------ 
% 1.88/0.99  Current options:
% 1.88/0.99  ------ 
% 1.88/0.99  
% 1.88/0.99  ------ Input Options
% 1.88/0.99  
% 1.88/0.99  --out_options                           all
% 1.88/0.99  --tptp_safe_out                         true
% 1.88/0.99  --problem_path                          ""
% 1.88/0.99  --include_path                          ""
% 1.88/0.99  --clausifier                            res/vclausify_rel
% 1.88/0.99  --clausifier_options                    --mode clausify
% 1.88/0.99  --stdin                                 false
% 1.88/0.99  --stats_out                             all
% 1.88/0.99  
% 1.88/0.99  ------ General Options
% 1.88/0.99  
% 1.88/0.99  --fof                                   false
% 1.88/0.99  --time_out_real                         305.
% 1.88/0.99  --time_out_virtual                      -1.
% 1.88/0.99  --symbol_type_check                     false
% 1.88/0.99  --clausify_out                          false
% 1.88/0.99  --sig_cnt_out                           false
% 1.88/0.99  --trig_cnt_out                          false
% 1.88/0.99  --trig_cnt_out_tolerance                1.
% 1.88/0.99  --trig_cnt_out_sk_spl                   false
% 1.88/0.99  --abstr_cl_out                          false
% 1.88/0.99  
% 1.88/0.99  ------ Global Options
% 1.88/0.99  
% 1.88/0.99  --schedule                              default
% 1.88/0.99  --add_important_lit                     false
% 1.88/0.99  --prop_solver_per_cl                    1000
% 1.88/0.99  --min_unsat_core                        false
% 1.88/0.99  --soft_assumptions                      false
% 1.88/0.99  --soft_lemma_size                       3
% 1.88/0.99  --prop_impl_unit_size                   0
% 1.88/0.99  --prop_impl_unit                        []
% 1.88/0.99  --share_sel_clauses                     true
% 1.88/0.99  --reset_solvers                         false
% 1.88/0.99  --bc_imp_inh                            [conj_cone]
% 1.88/0.99  --conj_cone_tolerance                   3.
% 1.88/0.99  --extra_neg_conj                        none
% 1.88/0.99  --large_theory_mode                     true
% 1.88/0.99  --prolific_symb_bound                   200
% 1.88/0.99  --lt_threshold                          2000
% 1.88/0.99  --clause_weak_htbl                      true
% 1.88/0.99  --gc_record_bc_elim                     false
% 1.88/0.99  
% 1.88/0.99  ------ Preprocessing Options
% 1.88/0.99  
% 1.88/0.99  --preprocessing_flag                    true
% 1.88/0.99  --time_out_prep_mult                    0.1
% 1.88/0.99  --splitting_mode                        input
% 1.88/0.99  --splitting_grd                         true
% 1.88/0.99  --splitting_cvd                         false
% 1.88/0.99  --splitting_cvd_svl                     false
% 1.88/0.99  --splitting_nvd                         32
% 1.88/0.99  --sub_typing                            true
% 1.88/0.99  --prep_gs_sim                           true
% 1.88/0.99  --prep_unflatten                        true
% 1.88/0.99  --prep_res_sim                          true
% 1.88/0.99  --prep_upred                            true
% 1.88/0.99  --prep_sem_filter                       exhaustive
% 1.88/0.99  --prep_sem_filter_out                   false
% 1.88/0.99  --pred_elim                             true
% 1.88/0.99  --res_sim_input                         true
% 1.88/0.99  --eq_ax_congr_red                       true
% 1.88/0.99  --pure_diseq_elim                       true
% 1.88/0.99  --brand_transform                       false
% 1.88/0.99  --non_eq_to_eq                          false
% 1.88/0.99  --prep_def_merge                        true
% 1.88/0.99  --prep_def_merge_prop_impl              false
% 1.88/0.99  --prep_def_merge_mbd                    true
% 1.88/0.99  --prep_def_merge_tr_red                 false
% 1.88/0.99  --prep_def_merge_tr_cl                  false
% 1.88/0.99  --smt_preprocessing                     true
% 1.88/0.99  --smt_ac_axioms                         fast
% 1.88/0.99  --preprocessed_out                      false
% 1.88/0.99  --preprocessed_stats                    false
% 1.88/0.99  
% 1.88/0.99  ------ Abstraction refinement Options
% 1.88/0.99  
% 1.88/0.99  --abstr_ref                             []
% 1.88/0.99  --abstr_ref_prep                        false
% 1.88/0.99  --abstr_ref_until_sat                   false
% 1.88/0.99  --abstr_ref_sig_restrict                funpre
% 1.88/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.88/0.99  --abstr_ref_under                       []
% 1.88/0.99  
% 1.88/0.99  ------ SAT Options
% 1.88/0.99  
% 1.88/0.99  --sat_mode                              false
% 1.88/0.99  --sat_fm_restart_options                ""
% 1.88/0.99  --sat_gr_def                            false
% 1.88/0.99  --sat_epr_types                         true
% 1.88/0.99  --sat_non_cyclic_types                  false
% 1.88/0.99  --sat_finite_models                     false
% 1.88/0.99  --sat_fm_lemmas                         false
% 1.88/0.99  --sat_fm_prep                           false
% 1.88/0.99  --sat_fm_uc_incr                        true
% 1.88/0.99  --sat_out_model                         small
% 1.88/0.99  --sat_out_clauses                       false
% 1.88/0.99  
% 1.88/0.99  ------ QBF Options
% 1.88/0.99  
% 1.88/0.99  --qbf_mode                              false
% 1.88/0.99  --qbf_elim_univ                         false
% 1.88/0.99  --qbf_dom_inst                          none
% 1.88/0.99  --qbf_dom_pre_inst                      false
% 1.88/0.99  --qbf_sk_in                             false
% 1.88/0.99  --qbf_pred_elim                         true
% 1.88/0.99  --qbf_split                             512
% 1.88/0.99  
% 1.88/0.99  ------ BMC1 Options
% 1.88/0.99  
% 1.88/0.99  --bmc1_incremental                      false
% 1.88/0.99  --bmc1_axioms                           reachable_all
% 1.88/0.99  --bmc1_min_bound                        0
% 1.88/0.99  --bmc1_max_bound                        -1
% 1.88/0.99  --bmc1_max_bound_default                -1
% 1.88/0.99  --bmc1_symbol_reachability              true
% 1.88/0.99  --bmc1_property_lemmas                  false
% 1.88/0.99  --bmc1_k_induction                      false
% 1.88/0.99  --bmc1_non_equiv_states                 false
% 1.88/0.99  --bmc1_deadlock                         false
% 1.88/0.99  --bmc1_ucm                              false
% 1.88/0.99  --bmc1_add_unsat_core                   none
% 1.88/0.99  --bmc1_unsat_core_children              false
% 1.88/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.88/0.99  --bmc1_out_stat                         full
% 1.88/0.99  --bmc1_ground_init                      false
% 1.88/0.99  --bmc1_pre_inst_next_state              false
% 1.88/0.99  --bmc1_pre_inst_state                   false
% 1.88/0.99  --bmc1_pre_inst_reach_state             false
% 1.88/0.99  --bmc1_out_unsat_core                   false
% 1.88/0.99  --bmc1_aig_witness_out                  false
% 1.88/0.99  --bmc1_verbose                          false
% 1.88/0.99  --bmc1_dump_clauses_tptp                false
% 1.88/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.88/0.99  --bmc1_dump_file                        -
% 1.88/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.88/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.88/0.99  --bmc1_ucm_extend_mode                  1
% 1.88/0.99  --bmc1_ucm_init_mode                    2
% 1.88/0.99  --bmc1_ucm_cone_mode                    none
% 1.88/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.88/0.99  --bmc1_ucm_relax_model                  4
% 1.88/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.88/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.88/0.99  --bmc1_ucm_layered_model                none
% 1.88/0.99  --bmc1_ucm_max_lemma_size               10
% 1.88/0.99  
% 1.88/0.99  ------ AIG Options
% 1.88/0.99  
% 1.88/0.99  --aig_mode                              false
% 1.88/0.99  
% 1.88/0.99  ------ Instantiation Options
% 1.88/0.99  
% 1.88/0.99  --instantiation_flag                    true
% 1.88/0.99  --inst_sos_flag                         false
% 1.88/0.99  --inst_sos_phase                        true
% 1.88/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.88/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.88/0.99  --inst_lit_sel_side                     none
% 1.88/0.99  --inst_solver_per_active                1400
% 1.88/0.99  --inst_solver_calls_frac                1.
% 1.88/0.99  --inst_passive_queue_type               priority_queues
% 1.88/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.88/0.99  --inst_passive_queues_freq              [25;2]
% 1.88/0.99  --inst_dismatching                      true
% 1.88/0.99  --inst_eager_unprocessed_to_passive     true
% 1.88/0.99  --inst_prop_sim_given                   true
% 1.88/0.99  --inst_prop_sim_new                     false
% 1.88/0.99  --inst_subs_new                         false
% 1.88/0.99  --inst_eq_res_simp                      false
% 1.88/0.99  --inst_subs_given                       false
% 1.88/0.99  --inst_orphan_elimination               true
% 1.88/0.99  --inst_learning_loop_flag               true
% 1.88/0.99  --inst_learning_start                   3000
% 1.88/0.99  --inst_learning_factor                  2
% 1.88/0.99  --inst_start_prop_sim_after_learn       3
% 1.88/0.99  --inst_sel_renew                        solver
% 1.88/0.99  --inst_lit_activity_flag                true
% 1.88/0.99  --inst_restr_to_given                   false
% 1.88/0.99  --inst_activity_threshold               500
% 1.88/0.99  --inst_out_proof                        true
% 1.88/0.99  
% 1.88/0.99  ------ Resolution Options
% 1.88/0.99  
% 1.88/0.99  --resolution_flag                       false
% 1.88/0.99  --res_lit_sel                           adaptive
% 1.88/0.99  --res_lit_sel_side                      none
% 1.88/0.99  --res_ordering                          kbo
% 1.88/0.99  --res_to_prop_solver                    active
% 1.88/0.99  --res_prop_simpl_new                    false
% 1.88/0.99  --res_prop_simpl_given                  true
% 1.88/0.99  --res_passive_queue_type                priority_queues
% 1.88/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.88/0.99  --res_passive_queues_freq               [15;5]
% 1.88/0.99  --res_forward_subs                      full
% 1.88/0.99  --res_backward_subs                     full
% 1.88/0.99  --res_forward_subs_resolution           true
% 1.88/0.99  --res_backward_subs_resolution          true
% 1.88/0.99  --res_orphan_elimination                true
% 1.88/0.99  --res_time_limit                        2.
% 1.88/0.99  --res_out_proof                         true
% 1.88/0.99  
% 1.88/0.99  ------ Superposition Options
% 1.88/0.99  
% 1.88/0.99  --superposition_flag                    true
% 1.88/0.99  --sup_passive_queue_type                priority_queues
% 1.88/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.88/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.88/0.99  --demod_completeness_check              fast
% 1.88/0.99  --demod_use_ground                      true
% 1.88/0.99  --sup_to_prop_solver                    passive
% 1.88/0.99  --sup_prop_simpl_new                    true
% 1.88/0.99  --sup_prop_simpl_given                  true
% 1.88/0.99  --sup_fun_splitting                     false
% 1.88/0.99  --sup_smt_interval                      50000
% 1.88/0.99  
% 1.88/0.99  ------ Superposition Simplification Setup
% 1.88/0.99  
% 1.88/0.99  --sup_indices_passive                   []
% 1.88/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.88/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.99  --sup_full_bw                           [BwDemod]
% 1.88/0.99  --sup_immed_triv                        [TrivRules]
% 1.88/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.88/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.99  --sup_immed_bw_main                     []
% 1.88/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.88/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/0.99  
% 1.88/0.99  ------ Combination Options
% 1.88/0.99  
% 1.88/0.99  --comb_res_mult                         3
% 1.88/0.99  --comb_sup_mult                         2
% 1.88/0.99  --comb_inst_mult                        10
% 1.88/0.99  
% 1.88/0.99  ------ Debug Options
% 1.88/0.99  
% 1.88/0.99  --dbg_backtrace                         false
% 1.88/0.99  --dbg_dump_prop_clauses                 false
% 1.88/0.99  --dbg_dump_prop_clauses_file            -
% 1.88/0.99  --dbg_out_stat                          false
% 1.88/0.99  
% 1.88/0.99  
% 1.88/0.99  
% 1.88/0.99  
% 1.88/0.99  ------ Proving...
% 1.88/0.99  
% 1.88/0.99  
% 1.88/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 1.88/0.99  
% 1.88/0.99  ------ Building Model...Done
% 1.88/0.99  
% 1.88/0.99  %------ The model is defined over ground terms (initial term algebra).
% 1.88/0.99  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 1.88/0.99  %------ where \phi is a formula over the term algebra.
% 1.88/0.99  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 1.88/0.99  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 1.88/0.99  %------ See help for --sat_out_model for different model outputs.
% 1.88/0.99  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 1.88/0.99  %------ where the first argument stands for the sort ($i in the unsorted case)
% 1.88/0.99  % SZS output start Model for theBenchmark.p
% 1.88/0.99  
% 1.88/0.99  %------ Positive definition of equality_sorted 
% 1.88/0.99  fof(lit_def,axiom,
% 1.88/0.99      (! [X0_0,X0_2,X1_2] : 
% 1.88/0.99        ( equality_sorted(X0_0,X0_2,X1_2) <=>
% 1.88/0.99             (
% 1.88/0.99                (
% 1.88/0.99                  ( X0_0=$o & X1_2=X0_2 )
% 1.88/0.99                )
% 1.88/0.99  
% 1.88/0.99               | 
% 1.88/0.99                (
% 1.88/0.99                  ( X0_0=$i )
% 1.88/0.99                 &
% 1.88/0.99                  ( X0!=k1_zfmisc_1(X0) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X0!=k2_struct_0(X0) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X0!=sK7 )
% 1.88/0.99                 &
% 1.88/0.99                  ( X0!=u1_struct_0(sK5) | X1!=u1_struct_0(sK6) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X0!=sK6 )
% 1.88/0.99                 &
% 1.88/0.99                  ( X0!=u1_struct_0(sK6) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X0!=k2_struct_0(sK5) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X0!=k1_zfmisc_1(k2_struct_0(sK5)) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X0!=k2_struct_0(sK6) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X0!=k1_zfmisc_1(k2_struct_0(X0)) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X1!=k1_zfmisc_1(X1) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X1!=k2_struct_0(X1) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X1!=sK7 )
% 1.88/0.99                 &
% 1.88/0.99                  ( X1!=sK6 )
% 1.88/0.99                 &
% 1.88/0.99                  ( X1!=u1_struct_0(sK6) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X1!=k2_struct_0(sK5) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X1!=k1_zfmisc_1(k2_struct_0(X1)) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X1!=k1_zfmisc_1(k2_struct_0(sK5)) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X1!=k2_struct_0(sK6) )
% 1.88/0.99                )
% 1.88/0.99  
% 1.88/0.99               | 
% 1.88/0.99              ? [X2] : 
% 1.88/0.99                (
% 1.88/0.99                  ( X0_0=$i & X0=k1_zfmisc_1(X2) & X1=k1_zfmisc_1(X2) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X2!=k2_struct_0(sK5) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X2!=k2_struct_0(X2) )
% 1.88/0.99                )
% 1.88/0.99  
% 1.88/0.99               | 
% 1.88/0.99              ? [X2,X3] : 
% 1.88/0.99                (
% 1.88/0.99                  ( X0_0=$i & X0=k1_zfmisc_1(X2) & X1=k1_zfmisc_1(X3) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X2!=k2_struct_0(sK5) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X2!=k2_struct_0(X2) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X3!=k2_struct_0(sK5) )
% 1.88/0.99                 &
% 1.88/0.99                  ( X3!=k2_struct_0(X3) )
% 1.88/0.99                )
% 1.88/0.99  
% 1.88/0.99               | 
% 1.88/0.99                (
% 1.88/0.99                  ( X0_0=$i & X0=sK7 & X1=sK7 )
% 1.88/0.99                )
% 1.88/0.99  
% 1.88/0.99               | 
% 1.88/0.99                (
% 1.88/0.99                  ( X0_0=$i & X0=sK6 & X1=sK6 )
% 1.88/0.99                )
% 1.88/0.99  
% 1.88/0.99               | 
% 1.88/0.99                (
% 1.88/0.99                  ( X0_0=$i & X0=u1_struct_0(sK6) & X1=u1_struct_0(sK6) )
% 1.88/0.99                )
% 1.88/0.99  
% 1.88/0.99               | 
% 1.88/0.99                (
% 1.88/0.99                  ( X0_0=$i & X0=k2_struct_0(sK5) & X1=k2_struct_0(sK5) )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00               | 
% 1.88/1.00              ? [X2] : 
% 1.88/1.00                (
% 1.88/1.00                  ( X0_0=$i & X0=k2_struct_0(X2) & X1=k2_struct_0(X2) )
% 1.88/1.00                 &
% 1.88/1.00                  ( X2!=sK5 )
% 1.88/1.00                 &
% 1.88/1.00                  ( X2!=sK6 )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00               | 
% 1.88/1.00              ? [X2,X3] : 
% 1.88/1.00                (
% 1.88/1.00                  ( X0_0=$i & X0=u1_struct_0(X2) & X1=u1_struct_0(X3) )
% 1.88/1.00                 &
% 1.88/1.00                  ( X2!=sK5 | X3!=sK6 )
% 1.88/1.00                 &
% 1.88/1.00                  ( X2!=sK6 )
% 1.88/1.00                 &
% 1.88/1.00                  ( X3!=sK6 )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00               | 
% 1.88/1.00                (
% 1.88/1.00                  ( X0_0=$i & X0=k1_zfmisc_1(k2_struct_0(sK5)) & X1=k1_zfmisc_1(k2_struct_0(sK5)) )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00               | 
% 1.88/1.00              ? [X2] : 
% 1.88/1.00                (
% 1.88/1.00                  ( X0_0=$i & X0=k1_zfmisc_1(k2_struct_0(sK5)) & X1=k1_zfmisc_1(k2_struct_0(X2)) )
% 1.88/1.00                 &
% 1.88/1.00                  ( X2!=sK5 )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00               | 
% 1.88/1.00              ? [X2] : 
% 1.88/1.00                (
% 1.88/1.00                  ( X0_0=$i & X0=k1_zfmisc_1(k2_struct_0(X2)) & X1=k1_zfmisc_1(k2_struct_0(sK5)) )
% 1.88/1.00                 &
% 1.88/1.00                  ( X2!=sK5 )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00               | 
% 1.88/1.00              ? [X2] : 
% 1.88/1.00                (
% 1.88/1.00                  ( X0_0=$i & X0=k1_zfmisc_1(k2_struct_0(X2)) & X1=k1_zfmisc_1(k2_struct_0(X2)) )
% 1.88/1.00                 &
% 1.88/1.00                  ( X2!=sK5 )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00               | 
% 1.88/1.00              ? [X2,X3] : 
% 1.88/1.00                (
% 1.88/1.00                  ( X0_0=$i & X0=k1_zfmisc_1(k2_struct_0(X2)) & X1=k1_zfmisc_1(k2_struct_0(X3)) )
% 1.88/1.00                 &
% 1.88/1.00                  ( X2!=sK5 )
% 1.88/1.00                 &
% 1.88/1.00                  ( X3!=sK5 )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00               | 
% 1.88/1.00                (
% 1.88/1.00                  ( X0_0=$i & X0=k2_struct_0(sK6) & X1=k2_struct_0(sK6) )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00               | 
% 1.88/1.00              ? [X2,X3,X4,X5,X6,X7] : 
% 1.88/1.00                (
% 1.88/1.00                  ( X0_0=$i & X0=k9_subset_1(X2,X3,X4) & X1=k9_subset_1(X5,X6,X7) )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00               | 
% 1.88/1.00                (
% 1.88/1.00                  ( X0_0=$i & X1=X0 )
% 1.88/1.00                 &
% 1.88/1.00                  ( X0!=k1_zfmisc_1(X0) )
% 1.88/1.00                 &
% 1.88/1.00                  ( X0!=k2_struct_0(X0) )
% 1.88/1.00                 &
% 1.88/1.00                  ( X0!=sK7 )
% 1.88/1.00                 &
% 1.88/1.00                  ( X0!=sK6 )
% 1.88/1.00                 &
% 1.88/1.00                  ( X0!=u1_struct_0(sK6) )
% 1.88/1.00                 &
% 1.88/1.00                  ( X0!=k2_struct_0(sK5) )
% 1.88/1.00                 &
% 1.88/1.00                  ( X0!=k1_zfmisc_1(k2_struct_0(sK5)) )
% 1.88/1.00                 &
% 1.88/1.00                  ( X0!=k2_struct_0(sK6) )
% 1.88/1.00                 &
% 1.88/1.00                  ( X0!=k1_zfmisc_1(k2_struct_0(X0)) )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00             )
% 1.88/1.00        )
% 1.88/1.00      )
% 1.88/1.00     ).
% 1.88/1.00  
% 1.88/1.00  %------ Positive definition of m1_subset_1 
% 1.88/1.00  fof(lit_def,axiom,
% 1.88/1.00      (! [X0,X1] : 
% 1.88/1.00        ( m1_subset_1(X0,X1) <=>
% 1.88/1.00             (
% 1.88/1.00                (
% 1.88/1.00                  ( X0=sK7 & X1=u1_struct_0(sK6) )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00               | 
% 1.88/1.00                (
% 1.88/1.00                  ( X0=k2_struct_0(sK6) & X1=k1_zfmisc_1(k2_struct_0(sK5)) )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00               | 
% 1.88/1.00              ? [X2] : 
% 1.88/1.00                (
% 1.88/1.00                  ( X0=k2_struct_0(sK6) & X1=k1_zfmisc_1(k2_struct_0(X2)) )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00             )
% 1.88/1.00        )
% 1.88/1.00      )
% 1.88/1.00     ).
% 1.88/1.00  
% 1.88/1.00  %------ Positive definition of v1_xboole_0 
% 1.88/1.00  fof(lit_def,axiom,
% 1.88/1.00      (! [X0] : 
% 1.88/1.00        ( v1_xboole_0(X0) <=>
% 1.88/1.00            $false
% 1.88/1.00        )
% 1.88/1.00      )
% 1.88/1.00     ).
% 1.88/1.00  
% 1.88/1.00  %------ Positive definition of r2_hidden 
% 1.88/1.00  fof(lit_def,axiom,
% 1.88/1.00      (! [X0,X1] : 
% 1.88/1.00        ( r2_hidden(X0,X1) <=>
% 1.88/1.00             (
% 1.88/1.00                (
% 1.88/1.00                  ( X0=sK7 & X1=u1_struct_0(sK6) )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00               | 
% 1.88/1.00                (
% 1.88/1.00                  ( X0=k2_struct_0(sK6) & X1=k1_zfmisc_1(k2_struct_0(sK5)) )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00               | 
% 1.88/1.00              ? [X2] : 
% 1.88/1.00                (
% 1.88/1.00                  ( X0=k2_struct_0(sK6) & X1=k1_zfmisc_1(k2_struct_0(X2)) )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00             )
% 1.88/1.00        )
% 1.88/1.00      )
% 1.88/1.00     ).
% 1.88/1.00  
% 1.88/1.00  %------ Positive definition of r1_tarski 
% 1.88/1.00  fof(lit_def,axiom,
% 1.88/1.00      (! [X0,X1] : 
% 1.88/1.00        ( r1_tarski(X0,X1) <=>
% 1.88/1.00            $false
% 1.88/1.00        )
% 1.88/1.00      )
% 1.88/1.00     ).
% 1.88/1.00  
% 1.88/1.00  %------ Positive definition of m1_pre_topc 
% 1.88/1.00  fof(lit_def,axiom,
% 1.88/1.00      (! [X0,X1] : 
% 1.88/1.00        ( m1_pre_topc(X0,X1) <=>
% 1.88/1.00            $false
% 1.88/1.00        )
% 1.88/1.00      )
% 1.88/1.00     ).
% 1.88/1.00  
% 1.88/1.00  %------ Positive definition of sP0 
% 1.88/1.00  fof(lit_def,axiom,
% 1.88/1.00      (! [X0,X1] : 
% 1.88/1.00        ( sP0(X0,X1) <=>
% 1.88/1.00             (
% 1.88/1.00                (
% 1.88/1.00                  ( X0=sK6 )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00               | 
% 1.88/1.00                (
% 1.88/1.00                  ( X0=sK6 & X1=sK5 )
% 1.88/1.00                )
% 1.88/1.00  
% 1.88/1.00             )
% 1.88/1.00        )
% 1.88/1.00      )
% 1.88/1.00     ).
% 1.88/1.00  
% 1.88/1.00  %------ Positive definition of l1_pre_topc 
% 1.88/1.00  fof(lit_def,axiom,
% 1.88/1.00      (! [X0] : 
% 1.88/1.00        ( l1_pre_topc(X0) <=>
% 1.88/1.00            $false
% 1.88/1.00        )
% 1.88/1.00      )
% 1.88/1.00     ).
% 1.88/1.00  % SZS output end Model for theBenchmark.p
% 1.88/1.00  ------                               Statistics
% 1.88/1.00  
% 1.88/1.00  ------ General
% 1.88/1.00  
% 1.88/1.00  abstr_ref_over_cycles:                  0
% 1.88/1.00  abstr_ref_under_cycles:                 0
% 1.88/1.00  gc_basic_clause_elim:                   0
% 1.88/1.00  forced_gc_time:                         0
% 1.88/1.00  parsing_time:                           0.017
% 1.88/1.00  unif_index_cands_time:                  0.
% 1.88/1.00  unif_index_add_time:                    0.
% 1.88/1.00  orderings_time:                         0.
% 1.88/1.00  out_proof_time:                         0.
% 1.88/1.00  total_time:                             0.142
% 1.88/1.00  num_of_symbols:                         50
% 1.88/1.00  num_of_terms:                           2028
% 1.88/1.00  
% 1.88/1.00  ------ Preprocessing
% 1.88/1.00  
% 1.88/1.00  num_of_splits:                          0
% 1.88/1.00  num_of_split_atoms:                     0
% 1.88/1.00  num_of_reused_defs:                     0
% 1.88/1.00  num_eq_ax_congr_red:                    34
% 1.88/1.00  num_of_sem_filtered_clauses:            1
% 1.88/1.00  num_of_subtypes:                        0
% 1.88/1.00  monotx_restored_types:                  0
% 1.88/1.00  sat_num_of_epr_types:                   0
% 1.88/1.00  sat_num_of_non_cyclic_types:            0
% 1.88/1.00  sat_guarded_non_collapsed_types:        0
% 1.88/1.00  num_pure_diseq_elim:                    0
% 1.88/1.00  simp_replaced_by:                       0
% 1.88/1.00  res_preprocessed:                       96
% 1.88/1.00  prep_upred:                             0
% 1.88/1.00  prep_unflattend:                        36
% 1.88/1.00  smt_new_axioms:                         0
% 1.88/1.00  pred_elim_cands:                        4
% 1.88/1.00  pred_elim:                              4
% 1.88/1.00  pred_elim_cl:                           7
% 1.88/1.00  pred_elim_cycles:                       6
% 1.88/1.00  merged_defs:                            2
% 1.88/1.00  merged_defs_ncl:                        0
% 1.88/1.00  bin_hyper_res:                          2
% 1.88/1.00  prep_cycles:                            4
% 1.88/1.00  pred_elim_time:                         0.03
% 1.88/1.00  splitting_time:                         0.
% 1.88/1.00  sem_filter_time:                        0.
% 1.88/1.00  monotx_time:                            0.001
% 1.88/1.00  subtype_inf_time:                       0.
% 1.88/1.00  
% 1.88/1.00  ------ Problem properties
% 1.88/1.00  
% 1.88/1.00  clauses:                                18
% 1.88/1.00  conjectures:                            2
% 1.88/1.00  epr:                                    5
% 1.88/1.00  horn:                                   12
% 1.88/1.00  ground:                                 3
% 1.88/1.00  unary:                                  3
% 1.88/1.00  binary:                                 1
% 1.88/1.00  lits:                                   58
% 1.88/1.00  lits_eq:                                3
% 1.88/1.00  fd_pure:                                0
% 1.88/1.00  fd_pseudo:                              0
% 1.88/1.00  fd_cond:                                0
% 1.88/1.00  fd_pseudo_cond:                         0
% 1.88/1.00  ac_symbols:                             0
% 1.88/1.00  
% 1.88/1.00  ------ Propositional Solver
% 1.88/1.00  
% 1.88/1.00  prop_solver_calls:                      32
% 1.88/1.00  prop_fast_solver_calls:                 1074
% 1.88/1.00  smt_solver_calls:                       0
% 1.88/1.00  smt_fast_solver_calls:                  0
% 1.88/1.00  prop_num_of_clauses:                    652
% 1.88/1.00  prop_preprocess_simplified:             3536
% 1.88/1.00  prop_fo_subsumed:                       3
% 1.88/1.00  prop_solver_time:                       0.
% 1.88/1.00  smt_solver_time:                        0.
% 1.88/1.00  smt_fast_solver_time:                   0.
% 1.88/1.00  prop_fast_solver_time:                  0.
% 1.88/1.00  prop_unsat_core_time:                   0.
% 1.88/1.00  
% 1.88/1.00  ------ QBF
% 1.88/1.00  
% 1.88/1.00  qbf_q_res:                              0
% 1.88/1.00  qbf_num_tautologies:                    0
% 1.88/1.00  qbf_prep_cycles:                        0
% 1.88/1.00  
% 1.88/1.00  ------ BMC1
% 1.88/1.00  
% 1.88/1.00  bmc1_current_bound:                     -1
% 1.88/1.00  bmc1_last_solved_bound:                 -1
% 1.88/1.00  bmc1_unsat_core_size:                   -1
% 1.88/1.00  bmc1_unsat_core_parents_size:           -1
% 1.88/1.00  bmc1_merge_next_fun:                    0
% 1.88/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.88/1.00  
% 1.88/1.00  ------ Instantiation
% 1.88/1.00  
% 1.88/1.00  inst_num_of_clauses:                    165
% 1.88/1.00  inst_num_in_passive:                    0
% 1.88/1.00  inst_num_in_active:                     165
% 1.88/1.00  inst_num_in_unprocessed:                0
% 1.88/1.00  inst_num_of_loops:                      183
% 1.88/1.00  inst_num_of_learning_restarts:          0
% 1.88/1.00  inst_num_moves_active_passive:          5
% 1.88/1.00  inst_lit_activity:                      0
% 1.88/1.00  inst_lit_activity_moves:                0
% 1.88/1.00  inst_num_tautologies:                   0
% 1.88/1.00  inst_num_prop_implied:                  0
% 1.88/1.00  inst_num_existing_simplified:           0
% 1.88/1.00  inst_num_eq_res_simplified:             0
% 1.88/1.00  inst_num_child_elim:                    0
% 1.88/1.00  inst_num_of_dismatching_blockings:      65
% 1.88/1.00  inst_num_of_non_proper_insts:           292
% 1.88/1.00  inst_num_of_duplicates:                 0
% 1.88/1.00  inst_inst_num_from_inst_to_res:         0
% 1.88/1.00  inst_dismatching_checking_time:         0.
% 1.88/1.00  
% 1.88/1.00  ------ Resolution
% 1.88/1.00  
% 1.88/1.00  res_num_of_clauses:                     0
% 1.88/1.00  res_num_in_passive:                     0
% 1.88/1.00  res_num_in_active:                      0
% 1.88/1.00  res_num_of_loops:                       100
% 1.88/1.00  res_forward_subset_subsumed:            74
% 1.88/1.00  res_backward_subset_subsumed:           2
% 1.88/1.00  res_forward_subsumed:                   0
% 1.88/1.00  res_backward_subsumed:                  0
% 1.88/1.00  res_forward_subsumption_resolution:     0
% 1.88/1.00  res_backward_subsumption_resolution:    0
% 1.88/1.00  res_clause_to_clause_subsumption:       473
% 1.88/1.00  res_orphan_elimination:                 0
% 1.88/1.00  res_tautology_del:                      137
% 1.88/1.00  res_num_eq_res_simplified:              0
% 1.88/1.00  res_num_sel_changes:                    0
% 1.88/1.00  res_moves_from_active_to_pass:          0
% 1.88/1.00  
% 1.88/1.00  ------ Superposition
% 1.88/1.00  
% 1.88/1.00  sup_time_total:                         0.
% 1.88/1.00  sup_time_generating:                    0.
% 1.88/1.00  sup_time_sim_full:                      0.
% 1.88/1.00  sup_time_sim_immed:                     0.
% 1.88/1.00  
% 1.88/1.00  sup_num_of_clauses:                     61
% 1.88/1.00  sup_num_in_active:                      36
% 1.88/1.00  sup_num_in_passive:                     25
% 1.88/1.00  sup_num_of_loops:                       36
% 1.88/1.00  sup_fw_superposition:                   29
% 1.88/1.00  sup_bw_superposition:                   24
% 1.88/1.00  sup_immediate_simplified:               3
% 1.88/1.00  sup_given_eliminated:                   0
% 1.88/1.00  comparisons_done:                       0
% 1.88/1.00  comparisons_avoided:                    0
% 1.88/1.00  
% 1.88/1.00  ------ Simplifications
% 1.88/1.00  
% 1.88/1.00  
% 1.88/1.00  sim_fw_subset_subsumed:                 3
% 1.88/1.00  sim_bw_subset_subsumed:                 0
% 1.88/1.00  sim_fw_subsumed:                        0
% 1.88/1.00  sim_bw_subsumed:                        0
% 1.88/1.00  sim_fw_subsumption_res:                 1
% 1.88/1.00  sim_bw_subsumption_res:                 0
% 1.88/1.00  sim_tautology_del:                      7
% 1.88/1.00  sim_eq_tautology_del:                   0
% 1.88/1.00  sim_eq_res_simp:                        0
% 1.88/1.00  sim_fw_demodulated:                     0
% 1.88/1.00  sim_bw_demodulated:                     0
% 1.88/1.00  sim_light_normalised:                   0
% 1.88/1.00  sim_joinable_taut:                      0
% 1.88/1.00  sim_joinable_simp:                      0
% 1.88/1.00  sim_ac_normalised:                      0
% 1.88/1.00  sim_smt_subsumption:                    0
% 1.88/1.00  
%------------------------------------------------------------------------------
