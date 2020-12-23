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
% DateTime   : Thu Dec  3 11:46:55 EST 2020

% Result     : Theorem 0.49s
% Output     : CNFRefutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   50 (  88 expanded)
%              Number of clauses        :   31 (  40 expanded)
%              Number of leaves         :    9 (  22 expanded)
%              Depth                    :   13
%              Number of atoms          :  103 ( 211 expanded)
%              Number of equality atoms :   55 (  96 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1)
          & r1_tarski(X1,X2) )
     => ( k9_relat_1(X0,sK1) != k9_relat_1(k7_relat_1(X0,sK2),sK1)
        & r1_tarski(sK1,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1)
            & r1_tarski(X1,X2) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(sK0,X1) != k9_relat_1(k7_relat_1(sK0,X2),X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12,f11])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f18,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,(
    k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_5,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_112,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_215,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_112])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_4,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_62,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X2)
    | sK2 != X1
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_4])).

cnf(c_63,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,sK2),sK1) = k7_relat_1(X0,sK1) ),
    inference(unflattening,[status(thm)],[c_62])).

cnf(c_111,plain,
    ( ~ v1_relat_1(X0_36)
    | k7_relat_1(k7_relat_1(X0_36,sK2),sK1) = k7_relat_1(X0_36,sK1) ),
    inference(subtyping,[status(esa)],[c_63])).

cnf(c_216,plain,
    ( k7_relat_1(k7_relat_1(X0_36,sK2),sK1) = k7_relat_1(X0_36,sK1)
    | v1_relat_1(X0_36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_111])).

cnf(c_267,plain,
    ( k7_relat_1(k7_relat_1(sK0,sK2),sK1) = k7_relat_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_215,c_216])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_115,plain,
    ( ~ v1_relat_1(X0_36)
    | v1_relat_1(k7_relat_1(X0_36,X0_37)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_213,plain,
    ( v1_relat_1(X0_36) != iProver_top
    | v1_relat_1(k7_relat_1(X0_36,X0_37)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_115])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_114,plain,
    ( ~ v1_relat_1(X0_36)
    | k2_relat_1(k7_relat_1(X0_36,X0_37)) = k9_relat_1(X0_36,X0_37) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_214,plain,
    ( k2_relat_1(k7_relat_1(X0_36,X0_37)) = k9_relat_1(X0_36,X0_37)
    | v1_relat_1(X0_36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_114])).

cnf(c_465,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(X0_36,X0_37),X1_37)) = k9_relat_1(k7_relat_1(X0_36,X0_37),X1_37)
    | v1_relat_1(X0_36) != iProver_top ),
    inference(superposition,[status(thm)],[c_213,c_214])).

cnf(c_1071,plain,
    ( k2_relat_1(k7_relat_1(k7_relat_1(sK0,X0_37),X1_37)) = k9_relat_1(k7_relat_1(sK0,X0_37),X1_37) ),
    inference(superposition,[status(thm)],[c_215,c_465])).

cnf(c_1087,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k2_relat_1(k7_relat_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_267,c_1071])).

cnf(c_464,plain,
    ( k2_relat_1(k7_relat_1(sK0,X0_37)) = k9_relat_1(sK0,X0_37) ),
    inference(superposition,[status(thm)],[c_215,c_214])).

cnf(c_1088,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1087,c_464])).

cnf(c_120,plain,
    ( X0_38 != X1_38
    | X2_38 != X1_38
    | X2_38 = X0_38 ),
    theory(equality)).

cnf(c_245,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != X0_38
    | k9_relat_1(sK0,sK1) != X0_38
    | k9_relat_1(sK0,sK1) = k9_relat_1(k7_relat_1(sK0,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_120])).

cnf(c_250,plain,
    ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
    | k9_relat_1(sK0,sK1) = k9_relat_1(k7_relat_1(sK0,sK2),sK1)
    | k9_relat_1(sK0,sK1) != k9_relat_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_3,negated_conjecture,
    ( k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_113,negated_conjecture,
    ( k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_117,plain,
    ( X0_36 = X0_36 ),
    theory(equality)).

cnf(c_130,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_117])).

cnf(c_124,plain,
    ( k9_relat_1(X0_36,X0_37) = k9_relat_1(X1_36,X0_37)
    | X0_36 != X1_36 ),
    theory(equality)).

cnf(c_128,plain,
    ( k9_relat_1(sK0,sK1) = k9_relat_1(sK0,sK1)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_124])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1088,c_250,c_113,c_130,c_128])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.07  % Command    : iproveropt_run.sh %d %s
% 0.06/0.25  % Computer   : n005.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % WCLimit    : 600
% 0.06/0.25  % DateTime   : Tue Dec  1 17:23:47 EST 2020
% 0.06/0.25  % CPUTime    : 
% 0.06/0.25  % Running in FOF mode
% 0.49/0.83  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.49/0.83  
% 0.49/0.83  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.49/0.83  
% 0.49/0.83  ------  iProver source info
% 0.49/0.83  
% 0.49/0.83  git: date: 2020-06-30 10:37:57 +0100
% 0.49/0.83  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.49/0.83  git: non_committed_changes: false
% 0.49/0.83  git: last_make_outside_of_git: false
% 0.49/0.83  
% 0.49/0.83  ------ 
% 0.49/0.83  
% 0.49/0.83  ------ Input Options
% 0.49/0.83  
% 0.49/0.83  --out_options                           all
% 0.49/0.83  --tptp_safe_out                         true
% 0.49/0.83  --problem_path                          ""
% 0.49/0.83  --include_path                          ""
% 0.49/0.83  --clausifier                            res/vclausify_rel
% 0.49/0.83  --clausifier_options                    --mode clausify
% 0.49/0.83  --stdin                                 false
% 0.49/0.83  --stats_out                             all
% 0.49/0.83  
% 0.49/0.83  ------ General Options
% 0.49/0.83  
% 0.49/0.83  --fof                                   false
% 0.49/0.83  --time_out_real                         305.
% 0.49/0.83  --time_out_virtual                      -1.
% 0.49/0.83  --symbol_type_check                     false
% 0.49/0.83  --clausify_out                          false
% 0.49/0.83  --sig_cnt_out                           false
% 0.49/0.83  --trig_cnt_out                          false
% 0.49/0.83  --trig_cnt_out_tolerance                1.
% 0.49/0.83  --trig_cnt_out_sk_spl                   false
% 0.49/0.83  --abstr_cl_out                          false
% 0.49/0.83  
% 0.49/0.83  ------ Global Options
% 0.49/0.83  
% 0.49/0.83  --schedule                              default
% 0.49/0.83  --add_important_lit                     false
% 0.49/0.83  --prop_solver_per_cl                    1000
% 0.49/0.83  --min_unsat_core                        false
% 0.49/0.83  --soft_assumptions                      false
% 0.49/0.83  --soft_lemma_size                       3
% 0.49/0.83  --prop_impl_unit_size                   0
% 0.49/0.83  --prop_impl_unit                        []
% 0.49/0.83  --share_sel_clauses                     true
% 0.49/0.83  --reset_solvers                         false
% 0.49/0.83  --bc_imp_inh                            [conj_cone]
% 0.49/0.83  --conj_cone_tolerance                   3.
% 0.49/0.83  --extra_neg_conj                        none
% 0.49/0.83  --large_theory_mode                     true
% 0.49/0.83  --prolific_symb_bound                   200
% 0.49/0.83  --lt_threshold                          2000
% 0.49/0.83  --clause_weak_htbl                      true
% 0.49/0.83  --gc_record_bc_elim                     false
% 0.49/0.83  
% 0.49/0.83  ------ Preprocessing Options
% 0.49/0.83  
% 0.49/0.83  --preprocessing_flag                    true
% 0.49/0.83  --time_out_prep_mult                    0.1
% 0.49/0.83  --splitting_mode                        input
% 0.49/0.83  --splitting_grd                         true
% 0.49/0.83  --splitting_cvd                         false
% 0.49/0.83  --splitting_cvd_svl                     false
% 0.49/0.83  --splitting_nvd                         32
% 0.49/0.83  --sub_typing                            true
% 0.49/0.83  --prep_gs_sim                           true
% 0.49/0.83  --prep_unflatten                        true
% 0.49/0.83  --prep_res_sim                          true
% 0.49/0.83  --prep_upred                            true
% 0.49/0.83  --prep_sem_filter                       exhaustive
% 0.49/0.83  --prep_sem_filter_out                   false
% 0.49/0.83  --pred_elim                             true
% 0.49/0.83  --res_sim_input                         true
% 0.49/0.83  --eq_ax_congr_red                       true
% 0.49/0.83  --pure_diseq_elim                       true
% 0.49/0.83  --brand_transform                       false
% 0.49/0.83  --non_eq_to_eq                          false
% 0.49/0.83  --prep_def_merge                        true
% 0.49/0.83  --prep_def_merge_prop_impl              false
% 0.49/0.83  --prep_def_merge_mbd                    true
% 0.49/0.83  --prep_def_merge_tr_red                 false
% 0.49/0.83  --prep_def_merge_tr_cl                  false
% 0.49/0.83  --smt_preprocessing                     true
% 0.49/0.83  --smt_ac_axioms                         fast
% 0.49/0.83  --preprocessed_out                      false
% 0.49/0.83  --preprocessed_stats                    false
% 0.49/0.83  
% 0.49/0.83  ------ Abstraction refinement Options
% 0.49/0.83  
% 0.49/0.83  --abstr_ref                             []
% 0.49/0.83  --abstr_ref_prep                        false
% 0.49/0.83  --abstr_ref_until_sat                   false
% 0.49/0.83  --abstr_ref_sig_restrict                funpre
% 0.49/0.83  --abstr_ref_af_restrict_to_split_sk     false
% 0.49/0.83  --abstr_ref_under                       []
% 0.49/0.83  
% 0.49/0.83  ------ SAT Options
% 0.49/0.83  
% 0.49/0.83  --sat_mode                              false
% 0.49/0.83  --sat_fm_restart_options                ""
% 0.49/0.83  --sat_gr_def                            false
% 0.49/0.83  --sat_epr_types                         true
% 0.49/0.83  --sat_non_cyclic_types                  false
% 0.49/0.83  --sat_finite_models                     false
% 0.49/0.83  --sat_fm_lemmas                         false
% 0.49/0.83  --sat_fm_prep                           false
% 0.49/0.83  --sat_fm_uc_incr                        true
% 0.49/0.83  --sat_out_model                         small
% 0.49/0.83  --sat_out_clauses                       false
% 0.49/0.83  
% 0.49/0.83  ------ QBF Options
% 0.49/0.83  
% 0.49/0.83  --qbf_mode                              false
% 0.49/0.83  --qbf_elim_univ                         false
% 0.49/0.83  --qbf_dom_inst                          none
% 0.49/0.83  --qbf_dom_pre_inst                      false
% 0.49/0.83  --qbf_sk_in                             false
% 0.49/0.83  --qbf_pred_elim                         true
% 0.49/0.83  --qbf_split                             512
% 0.49/0.83  
% 0.49/0.83  ------ BMC1 Options
% 0.49/0.83  
% 0.49/0.83  --bmc1_incremental                      false
% 0.49/0.83  --bmc1_axioms                           reachable_all
% 0.49/0.83  --bmc1_min_bound                        0
% 0.49/0.83  --bmc1_max_bound                        -1
% 0.49/0.83  --bmc1_max_bound_default                -1
% 0.49/0.83  --bmc1_symbol_reachability              true
% 0.49/0.83  --bmc1_property_lemmas                  false
% 0.49/0.83  --bmc1_k_induction                      false
% 0.49/0.83  --bmc1_non_equiv_states                 false
% 0.49/0.83  --bmc1_deadlock                         false
% 0.49/0.83  --bmc1_ucm                              false
% 0.49/0.83  --bmc1_add_unsat_core                   none
% 0.49/0.83  --bmc1_unsat_core_children              false
% 0.49/0.83  --bmc1_unsat_core_extrapolate_axioms    false
% 0.49/0.83  --bmc1_out_stat                         full
% 0.49/0.83  --bmc1_ground_init                      false
% 0.49/0.83  --bmc1_pre_inst_next_state              false
% 0.49/0.83  --bmc1_pre_inst_state                   false
% 0.49/0.83  --bmc1_pre_inst_reach_state             false
% 0.49/0.83  --bmc1_out_unsat_core                   false
% 0.49/0.83  --bmc1_aig_witness_out                  false
% 0.49/0.83  --bmc1_verbose                          false
% 0.49/0.83  --bmc1_dump_clauses_tptp                false
% 0.49/0.83  --bmc1_dump_unsat_core_tptp             false
% 0.49/0.83  --bmc1_dump_file                        -
% 0.49/0.83  --bmc1_ucm_expand_uc_limit              128
% 0.49/0.83  --bmc1_ucm_n_expand_iterations          6
% 0.49/0.83  --bmc1_ucm_extend_mode                  1
% 0.49/0.83  --bmc1_ucm_init_mode                    2
% 0.49/0.83  --bmc1_ucm_cone_mode                    none
% 0.49/0.83  --bmc1_ucm_reduced_relation_type        0
% 0.49/0.83  --bmc1_ucm_relax_model                  4
% 0.49/0.83  --bmc1_ucm_full_tr_after_sat            true
% 0.49/0.83  --bmc1_ucm_expand_neg_assumptions       false
% 0.49/0.83  --bmc1_ucm_layered_model                none
% 0.49/0.83  --bmc1_ucm_max_lemma_size               10
% 0.49/0.83  
% 0.49/0.83  ------ AIG Options
% 0.49/0.83  
% 0.49/0.83  --aig_mode                              false
% 0.49/0.83  
% 0.49/0.83  ------ Instantiation Options
% 0.49/0.83  
% 0.49/0.83  --instantiation_flag                    true
% 0.49/0.83  --inst_sos_flag                         false
% 0.49/0.83  --inst_sos_phase                        true
% 0.49/0.83  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.49/0.83  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.49/0.83  --inst_lit_sel_side                     num_symb
% 0.49/0.83  --inst_solver_per_active                1400
% 0.49/0.83  --inst_solver_calls_frac                1.
% 0.49/0.83  --inst_passive_queue_type               priority_queues
% 0.49/0.83  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.49/0.83  --inst_passive_queues_freq              [25;2]
% 0.49/0.83  --inst_dismatching                      true
% 0.49/0.83  --inst_eager_unprocessed_to_passive     true
% 0.49/0.83  --inst_prop_sim_given                   true
% 0.49/0.83  --inst_prop_sim_new                     false
% 0.49/0.83  --inst_subs_new                         false
% 0.49/0.83  --inst_eq_res_simp                      false
% 0.49/0.83  --inst_subs_given                       false
% 0.49/0.83  --inst_orphan_elimination               true
% 0.49/0.83  --inst_learning_loop_flag               true
% 0.49/0.83  --inst_learning_start                   3000
% 0.49/0.83  --inst_learning_factor                  2
% 0.49/0.83  --inst_start_prop_sim_after_learn       3
% 0.49/0.83  --inst_sel_renew                        solver
% 0.49/0.83  --inst_lit_activity_flag                true
% 0.49/0.83  --inst_restr_to_given                   false
% 0.49/0.83  --inst_activity_threshold               500
% 0.49/0.83  --inst_out_proof                        true
% 0.49/0.83  
% 0.49/0.83  ------ Resolution Options
% 0.49/0.83  
% 0.49/0.83  --resolution_flag                       true
% 0.49/0.83  --res_lit_sel                           adaptive
% 0.49/0.83  --res_lit_sel_side                      none
% 0.49/0.83  --res_ordering                          kbo
% 0.49/0.83  --res_to_prop_solver                    active
% 0.49/0.83  --res_prop_simpl_new                    false
% 0.49/0.83  --res_prop_simpl_given                  true
% 0.49/0.83  --res_passive_queue_type                priority_queues
% 0.49/0.83  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.49/0.83  --res_passive_queues_freq               [15;5]
% 0.49/0.83  --res_forward_subs                      full
% 0.49/0.83  --res_backward_subs                     full
% 0.49/0.83  --res_forward_subs_resolution           true
% 0.49/0.83  --res_backward_subs_resolution          true
% 0.49/0.83  --res_orphan_elimination                true
% 0.49/0.83  --res_time_limit                        2.
% 0.49/0.83  --res_out_proof                         true
% 0.49/0.83  
% 0.49/0.83  ------ Superposition Options
% 0.49/0.83  
% 0.49/0.83  --superposition_flag                    true
% 0.49/0.83  --sup_passive_queue_type                priority_queues
% 0.49/0.83  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.49/0.83  --sup_passive_queues_freq               [8;1;4]
% 0.49/0.83  --demod_completeness_check              fast
% 0.49/0.83  --demod_use_ground                      true
% 0.49/0.83  --sup_to_prop_solver                    passive
% 0.49/0.83  --sup_prop_simpl_new                    true
% 0.49/0.83  --sup_prop_simpl_given                  true
% 0.49/0.83  --sup_fun_splitting                     false
% 0.49/0.83  --sup_smt_interval                      50000
% 0.49/0.83  
% 0.49/0.83  ------ Superposition Simplification Setup
% 0.49/0.83  
% 0.49/0.83  --sup_indices_passive                   []
% 0.49/0.83  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.49/0.83  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.49/0.83  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.49/0.83  --sup_full_triv                         [TrivRules;PropSubs]
% 0.49/0.83  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.49/0.83  --sup_full_bw                           [BwDemod]
% 0.49/0.83  --sup_immed_triv                        [TrivRules]
% 0.49/0.83  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.49/0.83  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.49/0.83  --sup_immed_bw_main                     []
% 0.49/0.83  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.49/0.83  --sup_input_triv                        [Unflattening;TrivRules]
% 0.49/0.83  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.49/0.83  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.49/0.83  
% 0.49/0.83  ------ Combination Options
% 0.49/0.83  
% 0.49/0.83  --comb_res_mult                         3
% 0.49/0.83  --comb_sup_mult                         2
% 0.49/0.83  --comb_inst_mult                        10
% 0.49/0.83  
% 0.49/0.83  ------ Debug Options
% 0.49/0.83  
% 0.49/0.83  --dbg_backtrace                         false
% 0.49/0.83  --dbg_dump_prop_clauses                 false
% 0.49/0.83  --dbg_dump_prop_clauses_file            -
% 0.49/0.83  --dbg_out_stat                          false
% 0.49/0.83  ------ Parsing...
% 0.49/0.83  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.49/0.83  
% 0.49/0.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 0.49/0.83  
% 0.49/0.83  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.49/0.83  
% 0.49/0.83  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.49/0.83  ------ Proving...
% 0.49/0.83  ------ Problem Properties 
% 0.49/0.83  
% 0.49/0.83  
% 0.49/0.83  clauses                                 5
% 0.49/0.83  conjectures                             2
% 0.49/0.83  EPR                                     1
% 0.49/0.83  Horn                                    5
% 0.49/0.83  unary                                   2
% 0.49/0.83  binary                                  3
% 0.49/0.83  lits                                    8
% 0.49/0.83  lits eq                                 3
% 0.49/0.83  fd_pure                                 0
% 0.49/0.83  fd_pseudo                               0
% 0.49/0.83  fd_cond                                 0
% 0.49/0.83  fd_pseudo_cond                          0
% 0.49/0.83  AC symbols                              0
% 0.49/0.83  
% 0.49/0.83  ------ Schedule dynamic 5 is on 
% 0.49/0.83  
% 0.49/0.83  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.49/0.83  
% 0.49/0.83  
% 0.49/0.83  ------ 
% 0.49/0.83  Current options:
% 0.49/0.83  ------ 
% 0.49/0.83  
% 0.49/0.83  ------ Input Options
% 0.49/0.83  
% 0.49/0.83  --out_options                           all
% 0.49/0.83  --tptp_safe_out                         true
% 0.49/0.83  --problem_path                          ""
% 0.49/0.83  --include_path                          ""
% 0.49/0.83  --clausifier                            res/vclausify_rel
% 0.49/0.83  --clausifier_options                    --mode clausify
% 0.49/0.83  --stdin                                 false
% 0.49/0.83  --stats_out                             all
% 0.49/0.83  
% 0.49/0.83  ------ General Options
% 0.49/0.83  
% 0.49/0.83  --fof                                   false
% 0.49/0.83  --time_out_real                         305.
% 0.49/0.83  --time_out_virtual                      -1.
% 0.49/0.83  --symbol_type_check                     false
% 0.49/0.83  --clausify_out                          false
% 0.49/0.83  --sig_cnt_out                           false
% 0.49/0.83  --trig_cnt_out                          false
% 0.49/0.83  --trig_cnt_out_tolerance                1.
% 0.49/0.83  --trig_cnt_out_sk_spl                   false
% 0.49/0.83  --abstr_cl_out                          false
% 0.49/0.83  
% 0.49/0.83  ------ Global Options
% 0.49/0.83  
% 0.49/0.83  --schedule                              default
% 0.49/0.83  --add_important_lit                     false
% 0.49/0.83  --prop_solver_per_cl                    1000
% 0.49/0.83  --min_unsat_core                        false
% 0.49/0.83  --soft_assumptions                      false
% 0.49/0.83  --soft_lemma_size                       3
% 0.49/0.83  --prop_impl_unit_size                   0
% 0.49/0.83  --prop_impl_unit                        []
% 0.49/0.83  --share_sel_clauses                     true
% 0.49/0.83  --reset_solvers                         false
% 0.49/0.83  --bc_imp_inh                            [conj_cone]
% 0.49/0.83  --conj_cone_tolerance                   3.
% 0.49/0.83  --extra_neg_conj                        none
% 0.49/0.83  --large_theory_mode                     true
% 0.49/0.83  --prolific_symb_bound                   200
% 0.49/0.83  --lt_threshold                          2000
% 0.49/0.83  --clause_weak_htbl                      true
% 0.49/0.83  --gc_record_bc_elim                     false
% 0.49/0.83  
% 0.49/0.83  ------ Preprocessing Options
% 0.49/0.83  
% 0.49/0.83  --preprocessing_flag                    true
% 0.49/0.83  --time_out_prep_mult                    0.1
% 0.49/0.83  --splitting_mode                        input
% 0.49/0.83  --splitting_grd                         true
% 0.49/0.83  --splitting_cvd                         false
% 0.49/0.83  --splitting_cvd_svl                     false
% 0.49/0.83  --splitting_nvd                         32
% 0.49/0.83  --sub_typing                            true
% 0.49/0.83  --prep_gs_sim                           true
% 0.49/0.83  --prep_unflatten                        true
% 0.49/0.83  --prep_res_sim                          true
% 0.49/0.83  --prep_upred                            true
% 0.49/0.83  --prep_sem_filter                       exhaustive
% 0.49/0.83  --prep_sem_filter_out                   false
% 0.49/0.83  --pred_elim                             true
% 0.49/0.83  --res_sim_input                         true
% 0.49/0.83  --eq_ax_congr_red                       true
% 0.49/0.83  --pure_diseq_elim                       true
% 0.49/0.83  --brand_transform                       false
% 0.49/0.83  --non_eq_to_eq                          false
% 0.49/0.83  --prep_def_merge                        true
% 0.49/0.83  --prep_def_merge_prop_impl              false
% 0.49/0.83  --prep_def_merge_mbd                    true
% 0.49/0.83  --prep_def_merge_tr_red                 false
% 0.49/0.83  --prep_def_merge_tr_cl                  false
% 0.49/0.83  --smt_preprocessing                     true
% 0.49/0.83  --smt_ac_axioms                         fast
% 0.49/0.83  --preprocessed_out                      false
% 0.49/0.83  --preprocessed_stats                    false
% 0.49/0.83  
% 0.49/0.83  ------ Abstraction refinement Options
% 0.49/0.83  
% 0.49/0.83  --abstr_ref                             []
% 0.49/0.83  --abstr_ref_prep                        false
% 0.49/0.83  --abstr_ref_until_sat                   false
% 0.49/0.83  --abstr_ref_sig_restrict                funpre
% 0.49/0.83  --abstr_ref_af_restrict_to_split_sk     false
% 0.49/0.83  --abstr_ref_under                       []
% 0.49/0.83  
% 0.49/0.83  ------ SAT Options
% 0.49/0.83  
% 0.49/0.83  --sat_mode                              false
% 0.49/0.83  --sat_fm_restart_options                ""
% 0.49/0.83  --sat_gr_def                            false
% 0.49/0.83  --sat_epr_types                         true
% 0.49/0.83  --sat_non_cyclic_types                  false
% 0.49/0.83  --sat_finite_models                     false
% 0.49/0.83  --sat_fm_lemmas                         false
% 0.49/0.83  --sat_fm_prep                           false
% 0.49/0.83  --sat_fm_uc_incr                        true
% 0.49/0.83  --sat_out_model                         small
% 0.49/0.83  --sat_out_clauses                       false
% 0.49/0.83  
% 0.49/0.83  ------ QBF Options
% 0.49/0.83  
% 0.49/0.83  --qbf_mode                              false
% 0.49/0.83  --qbf_elim_univ                         false
% 0.49/0.83  --qbf_dom_inst                          none
% 0.49/0.83  --qbf_dom_pre_inst                      false
% 0.49/0.83  --qbf_sk_in                             false
% 0.49/0.83  --qbf_pred_elim                         true
% 0.49/0.83  --qbf_split                             512
% 0.49/0.83  
% 0.49/0.83  ------ BMC1 Options
% 0.49/0.83  
% 0.49/0.83  --bmc1_incremental                      false
% 0.49/0.83  --bmc1_axioms                           reachable_all
% 0.49/0.83  --bmc1_min_bound                        0
% 0.49/0.83  --bmc1_max_bound                        -1
% 0.49/0.83  --bmc1_max_bound_default                -1
% 0.49/0.83  --bmc1_symbol_reachability              true
% 0.49/0.83  --bmc1_property_lemmas                  false
% 0.49/0.83  --bmc1_k_induction                      false
% 0.49/0.83  --bmc1_non_equiv_states                 false
% 0.49/0.83  --bmc1_deadlock                         false
% 0.49/0.83  --bmc1_ucm                              false
% 0.49/0.83  --bmc1_add_unsat_core                   none
% 0.49/0.83  --bmc1_unsat_core_children              false
% 0.49/0.83  --bmc1_unsat_core_extrapolate_axioms    false
% 0.49/0.83  --bmc1_out_stat                         full
% 0.49/0.83  --bmc1_ground_init                      false
% 0.49/0.83  --bmc1_pre_inst_next_state              false
% 0.49/0.83  --bmc1_pre_inst_state                   false
% 0.49/0.83  --bmc1_pre_inst_reach_state             false
% 0.49/0.83  --bmc1_out_unsat_core                   false
% 0.49/0.83  --bmc1_aig_witness_out                  false
% 0.49/0.83  --bmc1_verbose                          false
% 0.49/0.83  --bmc1_dump_clauses_tptp                false
% 0.49/0.83  --bmc1_dump_unsat_core_tptp             false
% 0.49/0.83  --bmc1_dump_file                        -
% 0.49/0.83  --bmc1_ucm_expand_uc_limit              128
% 0.49/0.83  --bmc1_ucm_n_expand_iterations          6
% 0.49/0.83  --bmc1_ucm_extend_mode                  1
% 0.49/0.83  --bmc1_ucm_init_mode                    2
% 0.49/0.83  --bmc1_ucm_cone_mode                    none
% 0.49/0.83  --bmc1_ucm_reduced_relation_type        0
% 0.49/0.83  --bmc1_ucm_relax_model                  4
% 0.49/0.83  --bmc1_ucm_full_tr_after_sat            true
% 0.49/0.83  --bmc1_ucm_expand_neg_assumptions       false
% 0.49/0.83  --bmc1_ucm_layered_model                none
% 0.49/0.83  --bmc1_ucm_max_lemma_size               10
% 0.49/0.83  
% 0.49/0.83  ------ AIG Options
% 0.49/0.83  
% 0.49/0.83  --aig_mode                              false
% 0.49/0.83  
% 0.49/0.83  ------ Instantiation Options
% 0.49/0.83  
% 0.49/0.83  --instantiation_flag                    true
% 0.49/0.83  --inst_sos_flag                         false
% 0.49/0.83  --inst_sos_phase                        true
% 0.49/0.83  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.49/0.83  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.49/0.83  --inst_lit_sel_side                     none
% 0.49/0.83  --inst_solver_per_active                1400
% 0.49/0.83  --inst_solver_calls_frac                1.
% 0.49/0.83  --inst_passive_queue_type               priority_queues
% 0.49/0.83  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.49/0.83  --inst_passive_queues_freq              [25;2]
% 0.49/0.83  --inst_dismatching                      true
% 0.49/0.83  --inst_eager_unprocessed_to_passive     true
% 0.49/0.83  --inst_prop_sim_given                   true
% 0.49/0.83  --inst_prop_sim_new                     false
% 0.49/0.83  --inst_subs_new                         false
% 0.49/0.83  --inst_eq_res_simp                      false
% 0.49/0.83  --inst_subs_given                       false
% 0.49/0.83  --inst_orphan_elimination               true
% 0.49/0.83  --inst_learning_loop_flag               true
% 0.49/0.83  --inst_learning_start                   3000
% 0.49/0.83  --inst_learning_factor                  2
% 0.49/0.83  --inst_start_prop_sim_after_learn       3
% 0.49/0.83  --inst_sel_renew                        solver
% 0.49/0.83  --inst_lit_activity_flag                true
% 0.49/0.83  --inst_restr_to_given                   false
% 0.49/0.83  --inst_activity_threshold               500
% 0.49/0.83  --inst_out_proof                        true
% 0.49/0.83  
% 0.49/0.83  ------ Resolution Options
% 0.49/0.83  
% 0.49/0.83  --resolution_flag                       false
% 0.49/0.83  --res_lit_sel                           adaptive
% 0.49/0.83  --res_lit_sel_side                      none
% 0.49/0.83  --res_ordering                          kbo
% 0.49/0.83  --res_to_prop_solver                    active
% 0.49/0.83  --res_prop_simpl_new                    false
% 0.49/0.83  --res_prop_simpl_given                  true
% 0.49/0.83  --res_passive_queue_type                priority_queues
% 0.49/0.83  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.49/0.83  --res_passive_queues_freq               [15;5]
% 0.49/0.83  --res_forward_subs                      full
% 0.49/0.83  --res_backward_subs                     full
% 0.49/0.83  --res_forward_subs_resolution           true
% 0.49/0.83  --res_backward_subs_resolution          true
% 0.49/0.83  --res_orphan_elimination                true
% 0.49/0.83  --res_time_limit                        2.
% 0.49/0.83  --res_out_proof                         true
% 0.49/0.83  
% 0.49/0.83  ------ Superposition Options
% 0.49/0.83  
% 0.49/0.83  --superposition_flag                    true
% 0.49/0.83  --sup_passive_queue_type                priority_queues
% 0.49/0.83  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.49/0.83  --sup_passive_queues_freq               [8;1;4]
% 0.49/0.83  --demod_completeness_check              fast
% 0.49/0.83  --demod_use_ground                      true
% 0.49/0.83  --sup_to_prop_solver                    passive
% 0.49/0.83  --sup_prop_simpl_new                    true
% 0.49/0.83  --sup_prop_simpl_given                  true
% 0.49/0.83  --sup_fun_splitting                     false
% 0.49/0.83  --sup_smt_interval                      50000
% 0.49/0.83  
% 0.49/0.83  ------ Superposition Simplification Setup
% 0.49/0.83  
% 0.49/0.83  --sup_indices_passive                   []
% 0.49/0.83  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.49/0.83  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.49/0.83  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.49/0.83  --sup_full_triv                         [TrivRules;PropSubs]
% 0.49/0.83  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.49/0.83  --sup_full_bw                           [BwDemod]
% 0.49/0.83  --sup_immed_triv                        [TrivRules]
% 0.49/0.83  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.49/0.83  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.49/0.83  --sup_immed_bw_main                     []
% 0.49/0.83  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.49/0.83  --sup_input_triv                        [Unflattening;TrivRules]
% 0.49/0.83  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.49/0.83  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.49/0.83  
% 0.49/0.83  ------ Combination Options
% 0.49/0.83  
% 0.49/0.83  --comb_res_mult                         3
% 0.49/0.83  --comb_sup_mult                         2
% 0.49/0.83  --comb_inst_mult                        10
% 0.49/0.83  
% 0.49/0.83  ------ Debug Options
% 0.49/0.83  
% 0.49/0.83  --dbg_backtrace                         false
% 0.49/0.83  --dbg_dump_prop_clauses                 false
% 0.49/0.83  --dbg_dump_prop_clauses_file            -
% 0.49/0.83  --dbg_out_stat                          false
% 0.49/0.83  
% 0.49/0.83  
% 0.49/0.83  
% 0.49/0.83  
% 0.49/0.83  ------ Proving...
% 0.49/0.83  
% 0.49/0.83  
% 0.49/0.83  % SZS status Theorem for theBenchmark.p
% 0.49/0.83  
% 0.49/0.83  % SZS output start CNFRefutation for theBenchmark.p
% 0.49/0.83  
% 0.49/0.83  fof(f4,conjecture,(
% 0.49/0.83    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 0.49/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.49/0.83  
% 0.49/0.83  fof(f5,negated_conjecture,(
% 0.49/0.83    ~! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)))),
% 0.49/0.83    inference(negated_conjecture,[],[f4])).
% 0.49/0.83  
% 0.49/0.83  fof(f10,plain,(
% 0.49/0.83    ? [X0] : (? [X1,X2] : (k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1) & r1_tarski(X1,X2)) & v1_relat_1(X0))),
% 0.49/0.83    inference(ennf_transformation,[],[f5])).
% 0.49/0.83  
% 0.49/0.83  fof(f12,plain,(
% 0.49/0.83    ( ! [X0] : (? [X1,X2] : (k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1) & r1_tarski(X1,X2)) => (k9_relat_1(X0,sK1) != k9_relat_1(k7_relat_1(X0,sK2),sK1) & r1_tarski(sK1,sK2))) )),
% 0.49/0.83    introduced(choice_axiom,[])).
% 0.49/0.83  
% 0.49/0.83  fof(f11,plain,(
% 0.49/0.83    ? [X0] : (? [X1,X2] : (k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1) & r1_tarski(X1,X2)) & v1_relat_1(X0)) => (? [X2,X1] : (k9_relat_1(sK0,X1) != k9_relat_1(k7_relat_1(sK0,X2),X1) & r1_tarski(X1,X2)) & v1_relat_1(sK0))),
% 0.49/0.83    introduced(choice_axiom,[])).
% 0.49/0.83  
% 0.49/0.83  fof(f13,plain,(
% 0.49/0.83    (k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1) & r1_tarski(sK1,sK2)) & v1_relat_1(sK0)),
% 0.49/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12,f11])).
% 0.49/0.83  
% 0.49/0.83  fof(f17,plain,(
% 0.49/0.83    v1_relat_1(sK0)),
% 0.49/0.83    inference(cnf_transformation,[],[f13])).
% 0.49/0.83  
% 0.49/0.83  fof(f2,axiom,(
% 0.49/0.83    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)))),
% 0.49/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.49/0.83  
% 0.49/0.83  fof(f7,plain,(
% 0.49/0.83    ! [X0,X1,X2] : ((k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.49/0.83    inference(ennf_transformation,[],[f2])).
% 0.49/0.83  
% 0.49/0.83  fof(f8,plain,(
% 0.49/0.83    ! [X0,X1,X2] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.49/0.83    inference(flattening,[],[f7])).
% 0.49/0.83  
% 0.49/0.83  fof(f15,plain,(
% 0.49/0.83    ( ! [X2,X0,X1] : (k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.49/0.83    inference(cnf_transformation,[],[f8])).
% 0.49/0.83  
% 0.49/0.83  fof(f18,plain,(
% 0.49/0.83    r1_tarski(sK1,sK2)),
% 0.49/0.83    inference(cnf_transformation,[],[f13])).
% 0.49/0.83  
% 0.49/0.83  fof(f1,axiom,(
% 0.49/0.83    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.49/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.49/0.83  
% 0.49/0.83  fof(f6,plain,(
% 0.49/0.83    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.49/0.83    inference(ennf_transformation,[],[f1])).
% 0.49/0.83  
% 0.49/0.83  fof(f14,plain,(
% 0.49/0.83    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.49/0.83    inference(cnf_transformation,[],[f6])).
% 0.49/0.83  
% 0.49/0.83  fof(f3,axiom,(
% 0.49/0.83    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.49/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.49/0.83  
% 0.49/0.83  fof(f9,plain,(
% 0.49/0.83    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.49/0.83    inference(ennf_transformation,[],[f3])).
% 0.49/0.83  
% 0.49/0.83  fof(f16,plain,(
% 0.49/0.83    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.49/0.83    inference(cnf_transformation,[],[f9])).
% 0.49/0.83  
% 0.49/0.83  fof(f19,plain,(
% 0.49/0.83    k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1)),
% 0.49/0.83    inference(cnf_transformation,[],[f13])).
% 0.49/0.83  
% 0.49/0.83  cnf(c_5,negated_conjecture,
% 0.49/0.83      ( v1_relat_1(sK0) ),
% 0.49/0.83      inference(cnf_transformation,[],[f17]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_112,negated_conjecture,
% 0.49/0.83      ( v1_relat_1(sK0) ),
% 0.49/0.83      inference(subtyping,[status(esa)],[c_5]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_215,plain,
% 0.49/0.83      ( v1_relat_1(sK0) = iProver_top ),
% 0.49/0.83      inference(predicate_to_equality,[status(thm)],[c_112]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_1,plain,
% 0.49/0.83      ( ~ r1_tarski(X0,X1)
% 0.49/0.83      | ~ v1_relat_1(X2)
% 0.49/0.83      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
% 0.49/0.83      inference(cnf_transformation,[],[f15]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_4,negated_conjecture,
% 0.49/0.83      ( r1_tarski(sK1,sK2) ),
% 0.49/0.83      inference(cnf_transformation,[],[f18]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_62,plain,
% 0.49/0.83      ( ~ v1_relat_1(X0)
% 0.49/0.83      | k7_relat_1(k7_relat_1(X0,X1),X2) = k7_relat_1(X0,X2)
% 0.49/0.83      | sK2 != X1
% 0.49/0.83      | sK1 != X2 ),
% 0.49/0.83      inference(resolution_lifted,[status(thm)],[c_1,c_4]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_63,plain,
% 0.49/0.83      ( ~ v1_relat_1(X0)
% 0.49/0.83      | k7_relat_1(k7_relat_1(X0,sK2),sK1) = k7_relat_1(X0,sK1) ),
% 0.49/0.83      inference(unflattening,[status(thm)],[c_62]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_111,plain,
% 0.49/0.83      ( ~ v1_relat_1(X0_36)
% 0.49/0.83      | k7_relat_1(k7_relat_1(X0_36,sK2),sK1) = k7_relat_1(X0_36,sK1) ),
% 0.49/0.83      inference(subtyping,[status(esa)],[c_63]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_216,plain,
% 0.49/0.83      ( k7_relat_1(k7_relat_1(X0_36,sK2),sK1) = k7_relat_1(X0_36,sK1)
% 0.49/0.83      | v1_relat_1(X0_36) != iProver_top ),
% 0.49/0.83      inference(predicate_to_equality,[status(thm)],[c_111]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_267,plain,
% 0.49/0.83      ( k7_relat_1(k7_relat_1(sK0,sK2),sK1) = k7_relat_1(sK0,sK1) ),
% 0.49/0.83      inference(superposition,[status(thm)],[c_215,c_216]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_0,plain,
% 0.49/0.83      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 0.49/0.83      inference(cnf_transformation,[],[f14]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_115,plain,
% 0.49/0.83      ( ~ v1_relat_1(X0_36) | v1_relat_1(k7_relat_1(X0_36,X0_37)) ),
% 0.49/0.83      inference(subtyping,[status(esa)],[c_0]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_213,plain,
% 0.49/0.83      ( v1_relat_1(X0_36) != iProver_top
% 0.49/0.83      | v1_relat_1(k7_relat_1(X0_36,X0_37)) = iProver_top ),
% 0.49/0.83      inference(predicate_to_equality,[status(thm)],[c_115]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_2,plain,
% 0.49/0.83      ( ~ v1_relat_1(X0)
% 0.49/0.83      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 0.49/0.83      inference(cnf_transformation,[],[f16]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_114,plain,
% 0.49/0.83      ( ~ v1_relat_1(X0_36)
% 0.49/0.83      | k2_relat_1(k7_relat_1(X0_36,X0_37)) = k9_relat_1(X0_36,X0_37) ),
% 0.49/0.83      inference(subtyping,[status(esa)],[c_2]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_214,plain,
% 0.49/0.83      ( k2_relat_1(k7_relat_1(X0_36,X0_37)) = k9_relat_1(X0_36,X0_37)
% 0.49/0.83      | v1_relat_1(X0_36) != iProver_top ),
% 0.49/0.83      inference(predicate_to_equality,[status(thm)],[c_114]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_465,plain,
% 0.49/0.83      ( k2_relat_1(k7_relat_1(k7_relat_1(X0_36,X0_37),X1_37)) = k9_relat_1(k7_relat_1(X0_36,X0_37),X1_37)
% 0.49/0.83      | v1_relat_1(X0_36) != iProver_top ),
% 0.49/0.83      inference(superposition,[status(thm)],[c_213,c_214]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_1071,plain,
% 0.49/0.83      ( k2_relat_1(k7_relat_1(k7_relat_1(sK0,X0_37),X1_37)) = k9_relat_1(k7_relat_1(sK0,X0_37),X1_37) ),
% 0.49/0.83      inference(superposition,[status(thm)],[c_215,c_465]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_1087,plain,
% 0.49/0.83      ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k2_relat_1(k7_relat_1(sK0,sK1)) ),
% 0.49/0.83      inference(superposition,[status(thm)],[c_267,c_1071]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_464,plain,
% 0.49/0.83      ( k2_relat_1(k7_relat_1(sK0,X0_37)) = k9_relat_1(sK0,X0_37) ),
% 0.49/0.83      inference(superposition,[status(thm)],[c_215,c_214]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_1088,plain,
% 0.49/0.83      ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) = k9_relat_1(sK0,sK1) ),
% 0.49/0.83      inference(demodulation,[status(thm)],[c_1087,c_464]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_120,plain,
% 0.49/0.83      ( X0_38 != X1_38 | X2_38 != X1_38 | X2_38 = X0_38 ),
% 0.49/0.83      theory(equality) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_245,plain,
% 0.49/0.83      ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != X0_38
% 0.49/0.83      | k9_relat_1(sK0,sK1) != X0_38
% 0.49/0.83      | k9_relat_1(sK0,sK1) = k9_relat_1(k7_relat_1(sK0,sK2),sK1) ),
% 0.49/0.83      inference(instantiation,[status(thm)],[c_120]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_250,plain,
% 0.49/0.83      ( k9_relat_1(k7_relat_1(sK0,sK2),sK1) != k9_relat_1(sK0,sK1)
% 0.49/0.83      | k9_relat_1(sK0,sK1) = k9_relat_1(k7_relat_1(sK0,sK2),sK1)
% 0.49/0.83      | k9_relat_1(sK0,sK1) != k9_relat_1(sK0,sK1) ),
% 0.49/0.83      inference(instantiation,[status(thm)],[c_245]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_3,negated_conjecture,
% 0.49/0.83      ( k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1) ),
% 0.49/0.83      inference(cnf_transformation,[],[f19]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_113,negated_conjecture,
% 0.49/0.83      ( k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1) ),
% 0.49/0.83      inference(subtyping,[status(esa)],[c_3]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_117,plain,( X0_36 = X0_36 ),theory(equality) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_130,plain,
% 0.49/0.83      ( sK0 = sK0 ),
% 0.49/0.83      inference(instantiation,[status(thm)],[c_117]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_124,plain,
% 0.49/0.83      ( k9_relat_1(X0_36,X0_37) = k9_relat_1(X1_36,X0_37)
% 0.49/0.83      | X0_36 != X1_36 ),
% 0.49/0.83      theory(equality) ).
% 0.49/0.83  
% 0.49/0.83  cnf(c_128,plain,
% 0.49/0.83      ( k9_relat_1(sK0,sK1) = k9_relat_1(sK0,sK1) | sK0 != sK0 ),
% 0.49/0.83      inference(instantiation,[status(thm)],[c_124]) ).
% 0.49/0.83  
% 0.49/0.83  cnf(contradiction,plain,
% 0.49/0.83      ( $false ),
% 0.49/0.83      inference(minisat,[status(thm)],[c_1088,c_250,c_113,c_130,c_128]) ).
% 0.49/0.83  
% 0.49/0.83  
% 0.49/0.83  % SZS output end CNFRefutation for theBenchmark.p
% 0.49/0.83  
% 0.49/0.83  ------                               Statistics
% 0.49/0.83  
% 0.49/0.83  ------ General
% 0.49/0.83  
% 0.49/0.83  abstr_ref_over_cycles:                  0
% 0.49/0.83  abstr_ref_under_cycles:                 0
% 0.49/0.83  gc_basic_clause_elim:                   0
% 0.49/0.83  forced_gc_time:                         0
% 0.49/0.83  parsing_time:                           0.005
% 0.49/0.83  unif_index_cands_time:                  0.
% 0.49/0.83  unif_index_add_time:                    0.
% 0.49/0.83  orderings_time:                         0.
% 0.49/0.83  out_proof_time:                         0.005
% 0.49/0.83  total_time:                             0.045
% 0.49/0.83  num_of_symbols:                         39
% 0.49/0.83  num_of_terms:                           790
% 0.49/0.83  
% 0.49/0.83  ------ Preprocessing
% 0.49/0.83  
% 0.49/0.83  num_of_splits:                          0
% 0.49/0.83  num_of_split_atoms:                     0
% 0.49/0.83  num_of_reused_defs:                     0
% 0.49/0.83  num_eq_ax_congr_red:                    2
% 0.49/0.83  num_of_sem_filtered_clauses:            1
% 0.49/0.83  num_of_subtypes:                        3
% 0.49/0.83  monotx_restored_types:                  0
% 0.49/0.83  sat_num_of_epr_types:                   0
% 0.49/0.83  sat_num_of_non_cyclic_types:            0
% 0.49/0.83  sat_guarded_non_collapsed_types:        0
% 0.49/0.83  num_pure_diseq_elim:                    0
% 0.49/0.83  simp_replaced_by:                       0
% 0.49/0.83  res_preprocessed:                       38
% 0.49/0.83  prep_upred:                             0
% 0.49/0.83  prep_unflattend:                        2
% 0.49/0.83  smt_new_axioms:                         0
% 0.49/0.83  pred_elim_cands:                        1
% 0.49/0.83  pred_elim:                              1
% 0.49/0.83  pred_elim_cl:                           1
% 0.49/0.83  pred_elim_cycles:                       3
% 0.49/0.83  merged_defs:                            0
% 0.49/0.83  merged_defs_ncl:                        0
% 0.49/0.83  bin_hyper_res:                          0
% 0.49/0.83  prep_cycles:                            4
% 0.49/0.83  pred_elim_time:                         0.
% 0.49/0.83  splitting_time:                         0.
% 0.49/0.83  sem_filter_time:                        0.
% 0.49/0.83  monotx_time:                            0.
% 0.49/0.83  subtype_inf_time:                       0.
% 0.49/0.83  
% 0.49/0.83  ------ Problem properties
% 0.49/0.83  
% 0.49/0.83  clauses:                                5
% 0.49/0.83  conjectures:                            2
% 0.49/0.83  epr:                                    1
% 0.49/0.83  horn:                                   5
% 0.49/0.83  ground:                                 2
% 0.49/0.83  unary:                                  2
% 0.49/0.83  binary:                                 3
% 0.49/0.83  lits:                                   8
% 0.49/0.83  lits_eq:                                3
% 0.49/0.83  fd_pure:                                0
% 0.49/0.83  fd_pseudo:                              0
% 0.49/0.83  fd_cond:                                0
% 0.49/0.83  fd_pseudo_cond:                         0
% 0.49/0.83  ac_symbols:                             0
% 0.49/0.83  
% 0.49/0.83  ------ Propositional Solver
% 0.49/0.83  
% 0.49/0.83  prop_solver_calls:                      29
% 0.49/0.83  prop_fast_solver_calls:                 176
% 0.49/0.83  smt_solver_calls:                       0
% 0.49/0.83  smt_fast_solver_calls:                  0
% 0.49/0.83  prop_num_of_clauses:                    296
% 0.49/0.83  prop_preprocess_simplified:             1429
% 0.49/0.83  prop_fo_subsumed:                       1
% 0.49/0.83  prop_solver_time:                       0.
% 0.49/0.83  smt_solver_time:                        0.
% 0.49/0.83  smt_fast_solver_time:                   0.
% 0.49/0.83  prop_fast_solver_time:                  0.
% 0.49/0.83  prop_unsat_core_time:                   0.
% 0.49/0.83  
% 0.49/0.83  ------ QBF
% 0.49/0.83  
% 0.49/0.83  qbf_q_res:                              0
% 0.49/0.83  qbf_num_tautologies:                    0
% 0.49/0.83  qbf_prep_cycles:                        0
% 0.49/0.83  
% 0.49/0.83  ------ BMC1
% 0.49/0.83  
% 0.49/0.83  bmc1_current_bound:                     -1
% 0.49/0.83  bmc1_last_solved_bound:                 -1
% 0.49/0.83  bmc1_unsat_core_size:                   -1
% 0.49/0.83  bmc1_unsat_core_parents_size:           -1
% 0.49/0.83  bmc1_merge_next_fun:                    0
% 0.49/0.83  bmc1_unsat_core_clauses_time:           0.
% 0.49/0.83  
% 0.49/0.83  ------ Instantiation
% 0.49/0.83  
% 0.49/0.83  inst_num_of_clauses:                    181
% 0.49/0.83  inst_num_in_passive:                    14
% 0.49/0.83  inst_num_in_active:                     104
% 0.49/0.83  inst_num_in_unprocessed:                63
% 0.49/0.83  inst_num_of_loops:                      110
% 0.49/0.83  inst_num_of_learning_restarts:          0
% 0.49/0.83  inst_num_moves_active_passive:          2
% 0.49/0.83  inst_lit_activity:                      0
% 0.49/0.83  inst_lit_activity_moves:                0
% 0.49/0.83  inst_num_tautologies:                   0
% 0.49/0.83  inst_num_prop_implied:                  0
% 0.49/0.83  inst_num_existing_simplified:           0
% 0.49/0.83  inst_num_eq_res_simplified:             0
% 0.49/0.83  inst_num_child_elim:                    0
% 0.49/0.83  inst_num_of_dismatching_blockings:      56
% 0.49/0.83  inst_num_of_non_proper_insts:           217
% 0.49/0.83  inst_num_of_duplicates:                 0
% 0.49/0.83  inst_inst_num_from_inst_to_res:         0
% 0.49/0.83  inst_dismatching_checking_time:         0.
% 0.49/0.83  
% 0.49/0.83  ------ Resolution
% 0.49/0.83  
% 0.49/0.83  res_num_of_clauses:                     0
% 0.49/0.83  res_num_in_passive:                     0
% 0.49/0.83  res_num_in_active:                      0
% 0.49/0.83  res_num_of_loops:                       42
% 0.49/0.83  res_forward_subset_subsumed:            71
% 0.49/0.83  res_backward_subset_subsumed:           2
% 0.49/0.83  res_forward_subsumed:                   0
% 0.49/0.83  res_backward_subsumed:                  0
% 0.49/0.83  res_forward_subsumption_resolution:     0
% 0.49/0.83  res_backward_subsumption_resolution:    0
% 0.49/0.83  res_clause_to_clause_subsumption:       58
% 0.49/0.83  res_orphan_elimination:                 0
% 0.49/0.83  res_tautology_del:                      54
% 0.49/0.83  res_num_eq_res_simplified:              0
% 0.49/0.83  res_num_sel_changes:                    0
% 0.49/0.83  res_moves_from_active_to_pass:          0
% 0.49/0.83  
% 0.49/0.83  ------ Superposition
% 0.49/0.83  
% 0.49/0.83  sup_time_total:                         0.
% 0.49/0.83  sup_time_generating:                    0.
% 0.49/0.83  sup_time_sim_full:                      0.
% 0.49/0.83  sup_time_sim_immed:                     0.
% 0.49/0.83  
% 0.49/0.83  sup_num_of_clauses:                     27
% 0.49/0.83  sup_num_in_active:                      22
% 0.49/0.83  sup_num_in_passive:                     5
% 0.49/0.83  sup_num_of_loops:                       21
% 0.49/0.83  sup_fw_superposition:                   25
% 0.49/0.83  sup_bw_superposition:                   7
% 0.49/0.83  sup_immediate_simplified:               9
% 0.49/0.83  sup_given_eliminated:                   0
% 0.49/0.83  comparisons_done:                       0
% 0.49/0.83  comparisons_avoided:                    0
% 0.49/0.83  
% 0.49/0.83  ------ Simplifications
% 0.49/0.83  
% 0.49/0.83  
% 0.49/0.83  sim_fw_subset_subsumed:                 0
% 0.49/0.83  sim_bw_subset_subsumed:                 0
% 0.49/0.83  sim_fw_subsumed:                        7
% 0.49/0.83  sim_bw_subsumed:                        0
% 0.49/0.83  sim_fw_subsumption_res:                 0
% 0.49/0.83  sim_bw_subsumption_res:                 0
% 0.49/0.83  sim_tautology_del:                      0
% 0.49/0.83  sim_eq_tautology_del:                   1
% 0.49/0.83  sim_eq_res_simp:                        0
% 0.49/0.83  sim_fw_demodulated:                     1
% 0.49/0.83  sim_bw_demodulated:                     0
% 0.49/0.83  sim_light_normalised:                   4
% 0.49/0.83  sim_joinable_taut:                      0
% 0.49/0.83  sim_joinable_simp:                      0
% 0.49/0.83  sim_ac_normalised:                      0
% 0.49/0.83  sim_smt_subsumption:                    0
% 0.49/0.83  
%------------------------------------------------------------------------------
