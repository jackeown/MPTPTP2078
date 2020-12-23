%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:09:14 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 102 expanded)
%              Number of clauses        :   24 (  25 expanded)
%              Number of leaves         :   13 (  32 expanded)
%              Depth                    :   13
%              Number of atoms          :  103 ( 197 expanded)
%              Number of equality atoms :   64 ( 112 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f93,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f64,f65,f65])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
     => ( k10_relat_1(X0,sK4) != k10_relat_1(k7_relat_1(X0,sK3),sK4)
        & r1_tarski(k10_relat_1(X0,sK4),sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK2,X2) != k10_relat_1(k7_relat_1(sK2,X1),X2)
          & r1_tarski(k10_relat_1(sK2,X2),X1) )
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4)
    & r1_tarski(k10_relat_1(sK2,sK4),sK3)
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f51,f50])).

fof(f86,plain,(
    r1_tarski(k10_relat_1(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k6_subset_1(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f57,f66])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f88,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f63,f66,f66])).

fof(f94,plain,(
    ! [X0,X1] : k6_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f67,f88,f65])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f92,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( k6_subset_1(X0,k6_subset_1(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_unfolding,[],[f81,f88])).

fof(f84,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_10,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_29,negated_conjecture,
    ( r1_tarski(k10_relat_1(sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1401,plain,
    ( r1_tarski(k10_relat_1(sK2,sK4),sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k6_subset_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1408,plain,
    ( k6_subset_1(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6398,plain,
    ( k6_subset_1(k10_relat_1(sK2,sK4),sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1401,c_1408])).

cnf(c_11,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_6456,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,sK4),k10_relat_1(sK2,sK4),sK3)) = k6_subset_1(k10_relat_1(sK2,sK4),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_6398,c_11])).

cnf(c_8,plain,
    ( k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_6458,plain,
    ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,sK4),k10_relat_1(sK2,sK4),sK3)) = k10_relat_1(sK2,sK4) ),
    inference(demodulation,[status(thm)],[c_6456,c_8])).

cnf(c_9374,plain,
    ( k1_setfam_1(k1_enumset1(sK3,sK3,k10_relat_1(sK2,sK4))) = k10_relat_1(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_10,c_6458])).

cnf(c_25,plain,
    ( ~ v1_relat_1(X0)
    | k6_subset_1(X1,k6_subset_1(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_31,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_733,plain,
    ( k6_subset_1(X0,k6_subset_1(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_31])).

cnf(c_734,plain,
    ( k6_subset_1(X0,k6_subset_1(X0,k10_relat_1(sK2,X1))) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(unflattening,[status(thm)],[c_733])).

cnf(c_2231,plain,
    ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1))) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
    inference(superposition,[status(thm)],[c_11,c_734])).

cnf(c_9387,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) = k10_relat_1(sK2,sK4) ),
    inference(superposition,[status(thm)],[c_9374,c_2231])).

cnf(c_762,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1732,plain,
    ( k10_relat_1(sK2,sK4) = k10_relat_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_763,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1693,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != X0
    | k10_relat_1(sK2,sK4) != X0
    | k10_relat_1(sK2,sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_1731,plain,
    ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k10_relat_1(sK2,sK4)
    | k10_relat_1(sK2,sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4)
    | k10_relat_1(sK2,sK4) != k10_relat_1(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_1693])).

cnf(c_28,negated_conjecture,
    ( k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f87])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9387,c_1732,c_1731,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.71/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/1.00  
% 3.71/1.00  ------  iProver source info
% 3.71/1.00  
% 3.71/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.71/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/1.00  git: non_committed_changes: false
% 3.71/1.00  git: last_make_outside_of_git: false
% 3.71/1.00  
% 3.71/1.00  ------ 
% 3.71/1.00  
% 3.71/1.00  ------ Input Options
% 3.71/1.00  
% 3.71/1.00  --out_options                           all
% 3.71/1.00  --tptp_safe_out                         true
% 3.71/1.00  --problem_path                          ""
% 3.71/1.00  --include_path                          ""
% 3.71/1.00  --clausifier                            res/vclausify_rel
% 3.71/1.00  --clausifier_options                    --mode clausify
% 3.71/1.00  --stdin                                 false
% 3.71/1.00  --stats_out                             all
% 3.71/1.00  
% 3.71/1.00  ------ General Options
% 3.71/1.00  
% 3.71/1.00  --fof                                   false
% 3.71/1.00  --time_out_real                         305.
% 3.71/1.00  --time_out_virtual                      -1.
% 3.71/1.00  --symbol_type_check                     false
% 3.71/1.00  --clausify_out                          false
% 3.71/1.00  --sig_cnt_out                           false
% 3.71/1.00  --trig_cnt_out                          false
% 3.71/1.00  --trig_cnt_out_tolerance                1.
% 3.71/1.00  --trig_cnt_out_sk_spl                   false
% 3.71/1.00  --abstr_cl_out                          false
% 3.71/1.00  
% 3.71/1.00  ------ Global Options
% 3.71/1.00  
% 3.71/1.00  --schedule                              default
% 3.71/1.00  --add_important_lit                     false
% 3.71/1.00  --prop_solver_per_cl                    1000
% 3.71/1.00  --min_unsat_core                        false
% 3.71/1.00  --soft_assumptions                      false
% 3.71/1.00  --soft_lemma_size                       3
% 3.71/1.00  --prop_impl_unit_size                   0
% 3.71/1.00  --prop_impl_unit                        []
% 3.71/1.00  --share_sel_clauses                     true
% 3.71/1.00  --reset_solvers                         false
% 3.71/1.00  --bc_imp_inh                            [conj_cone]
% 3.71/1.00  --conj_cone_tolerance                   3.
% 3.71/1.00  --extra_neg_conj                        none
% 3.71/1.00  --large_theory_mode                     true
% 3.71/1.00  --prolific_symb_bound                   200
% 3.71/1.00  --lt_threshold                          2000
% 3.71/1.00  --clause_weak_htbl                      true
% 3.71/1.00  --gc_record_bc_elim                     false
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing Options
% 3.71/1.00  
% 3.71/1.00  --preprocessing_flag                    true
% 3.71/1.00  --time_out_prep_mult                    0.1
% 3.71/1.00  --splitting_mode                        input
% 3.71/1.00  --splitting_grd                         true
% 3.71/1.00  --splitting_cvd                         false
% 3.71/1.00  --splitting_cvd_svl                     false
% 3.71/1.00  --splitting_nvd                         32
% 3.71/1.00  --sub_typing                            true
% 3.71/1.00  --prep_gs_sim                           true
% 3.71/1.00  --prep_unflatten                        true
% 3.71/1.00  --prep_res_sim                          true
% 3.71/1.00  --prep_upred                            true
% 3.71/1.00  --prep_sem_filter                       exhaustive
% 3.71/1.00  --prep_sem_filter_out                   false
% 3.71/1.00  --pred_elim                             true
% 3.71/1.00  --res_sim_input                         true
% 3.71/1.00  --eq_ax_congr_red                       true
% 3.71/1.00  --pure_diseq_elim                       true
% 3.71/1.00  --brand_transform                       false
% 3.71/1.00  --non_eq_to_eq                          false
% 3.71/1.00  --prep_def_merge                        true
% 3.71/1.00  --prep_def_merge_prop_impl              false
% 3.71/1.00  --prep_def_merge_mbd                    true
% 3.71/1.00  --prep_def_merge_tr_red                 false
% 3.71/1.00  --prep_def_merge_tr_cl                  false
% 3.71/1.00  --smt_preprocessing                     true
% 3.71/1.00  --smt_ac_axioms                         fast
% 3.71/1.00  --preprocessed_out                      false
% 3.71/1.00  --preprocessed_stats                    false
% 3.71/1.00  
% 3.71/1.00  ------ Abstraction refinement Options
% 3.71/1.00  
% 3.71/1.00  --abstr_ref                             []
% 3.71/1.00  --abstr_ref_prep                        false
% 3.71/1.00  --abstr_ref_until_sat                   false
% 3.71/1.00  --abstr_ref_sig_restrict                funpre
% 3.71/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/1.00  --abstr_ref_under                       []
% 3.71/1.00  
% 3.71/1.00  ------ SAT Options
% 3.71/1.00  
% 3.71/1.00  --sat_mode                              false
% 3.71/1.00  --sat_fm_restart_options                ""
% 3.71/1.00  --sat_gr_def                            false
% 3.71/1.00  --sat_epr_types                         true
% 3.71/1.00  --sat_non_cyclic_types                  false
% 3.71/1.00  --sat_finite_models                     false
% 3.71/1.00  --sat_fm_lemmas                         false
% 3.71/1.00  --sat_fm_prep                           false
% 3.71/1.00  --sat_fm_uc_incr                        true
% 3.71/1.00  --sat_out_model                         small
% 3.71/1.00  --sat_out_clauses                       false
% 3.71/1.00  
% 3.71/1.00  ------ QBF Options
% 3.71/1.00  
% 3.71/1.00  --qbf_mode                              false
% 3.71/1.00  --qbf_elim_univ                         false
% 3.71/1.00  --qbf_dom_inst                          none
% 3.71/1.00  --qbf_dom_pre_inst                      false
% 3.71/1.00  --qbf_sk_in                             false
% 3.71/1.00  --qbf_pred_elim                         true
% 3.71/1.00  --qbf_split                             512
% 3.71/1.00  
% 3.71/1.00  ------ BMC1 Options
% 3.71/1.00  
% 3.71/1.00  --bmc1_incremental                      false
% 3.71/1.00  --bmc1_axioms                           reachable_all
% 3.71/1.00  --bmc1_min_bound                        0
% 3.71/1.00  --bmc1_max_bound                        -1
% 3.71/1.00  --bmc1_max_bound_default                -1
% 3.71/1.00  --bmc1_symbol_reachability              true
% 3.71/1.00  --bmc1_property_lemmas                  false
% 3.71/1.00  --bmc1_k_induction                      false
% 3.71/1.00  --bmc1_non_equiv_states                 false
% 3.71/1.00  --bmc1_deadlock                         false
% 3.71/1.00  --bmc1_ucm                              false
% 3.71/1.00  --bmc1_add_unsat_core                   none
% 3.71/1.00  --bmc1_unsat_core_children              false
% 3.71/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/1.00  --bmc1_out_stat                         full
% 3.71/1.00  --bmc1_ground_init                      false
% 3.71/1.00  --bmc1_pre_inst_next_state              false
% 3.71/1.00  --bmc1_pre_inst_state                   false
% 3.71/1.00  --bmc1_pre_inst_reach_state             false
% 3.71/1.00  --bmc1_out_unsat_core                   false
% 3.71/1.00  --bmc1_aig_witness_out                  false
% 3.71/1.00  --bmc1_verbose                          false
% 3.71/1.00  --bmc1_dump_clauses_tptp                false
% 3.71/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.71/1.00  --bmc1_dump_file                        -
% 3.71/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.71/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.71/1.00  --bmc1_ucm_extend_mode                  1
% 3.71/1.00  --bmc1_ucm_init_mode                    2
% 3.71/1.00  --bmc1_ucm_cone_mode                    none
% 3.71/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.71/1.00  --bmc1_ucm_relax_model                  4
% 3.71/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.71/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/1.00  --bmc1_ucm_layered_model                none
% 3.71/1.00  --bmc1_ucm_max_lemma_size               10
% 3.71/1.00  
% 3.71/1.00  ------ AIG Options
% 3.71/1.00  
% 3.71/1.00  --aig_mode                              false
% 3.71/1.00  
% 3.71/1.00  ------ Instantiation Options
% 3.71/1.00  
% 3.71/1.00  --instantiation_flag                    true
% 3.71/1.00  --inst_sos_flag                         false
% 3.71/1.00  --inst_sos_phase                        true
% 3.71/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel_side                     num_symb
% 3.71/1.00  --inst_solver_per_active                1400
% 3.71/1.00  --inst_solver_calls_frac                1.
% 3.71/1.00  --inst_passive_queue_type               priority_queues
% 3.71/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/1.00  --inst_passive_queues_freq              [25;2]
% 3.71/1.00  --inst_dismatching                      true
% 3.71/1.00  --inst_eager_unprocessed_to_passive     true
% 3.71/1.00  --inst_prop_sim_given                   true
% 3.71/1.00  --inst_prop_sim_new                     false
% 3.71/1.00  --inst_subs_new                         false
% 3.71/1.00  --inst_eq_res_simp                      false
% 3.71/1.00  --inst_subs_given                       false
% 3.71/1.00  --inst_orphan_elimination               true
% 3.71/1.00  --inst_learning_loop_flag               true
% 3.71/1.00  --inst_learning_start                   3000
% 3.71/1.00  --inst_learning_factor                  2
% 3.71/1.00  --inst_start_prop_sim_after_learn       3
% 3.71/1.00  --inst_sel_renew                        solver
% 3.71/1.00  --inst_lit_activity_flag                true
% 3.71/1.00  --inst_restr_to_given                   false
% 3.71/1.00  --inst_activity_threshold               500
% 3.71/1.00  --inst_out_proof                        true
% 3.71/1.00  
% 3.71/1.00  ------ Resolution Options
% 3.71/1.00  
% 3.71/1.00  --resolution_flag                       true
% 3.71/1.00  --res_lit_sel                           adaptive
% 3.71/1.00  --res_lit_sel_side                      none
% 3.71/1.00  --res_ordering                          kbo
% 3.71/1.00  --res_to_prop_solver                    active
% 3.71/1.00  --res_prop_simpl_new                    false
% 3.71/1.00  --res_prop_simpl_given                  true
% 3.71/1.00  --res_passive_queue_type                priority_queues
% 3.71/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/1.00  --res_passive_queues_freq               [15;5]
% 3.71/1.00  --res_forward_subs                      full
% 3.71/1.00  --res_backward_subs                     full
% 3.71/1.00  --res_forward_subs_resolution           true
% 3.71/1.00  --res_backward_subs_resolution          true
% 3.71/1.00  --res_orphan_elimination                true
% 3.71/1.00  --res_time_limit                        2.
% 3.71/1.00  --res_out_proof                         true
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Options
% 3.71/1.00  
% 3.71/1.00  --superposition_flag                    true
% 3.71/1.00  --sup_passive_queue_type                priority_queues
% 3.71/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.71/1.00  --demod_completeness_check              fast
% 3.71/1.00  --demod_use_ground                      true
% 3.71/1.00  --sup_to_prop_solver                    passive
% 3.71/1.00  --sup_prop_simpl_new                    true
% 3.71/1.00  --sup_prop_simpl_given                  true
% 3.71/1.00  --sup_fun_splitting                     false
% 3.71/1.00  --sup_smt_interval                      50000
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Simplification Setup
% 3.71/1.00  
% 3.71/1.00  --sup_indices_passive                   []
% 3.71/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_full_bw                           [BwDemod]
% 3.71/1.00  --sup_immed_triv                        [TrivRules]
% 3.71/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_immed_bw_main                     []
% 3.71/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.00  
% 3.71/1.00  ------ Combination Options
% 3.71/1.00  
% 3.71/1.00  --comb_res_mult                         3
% 3.71/1.00  --comb_sup_mult                         2
% 3.71/1.00  --comb_inst_mult                        10
% 3.71/1.00  
% 3.71/1.00  ------ Debug Options
% 3.71/1.00  
% 3.71/1.00  --dbg_backtrace                         false
% 3.71/1.00  --dbg_dump_prop_clauses                 false
% 3.71/1.00  --dbg_dump_prop_clauses_file            -
% 3.71/1.00  --dbg_out_stat                          false
% 3.71/1.00  ------ Parsing...
% 3.71/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/1.00  ------ Proving...
% 3.71/1.00  ------ Problem Properties 
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  clauses                                 39
% 3.71/1.00  conjectures                             2
% 3.71/1.00  EPR                                     5
% 3.71/1.00  Horn                                    34
% 3.71/1.00  unary                                   17
% 3.71/1.00  binary                                  12
% 3.71/1.00  lits                                    73
% 3.71/1.00  lits eq                                 23
% 3.71/1.00  fd_pure                                 0
% 3.71/1.00  fd_pseudo                               0
% 3.71/1.00  fd_cond                                 1
% 3.71/1.00  fd_pseudo_cond                          6
% 3.71/1.00  AC symbols                              0
% 3.71/1.00  
% 3.71/1.00  ------ Schedule dynamic 5 is on 
% 3.71/1.00  
% 3.71/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  ------ 
% 3.71/1.00  Current options:
% 3.71/1.00  ------ 
% 3.71/1.00  
% 3.71/1.00  ------ Input Options
% 3.71/1.00  
% 3.71/1.00  --out_options                           all
% 3.71/1.00  --tptp_safe_out                         true
% 3.71/1.00  --problem_path                          ""
% 3.71/1.00  --include_path                          ""
% 3.71/1.00  --clausifier                            res/vclausify_rel
% 3.71/1.00  --clausifier_options                    --mode clausify
% 3.71/1.00  --stdin                                 false
% 3.71/1.00  --stats_out                             all
% 3.71/1.00  
% 3.71/1.00  ------ General Options
% 3.71/1.00  
% 3.71/1.00  --fof                                   false
% 3.71/1.00  --time_out_real                         305.
% 3.71/1.00  --time_out_virtual                      -1.
% 3.71/1.00  --symbol_type_check                     false
% 3.71/1.00  --clausify_out                          false
% 3.71/1.00  --sig_cnt_out                           false
% 3.71/1.00  --trig_cnt_out                          false
% 3.71/1.00  --trig_cnt_out_tolerance                1.
% 3.71/1.00  --trig_cnt_out_sk_spl                   false
% 3.71/1.00  --abstr_cl_out                          false
% 3.71/1.00  
% 3.71/1.00  ------ Global Options
% 3.71/1.00  
% 3.71/1.00  --schedule                              default
% 3.71/1.00  --add_important_lit                     false
% 3.71/1.00  --prop_solver_per_cl                    1000
% 3.71/1.00  --min_unsat_core                        false
% 3.71/1.00  --soft_assumptions                      false
% 3.71/1.00  --soft_lemma_size                       3
% 3.71/1.00  --prop_impl_unit_size                   0
% 3.71/1.00  --prop_impl_unit                        []
% 3.71/1.00  --share_sel_clauses                     true
% 3.71/1.00  --reset_solvers                         false
% 3.71/1.00  --bc_imp_inh                            [conj_cone]
% 3.71/1.00  --conj_cone_tolerance                   3.
% 3.71/1.00  --extra_neg_conj                        none
% 3.71/1.00  --large_theory_mode                     true
% 3.71/1.00  --prolific_symb_bound                   200
% 3.71/1.00  --lt_threshold                          2000
% 3.71/1.00  --clause_weak_htbl                      true
% 3.71/1.00  --gc_record_bc_elim                     false
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing Options
% 3.71/1.00  
% 3.71/1.00  --preprocessing_flag                    true
% 3.71/1.00  --time_out_prep_mult                    0.1
% 3.71/1.00  --splitting_mode                        input
% 3.71/1.00  --splitting_grd                         true
% 3.71/1.00  --splitting_cvd                         false
% 3.71/1.00  --splitting_cvd_svl                     false
% 3.71/1.00  --splitting_nvd                         32
% 3.71/1.00  --sub_typing                            true
% 3.71/1.00  --prep_gs_sim                           true
% 3.71/1.00  --prep_unflatten                        true
% 3.71/1.00  --prep_res_sim                          true
% 3.71/1.00  --prep_upred                            true
% 3.71/1.00  --prep_sem_filter                       exhaustive
% 3.71/1.00  --prep_sem_filter_out                   false
% 3.71/1.00  --pred_elim                             true
% 3.71/1.00  --res_sim_input                         true
% 3.71/1.00  --eq_ax_congr_red                       true
% 3.71/1.00  --pure_diseq_elim                       true
% 3.71/1.00  --brand_transform                       false
% 3.71/1.00  --non_eq_to_eq                          false
% 3.71/1.00  --prep_def_merge                        true
% 3.71/1.00  --prep_def_merge_prop_impl              false
% 3.71/1.00  --prep_def_merge_mbd                    true
% 3.71/1.00  --prep_def_merge_tr_red                 false
% 3.71/1.00  --prep_def_merge_tr_cl                  false
% 3.71/1.00  --smt_preprocessing                     true
% 3.71/1.00  --smt_ac_axioms                         fast
% 3.71/1.00  --preprocessed_out                      false
% 3.71/1.00  --preprocessed_stats                    false
% 3.71/1.00  
% 3.71/1.00  ------ Abstraction refinement Options
% 3.71/1.00  
% 3.71/1.00  --abstr_ref                             []
% 3.71/1.00  --abstr_ref_prep                        false
% 3.71/1.00  --abstr_ref_until_sat                   false
% 3.71/1.00  --abstr_ref_sig_restrict                funpre
% 3.71/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/1.00  --abstr_ref_under                       []
% 3.71/1.00  
% 3.71/1.00  ------ SAT Options
% 3.71/1.00  
% 3.71/1.00  --sat_mode                              false
% 3.71/1.00  --sat_fm_restart_options                ""
% 3.71/1.00  --sat_gr_def                            false
% 3.71/1.00  --sat_epr_types                         true
% 3.71/1.00  --sat_non_cyclic_types                  false
% 3.71/1.00  --sat_finite_models                     false
% 3.71/1.00  --sat_fm_lemmas                         false
% 3.71/1.00  --sat_fm_prep                           false
% 3.71/1.00  --sat_fm_uc_incr                        true
% 3.71/1.00  --sat_out_model                         small
% 3.71/1.00  --sat_out_clauses                       false
% 3.71/1.00  
% 3.71/1.00  ------ QBF Options
% 3.71/1.00  
% 3.71/1.00  --qbf_mode                              false
% 3.71/1.00  --qbf_elim_univ                         false
% 3.71/1.00  --qbf_dom_inst                          none
% 3.71/1.00  --qbf_dom_pre_inst                      false
% 3.71/1.00  --qbf_sk_in                             false
% 3.71/1.00  --qbf_pred_elim                         true
% 3.71/1.00  --qbf_split                             512
% 3.71/1.00  
% 3.71/1.00  ------ BMC1 Options
% 3.71/1.00  
% 3.71/1.00  --bmc1_incremental                      false
% 3.71/1.00  --bmc1_axioms                           reachable_all
% 3.71/1.00  --bmc1_min_bound                        0
% 3.71/1.00  --bmc1_max_bound                        -1
% 3.71/1.00  --bmc1_max_bound_default                -1
% 3.71/1.00  --bmc1_symbol_reachability              true
% 3.71/1.00  --bmc1_property_lemmas                  false
% 3.71/1.00  --bmc1_k_induction                      false
% 3.71/1.00  --bmc1_non_equiv_states                 false
% 3.71/1.00  --bmc1_deadlock                         false
% 3.71/1.00  --bmc1_ucm                              false
% 3.71/1.00  --bmc1_add_unsat_core                   none
% 3.71/1.00  --bmc1_unsat_core_children              false
% 3.71/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/1.00  --bmc1_out_stat                         full
% 3.71/1.00  --bmc1_ground_init                      false
% 3.71/1.00  --bmc1_pre_inst_next_state              false
% 3.71/1.00  --bmc1_pre_inst_state                   false
% 3.71/1.00  --bmc1_pre_inst_reach_state             false
% 3.71/1.00  --bmc1_out_unsat_core                   false
% 3.71/1.00  --bmc1_aig_witness_out                  false
% 3.71/1.00  --bmc1_verbose                          false
% 3.71/1.00  --bmc1_dump_clauses_tptp                false
% 3.71/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.71/1.00  --bmc1_dump_file                        -
% 3.71/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.71/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.71/1.00  --bmc1_ucm_extend_mode                  1
% 3.71/1.00  --bmc1_ucm_init_mode                    2
% 3.71/1.00  --bmc1_ucm_cone_mode                    none
% 3.71/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.71/1.00  --bmc1_ucm_relax_model                  4
% 3.71/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.71/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/1.00  --bmc1_ucm_layered_model                none
% 3.71/1.00  --bmc1_ucm_max_lemma_size               10
% 3.71/1.00  
% 3.71/1.00  ------ AIG Options
% 3.71/1.00  
% 3.71/1.00  --aig_mode                              false
% 3.71/1.00  
% 3.71/1.00  ------ Instantiation Options
% 3.71/1.00  
% 3.71/1.00  --instantiation_flag                    true
% 3.71/1.00  --inst_sos_flag                         false
% 3.71/1.00  --inst_sos_phase                        true
% 3.71/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/1.00  --inst_lit_sel_side                     none
% 3.71/1.00  --inst_solver_per_active                1400
% 3.71/1.00  --inst_solver_calls_frac                1.
% 3.71/1.00  --inst_passive_queue_type               priority_queues
% 3.71/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/1.00  --inst_passive_queues_freq              [25;2]
% 3.71/1.00  --inst_dismatching                      true
% 3.71/1.00  --inst_eager_unprocessed_to_passive     true
% 3.71/1.00  --inst_prop_sim_given                   true
% 3.71/1.00  --inst_prop_sim_new                     false
% 3.71/1.00  --inst_subs_new                         false
% 3.71/1.00  --inst_eq_res_simp                      false
% 3.71/1.00  --inst_subs_given                       false
% 3.71/1.00  --inst_orphan_elimination               true
% 3.71/1.00  --inst_learning_loop_flag               true
% 3.71/1.00  --inst_learning_start                   3000
% 3.71/1.00  --inst_learning_factor                  2
% 3.71/1.00  --inst_start_prop_sim_after_learn       3
% 3.71/1.00  --inst_sel_renew                        solver
% 3.71/1.00  --inst_lit_activity_flag                true
% 3.71/1.00  --inst_restr_to_given                   false
% 3.71/1.00  --inst_activity_threshold               500
% 3.71/1.00  --inst_out_proof                        true
% 3.71/1.00  
% 3.71/1.00  ------ Resolution Options
% 3.71/1.00  
% 3.71/1.00  --resolution_flag                       false
% 3.71/1.00  --res_lit_sel                           adaptive
% 3.71/1.00  --res_lit_sel_side                      none
% 3.71/1.00  --res_ordering                          kbo
% 3.71/1.00  --res_to_prop_solver                    active
% 3.71/1.00  --res_prop_simpl_new                    false
% 3.71/1.00  --res_prop_simpl_given                  true
% 3.71/1.00  --res_passive_queue_type                priority_queues
% 3.71/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/1.00  --res_passive_queues_freq               [15;5]
% 3.71/1.00  --res_forward_subs                      full
% 3.71/1.00  --res_backward_subs                     full
% 3.71/1.00  --res_forward_subs_resolution           true
% 3.71/1.00  --res_backward_subs_resolution          true
% 3.71/1.00  --res_orphan_elimination                true
% 3.71/1.00  --res_time_limit                        2.
% 3.71/1.00  --res_out_proof                         true
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Options
% 3.71/1.00  
% 3.71/1.00  --superposition_flag                    true
% 3.71/1.00  --sup_passive_queue_type                priority_queues
% 3.71/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.71/1.00  --demod_completeness_check              fast
% 3.71/1.00  --demod_use_ground                      true
% 3.71/1.00  --sup_to_prop_solver                    passive
% 3.71/1.00  --sup_prop_simpl_new                    true
% 3.71/1.00  --sup_prop_simpl_given                  true
% 3.71/1.00  --sup_fun_splitting                     false
% 3.71/1.00  --sup_smt_interval                      50000
% 3.71/1.00  
% 3.71/1.00  ------ Superposition Simplification Setup
% 3.71/1.00  
% 3.71/1.00  --sup_indices_passive                   []
% 3.71/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_full_bw                           [BwDemod]
% 3.71/1.00  --sup_immed_triv                        [TrivRules]
% 3.71/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_immed_bw_main                     []
% 3.71/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/1.00  
% 3.71/1.00  ------ Combination Options
% 3.71/1.00  
% 3.71/1.00  --comb_res_mult                         3
% 3.71/1.00  --comb_sup_mult                         2
% 3.71/1.00  --comb_inst_mult                        10
% 3.71/1.00  
% 3.71/1.00  ------ Debug Options
% 3.71/1.00  
% 3.71/1.00  --dbg_backtrace                         false
% 3.71/1.00  --dbg_dump_prop_clauses                 false
% 3.71/1.00  --dbg_dump_prop_clauses_file            -
% 3.71/1.00  --dbg_out_stat                          false
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  ------ Proving...
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  % SZS status Theorem for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  fof(f9,axiom,(
% 3.71/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f64,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f9])).
% 3.71/1.00  
% 3.71/1.00  fof(f10,axiom,(
% 3.71/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f65,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f10])).
% 3.71/1.00  
% 3.71/1.00  fof(f93,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.71/1.00    inference(definition_unfolding,[],[f64,f65,f65])).
% 3.71/1.00  
% 3.71/1.00  fof(f22,conjecture,(
% 3.71/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f23,negated_conjecture,(
% 3.71/1.00    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 3.71/1.00    inference(negated_conjecture,[],[f22])).
% 3.71/1.00  
% 3.71/1.00  fof(f38,plain,(
% 3.71/1.00    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.71/1.00    inference(ennf_transformation,[],[f23])).
% 3.71/1.00  
% 3.71/1.00  fof(f39,plain,(
% 3.71/1.00    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.71/1.00    inference(flattening,[],[f38])).
% 3.71/1.00  
% 3.71/1.00  fof(f51,plain,(
% 3.71/1.00    ( ! [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) => (k10_relat_1(X0,sK4) != k10_relat_1(k7_relat_1(X0,sK3),sK4) & r1_tarski(k10_relat_1(X0,sK4),sK3))) )),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f50,plain,(
% 3.71/1.00    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK2,X2) != k10_relat_1(k7_relat_1(sK2,X1),X2) & r1_tarski(k10_relat_1(sK2,X2),X1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 3.71/1.00    introduced(choice_axiom,[])).
% 3.71/1.00  
% 3.71/1.00  fof(f52,plain,(
% 3.71/1.00    (k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) & r1_tarski(k10_relat_1(sK2,sK4),sK3)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 3.71/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f51,f50])).
% 3.71/1.00  
% 3.71/1.00  fof(f86,plain,(
% 3.71/1.00    r1_tarski(k10_relat_1(sK2,sK4),sK3)),
% 3.71/1.00    inference(cnf_transformation,[],[f52])).
% 3.71/1.00  
% 3.71/1.00  fof(f2,axiom,(
% 3.71/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f44,plain,(
% 3.71/1.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.71/1.00    inference(nnf_transformation,[],[f2])).
% 3.71/1.00  
% 3.71/1.00  fof(f57,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f44])).
% 3.71/1.00  
% 3.71/1.00  fof(f11,axiom,(
% 3.71/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f66,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f11])).
% 3.71/1.00  
% 3.71/1.00  fof(f89,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.71/1.00    inference(definition_unfolding,[],[f57,f66])).
% 3.71/1.00  
% 3.71/1.00  fof(f12,axiom,(
% 3.71/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f67,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f12])).
% 3.71/1.00  
% 3.71/1.00  fof(f8,axiom,(
% 3.71/1.00    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f63,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f8])).
% 3.71/1.00  
% 3.71/1.00  fof(f88,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 3.71/1.00    inference(definition_unfolding,[],[f63,f66,f66])).
% 3.71/1.00  
% 3.71/1.00  fof(f94,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 3.71/1.00    inference(definition_unfolding,[],[f67,f88,f65])).
% 3.71/1.00  
% 3.71/1.00  fof(f6,axiom,(
% 3.71/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f61,plain,(
% 3.71/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.71/1.00    inference(cnf_transformation,[],[f6])).
% 3.71/1.00  
% 3.71/1.00  fof(f92,plain,(
% 3.71/1.00    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 3.71/1.00    inference(definition_unfolding,[],[f61,f66])).
% 3.71/1.00  
% 3.71/1.00  fof(f19,axiom,(
% 3.71/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f34,plain,(
% 3.71/1.00    ! [X0,X1,X2] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2))),
% 3.71/1.00    inference(ennf_transformation,[],[f19])).
% 3.71/1.00  
% 3.71/1.00  fof(f81,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k10_relat_1(X2,X1)) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f34])).
% 3.71/1.00  
% 3.71/1.00  fof(f95,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (k6_subset_1(X0,k6_subset_1(X0,k10_relat_1(X2,X1))) = k10_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.71/1.00    inference(definition_unfolding,[],[f81,f88])).
% 3.71/1.00  
% 3.71/1.00  fof(f84,plain,(
% 3.71/1.00    v1_relat_1(sK2)),
% 3.71/1.00    inference(cnf_transformation,[],[f52])).
% 3.71/1.00  
% 3.71/1.00  fof(f87,plain,(
% 3.71/1.00    k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4)),
% 3.71/1.00    inference(cnf_transformation,[],[f52])).
% 3.71/1.00  
% 3.71/1.00  cnf(c_10,plain,
% 3.71/1.00      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_29,negated_conjecture,
% 3.71/1.00      ( r1_tarski(k10_relat_1(sK2,sK4),sK3) ),
% 3.71/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1401,plain,
% 3.71/1.00      ( r1_tarski(k10_relat_1(sK2,sK4),sK3) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3,plain,
% 3.71/1.00      ( ~ r1_tarski(X0,X1) | k6_subset_1(X0,X1) = k1_xboole_0 ),
% 3.71/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1408,plain,
% 3.71/1.00      ( k6_subset_1(X0,X1) = k1_xboole_0
% 3.71/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6398,plain,
% 3.71/1.00      ( k6_subset_1(k10_relat_1(sK2,sK4),sK3) = k1_xboole_0 ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_1401,c_1408]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_11,plain,
% 3.71/1.00      ( k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6456,plain,
% 3.71/1.00      ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,sK4),k10_relat_1(sK2,sK4),sK3)) = k6_subset_1(k10_relat_1(sK2,sK4),k1_xboole_0) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_6398,c_11]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_8,plain,
% 3.71/1.00      ( k6_subset_1(X0,k1_xboole_0) = X0 ),
% 3.71/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6458,plain,
% 3.71/1.00      ( k1_setfam_1(k1_enumset1(k10_relat_1(sK2,sK4),k10_relat_1(sK2,sK4),sK3)) = k10_relat_1(sK2,sK4) ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_6456,c_8]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_9374,plain,
% 3.71/1.00      ( k1_setfam_1(k1_enumset1(sK3,sK3,k10_relat_1(sK2,sK4))) = k10_relat_1(sK2,sK4) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_10,c_6458]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_25,plain,
% 3.71/1.00      ( ~ v1_relat_1(X0)
% 3.71/1.00      | k6_subset_1(X1,k6_subset_1(X1,k10_relat_1(X0,X2))) = k10_relat_1(k7_relat_1(X0,X1),X2) ),
% 3.71/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_31,negated_conjecture,
% 3.71/1.00      ( v1_relat_1(sK2) ),
% 3.71/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_733,plain,
% 3.71/1.00      ( k6_subset_1(X0,k6_subset_1(X0,k10_relat_1(X1,X2))) = k10_relat_1(k7_relat_1(X1,X0),X2)
% 3.71/1.00      | sK2 != X1 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_31]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_734,plain,
% 3.71/1.00      ( k6_subset_1(X0,k6_subset_1(X0,k10_relat_1(sK2,X1))) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_733]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2231,plain,
% 3.71/1.00      ( k1_setfam_1(k1_enumset1(X0,X0,k10_relat_1(sK2,X1))) = k10_relat_1(k7_relat_1(sK2,X0),X1) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_11,c_734]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_9387,plain,
% 3.71/1.00      ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) = k10_relat_1(sK2,sK4) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_9374,c_2231]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_762,plain,( X0 = X0 ),theory(equality) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1732,plain,
% 3.71/1.00      ( k10_relat_1(sK2,sK4) = k10_relat_1(sK2,sK4) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_762]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_763,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1693,plain,
% 3.71/1.00      ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != X0
% 3.71/1.00      | k10_relat_1(sK2,sK4) != X0
% 3.71/1.00      | k10_relat_1(sK2,sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_763]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_1731,plain,
% 3.71/1.00      ( k10_relat_1(k7_relat_1(sK2,sK3),sK4) != k10_relat_1(sK2,sK4)
% 3.71/1.00      | k10_relat_1(sK2,sK4) = k10_relat_1(k7_relat_1(sK2,sK3),sK4)
% 3.71/1.00      | k10_relat_1(sK2,sK4) != k10_relat_1(sK2,sK4) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_1693]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_28,negated_conjecture,
% 3.71/1.00      ( k10_relat_1(sK2,sK4) != k10_relat_1(k7_relat_1(sK2,sK3),sK4) ),
% 3.71/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(contradiction,plain,
% 3.71/1.00      ( $false ),
% 3.71/1.00      inference(minisat,[status(thm)],[c_9387,c_1732,c_1731,c_28]) ).
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  ------                               Statistics
% 3.71/1.00  
% 3.71/1.00  ------ General
% 3.71/1.00  
% 3.71/1.00  abstr_ref_over_cycles:                  0
% 3.71/1.00  abstr_ref_under_cycles:                 0
% 3.71/1.00  gc_basic_clause_elim:                   0
% 3.71/1.00  forced_gc_time:                         0
% 3.71/1.00  parsing_time:                           0.009
% 3.71/1.00  unif_index_cands_time:                  0.
% 3.71/1.00  unif_index_add_time:                    0.
% 3.71/1.00  orderings_time:                         0.
% 3.71/1.00  out_proof_time:                         0.008
% 3.71/1.00  total_time:                             0.309
% 3.71/1.00  num_of_symbols:                         51
% 3.71/1.00  num_of_terms:                           11661
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing
% 3.71/1.00  
% 3.71/1.00  num_of_splits:                          0
% 3.71/1.00  num_of_split_atoms:                     0
% 3.71/1.00  num_of_reused_defs:                     0
% 3.71/1.00  num_eq_ax_congr_red:                    19
% 3.71/1.00  num_of_sem_filtered_clauses:            1
% 3.71/1.00  num_of_subtypes:                        0
% 3.71/1.00  monotx_restored_types:                  0
% 3.71/1.00  sat_num_of_epr_types:                   0
% 3.71/1.00  sat_num_of_non_cyclic_types:            0
% 3.71/1.00  sat_guarded_non_collapsed_types:        0
% 3.71/1.00  num_pure_diseq_elim:                    0
% 3.71/1.00  simp_replaced_by:                       0
% 3.71/1.00  res_preprocessed:                       137
% 3.71/1.00  prep_upred:                             0
% 3.71/1.00  prep_unflattend:                        22
% 3.71/1.00  smt_new_axioms:                         0
% 3.71/1.00  pred_elim_cands:                        4
% 3.71/1.00  pred_elim:                              2
% 3.71/1.00  pred_elim_cl:                           -7
% 3.71/1.00  pred_elim_cycles:                       3
% 3.71/1.00  merged_defs:                            6
% 3.71/1.00  merged_defs_ncl:                        0
% 3.71/1.00  bin_hyper_res:                          6
% 3.71/1.00  prep_cycles:                            3
% 3.71/1.00  pred_elim_time:                         0.011
% 3.71/1.00  splitting_time:                         0.
% 3.71/1.00  sem_filter_time:                        0.
% 3.71/1.00  monotx_time:                            0.
% 3.71/1.00  subtype_inf_time:                       0.
% 3.71/1.00  
% 3.71/1.00  ------ Problem properties
% 3.71/1.00  
% 3.71/1.00  clauses:                                39
% 3.71/1.00  conjectures:                            2
% 3.71/1.00  epr:                                    5
% 3.71/1.00  horn:                                   34
% 3.71/1.00  ground:                                 3
% 3.71/1.00  unary:                                  17
% 3.71/1.00  binary:                                 12
% 3.71/1.00  lits:                                   73
% 3.71/1.00  lits_eq:                                23
% 3.71/1.00  fd_pure:                                0
% 3.71/1.00  fd_pseudo:                              0
% 3.71/1.00  fd_cond:                                1
% 3.71/1.00  fd_pseudo_cond:                         6
% 3.71/1.00  ac_symbols:                             0
% 3.71/1.00  
% 3.71/1.00  ------ Propositional Solver
% 3.71/1.00  
% 3.71/1.00  prop_solver_calls:                      24
% 3.71/1.00  prop_fast_solver_calls:                 786
% 3.71/1.00  smt_solver_calls:                       0
% 3.71/1.00  smt_fast_solver_calls:                  0
% 3.71/1.00  prop_num_of_clauses:                    3484
% 3.71/1.00  prop_preprocess_simplified:             6687
% 3.71/1.00  prop_fo_subsumed:                       12
% 3.71/1.00  prop_solver_time:                       0.
% 3.71/1.00  smt_solver_time:                        0.
% 3.71/1.00  smt_fast_solver_time:                   0.
% 3.71/1.00  prop_fast_solver_time:                  0.
% 3.71/1.00  prop_unsat_core_time:                   0.
% 3.71/1.00  
% 3.71/1.00  ------ QBF
% 3.71/1.00  
% 3.71/1.00  qbf_q_res:                              0
% 3.71/1.00  qbf_num_tautologies:                    0
% 3.71/1.00  qbf_prep_cycles:                        0
% 3.71/1.00  
% 3.71/1.00  ------ BMC1
% 3.71/1.00  
% 3.71/1.00  bmc1_current_bound:                     -1
% 3.71/1.00  bmc1_last_solved_bound:                 -1
% 3.71/1.00  bmc1_unsat_core_size:                   -1
% 3.71/1.00  bmc1_unsat_core_parents_size:           -1
% 3.71/1.00  bmc1_merge_next_fun:                    0
% 3.71/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.71/1.00  
% 3.71/1.00  ------ Instantiation
% 3.71/1.00  
% 3.71/1.00  inst_num_of_clauses:                    727
% 3.71/1.00  inst_num_in_passive:                    188
% 3.71/1.00  inst_num_in_active:                     340
% 3.71/1.00  inst_num_in_unprocessed:                199
% 3.71/1.00  inst_num_of_loops:                      440
% 3.71/1.00  inst_num_of_learning_restarts:          0
% 3.71/1.00  inst_num_moves_active_passive:          97
% 3.71/1.00  inst_lit_activity:                      0
% 3.71/1.00  inst_lit_activity_moves:                0
% 3.71/1.00  inst_num_tautologies:                   0
% 3.71/1.00  inst_num_prop_implied:                  0
% 3.71/1.00  inst_num_existing_simplified:           0
% 3.71/1.00  inst_num_eq_res_simplified:             0
% 3.71/1.00  inst_num_child_elim:                    0
% 3.71/1.00  inst_num_of_dismatching_blockings:      188
% 3.71/1.00  inst_num_of_non_proper_insts:           582
% 3.71/1.00  inst_num_of_duplicates:                 0
% 3.71/1.00  inst_inst_num_from_inst_to_res:         0
% 3.71/1.00  inst_dismatching_checking_time:         0.
% 3.71/1.00  
% 3.71/1.00  ------ Resolution
% 3.71/1.00  
% 3.71/1.00  res_num_of_clauses:                     0
% 3.71/1.00  res_num_in_passive:                     0
% 3.71/1.00  res_num_in_active:                      0
% 3.71/1.00  res_num_of_loops:                       140
% 3.71/1.00  res_forward_subset_subsumed:            36
% 3.71/1.00  res_backward_subset_subsumed:           0
% 3.71/1.00  res_forward_subsumed:                   0
% 3.71/1.00  res_backward_subsumed:                  0
% 3.71/1.00  res_forward_subsumption_resolution:     4
% 3.71/1.00  res_backward_subsumption_resolution:    0
% 3.71/1.00  res_clause_to_clause_subsumption:       1649
% 3.71/1.00  res_orphan_elimination:                 0
% 3.71/1.00  res_tautology_del:                      51
% 3.71/1.00  res_num_eq_res_simplified:              0
% 3.71/1.00  res_num_sel_changes:                    0
% 3.71/1.00  res_moves_from_active_to_pass:          0
% 3.71/1.00  
% 3.71/1.00  ------ Superposition
% 3.71/1.00  
% 3.71/1.00  sup_time_total:                         0.
% 3.71/1.00  sup_time_generating:                    0.
% 3.71/1.00  sup_time_sim_full:                      0.
% 3.71/1.00  sup_time_sim_immed:                     0.
% 3.71/1.00  
% 3.71/1.00  sup_num_of_clauses:                     618
% 3.71/1.00  sup_num_in_active:                      88
% 3.71/1.00  sup_num_in_passive:                     530
% 3.71/1.00  sup_num_of_loops:                       87
% 3.71/1.00  sup_fw_superposition:                   401
% 3.71/1.00  sup_bw_superposition:                   463
% 3.71/1.00  sup_immediate_simplified:               368
% 3.71/1.00  sup_given_eliminated:                   0
% 3.71/1.00  comparisons_done:                       0
% 3.71/1.00  comparisons_avoided:                    0
% 3.71/1.00  
% 3.71/1.00  ------ Simplifications
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  sim_fw_subset_subsumed:                 5
% 3.71/1.00  sim_bw_subset_subsumed:                 1
% 3.71/1.00  sim_fw_subsumed:                        116
% 3.71/1.00  sim_bw_subsumed:                        12
% 3.71/1.00  sim_fw_subsumption_res:                 0
% 3.71/1.00  sim_bw_subsumption_res:                 0
% 3.71/1.00  sim_tautology_del:                      3
% 3.71/1.00  sim_eq_tautology_del:                   18
% 3.71/1.00  sim_eq_res_simp:                        1
% 3.71/1.00  sim_fw_demodulated:                     160
% 3.71/1.00  sim_bw_demodulated:                     24
% 3.71/1.00  sim_light_normalised:                   113
% 3.71/1.00  sim_joinable_taut:                      0
% 3.71/1.00  sim_joinable_simp:                      0
% 3.71/1.00  sim_ac_normalised:                      0
% 3.71/1.00  sim_smt_subsumption:                    0
% 3.71/1.00  
%------------------------------------------------------------------------------
