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
% DateTime   : Thu Dec  3 11:23:05 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 344 expanded)
%              Number of clauses        :   41 ( 134 expanded)
%              Number of leaves         :    9 (  71 expanded)
%              Depth                    :   19
%              Number of atoms          :  125 ( 731 expanded)
%              Number of equality atoms :   62 ( 256 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r1_tarski(sK1,sK2)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r1_tarski(sK1,sK2)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).

fof(f32,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f15])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f30,f29])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_11,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_419,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_12,negated_conjecture,
    ( r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_147,plain,
    ( r1_tarski(X0,X1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_12])).

cnf(c_148,plain,
    ( r1_tarski(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_147])).

cnf(c_417,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_148])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_422,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1021,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_417,c_422])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1143,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1021,c_8])).

cnf(c_1020,plain,
    ( k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_419,c_422])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_9,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_621,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_9])).

cnf(c_729,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_621,c_8])).

cnf(c_810,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_729])).

cnf(c_1028,plain,
    ( k2_xboole_0(sK1,k1_xboole_0) = sK1 ),
    inference(superposition,[status(thm)],[c_1020,c_810])).

cnf(c_1558,plain,
    ( k2_xboole_0(sK1,sK0) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1143,c_1028])).

cnf(c_7,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_420,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_710,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X2,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_420])).

cnf(c_1565,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | r1_tarski(sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1558,c_710])).

cnf(c_3479,plain,
    ( r1_tarski(sK0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_419,c_1565])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_10,negated_conjecture,
    ( ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_137,plain,
    ( ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_10])).

cnf(c_138,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK2 = sK0 ),
    inference(unflattening,[status(thm)],[c_137])).

cnf(c_418,plain,
    ( sK2 = sK0
    | r1_tarski(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_138])).

cnf(c_3588,plain,
    ( sK2 = sK0 ),
    inference(superposition,[status(thm)],[c_3479,c_418])).

cnf(c_1034,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1020,c_8])).

cnf(c_3605,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_3588,c_1034])).

cnf(c_1137,plain,
    ( k2_xboole_0(sK0,k1_xboole_0) = sK0 ),
    inference(superposition,[status(thm)],[c_1021,c_810])).

cnf(c_1560,plain,
    ( k2_xboole_0(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_0,c_1558])).

cnf(c_3616,plain,
    ( sK1 = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3605,c_1137,c_1560])).

cnf(c_159,plain,
    ( sK1 != sK2
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_12])).

cnf(c_180,plain,
    ( sK1 != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_159])).

cnf(c_3607,plain,
    ( sK1 != sK0 ),
    inference(demodulation,[status(thm)],[c_3588,c_180])).

cnf(c_3618,plain,
    ( sK0 != sK0 ),
    inference(demodulation,[status(thm)],[c_3616,c_3607])).

cnf(c_3621,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3618])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:10:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.74/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.01  
% 2.74/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.74/1.01  
% 2.74/1.01  ------  iProver source info
% 2.74/1.01  
% 2.74/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.74/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.74/1.01  git: non_committed_changes: false
% 2.74/1.01  git: last_make_outside_of_git: false
% 2.74/1.01  
% 2.74/1.01  ------ 
% 2.74/1.01  
% 2.74/1.01  ------ Input Options
% 2.74/1.01  
% 2.74/1.01  --out_options                           all
% 2.74/1.01  --tptp_safe_out                         true
% 2.74/1.01  --problem_path                          ""
% 2.74/1.01  --include_path                          ""
% 2.74/1.01  --clausifier                            res/vclausify_rel
% 2.74/1.01  --clausifier_options                    --mode clausify
% 2.74/1.01  --stdin                                 false
% 2.74/1.01  --stats_out                             all
% 2.74/1.01  
% 2.74/1.01  ------ General Options
% 2.74/1.01  
% 2.74/1.01  --fof                                   false
% 2.74/1.01  --time_out_real                         305.
% 2.74/1.01  --time_out_virtual                      -1.
% 2.74/1.01  --symbol_type_check                     false
% 2.74/1.01  --clausify_out                          false
% 2.74/1.01  --sig_cnt_out                           false
% 2.74/1.01  --trig_cnt_out                          false
% 2.74/1.01  --trig_cnt_out_tolerance                1.
% 2.74/1.01  --trig_cnt_out_sk_spl                   false
% 2.74/1.01  --abstr_cl_out                          false
% 2.74/1.01  
% 2.74/1.01  ------ Global Options
% 2.74/1.01  
% 2.74/1.01  --schedule                              default
% 2.74/1.01  --add_important_lit                     false
% 2.74/1.01  --prop_solver_per_cl                    1000
% 2.74/1.01  --min_unsat_core                        false
% 2.74/1.01  --soft_assumptions                      false
% 2.74/1.01  --soft_lemma_size                       3
% 2.74/1.01  --prop_impl_unit_size                   0
% 2.74/1.01  --prop_impl_unit                        []
% 2.74/1.01  --share_sel_clauses                     true
% 2.74/1.01  --reset_solvers                         false
% 2.74/1.01  --bc_imp_inh                            [conj_cone]
% 2.74/1.01  --conj_cone_tolerance                   3.
% 2.74/1.01  --extra_neg_conj                        none
% 2.74/1.01  --large_theory_mode                     true
% 2.74/1.01  --prolific_symb_bound                   200
% 2.74/1.01  --lt_threshold                          2000
% 2.74/1.01  --clause_weak_htbl                      true
% 2.74/1.01  --gc_record_bc_elim                     false
% 2.74/1.01  
% 2.74/1.01  ------ Preprocessing Options
% 2.74/1.01  
% 2.74/1.01  --preprocessing_flag                    true
% 2.74/1.01  --time_out_prep_mult                    0.1
% 2.74/1.01  --splitting_mode                        input
% 2.74/1.01  --splitting_grd                         true
% 2.74/1.01  --splitting_cvd                         false
% 2.74/1.01  --splitting_cvd_svl                     false
% 2.74/1.01  --splitting_nvd                         32
% 2.74/1.01  --sub_typing                            true
% 2.74/1.01  --prep_gs_sim                           true
% 2.74/1.01  --prep_unflatten                        true
% 2.74/1.01  --prep_res_sim                          true
% 2.74/1.01  --prep_upred                            true
% 2.74/1.01  --prep_sem_filter                       exhaustive
% 2.74/1.01  --prep_sem_filter_out                   false
% 2.74/1.01  --pred_elim                             true
% 2.74/1.01  --res_sim_input                         true
% 2.74/1.01  --eq_ax_congr_red                       true
% 2.74/1.01  --pure_diseq_elim                       true
% 2.74/1.01  --brand_transform                       false
% 2.74/1.01  --non_eq_to_eq                          false
% 2.74/1.01  --prep_def_merge                        true
% 2.74/1.01  --prep_def_merge_prop_impl              false
% 2.74/1.01  --prep_def_merge_mbd                    true
% 2.74/1.01  --prep_def_merge_tr_red                 false
% 2.74/1.01  --prep_def_merge_tr_cl                  false
% 2.74/1.01  --smt_preprocessing                     true
% 2.74/1.01  --smt_ac_axioms                         fast
% 2.74/1.01  --preprocessed_out                      false
% 2.74/1.01  --preprocessed_stats                    false
% 2.74/1.01  
% 2.74/1.01  ------ Abstraction refinement Options
% 2.74/1.01  
% 2.74/1.01  --abstr_ref                             []
% 2.74/1.01  --abstr_ref_prep                        false
% 2.74/1.01  --abstr_ref_until_sat                   false
% 2.74/1.01  --abstr_ref_sig_restrict                funpre
% 2.74/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/1.01  --abstr_ref_under                       []
% 2.74/1.01  
% 2.74/1.01  ------ SAT Options
% 2.74/1.01  
% 2.74/1.01  --sat_mode                              false
% 2.74/1.01  --sat_fm_restart_options                ""
% 2.74/1.01  --sat_gr_def                            false
% 2.74/1.01  --sat_epr_types                         true
% 2.74/1.01  --sat_non_cyclic_types                  false
% 2.74/1.01  --sat_finite_models                     false
% 2.74/1.01  --sat_fm_lemmas                         false
% 2.74/1.01  --sat_fm_prep                           false
% 2.74/1.01  --sat_fm_uc_incr                        true
% 2.74/1.01  --sat_out_model                         small
% 2.74/1.01  --sat_out_clauses                       false
% 2.74/1.01  
% 2.74/1.01  ------ QBF Options
% 2.74/1.01  
% 2.74/1.01  --qbf_mode                              false
% 2.74/1.01  --qbf_elim_univ                         false
% 2.74/1.01  --qbf_dom_inst                          none
% 2.74/1.01  --qbf_dom_pre_inst                      false
% 2.74/1.01  --qbf_sk_in                             false
% 2.74/1.01  --qbf_pred_elim                         true
% 2.74/1.01  --qbf_split                             512
% 2.74/1.01  
% 2.74/1.01  ------ BMC1 Options
% 2.74/1.01  
% 2.74/1.01  --bmc1_incremental                      false
% 2.74/1.01  --bmc1_axioms                           reachable_all
% 2.74/1.01  --bmc1_min_bound                        0
% 2.74/1.01  --bmc1_max_bound                        -1
% 2.74/1.01  --bmc1_max_bound_default                -1
% 2.74/1.01  --bmc1_symbol_reachability              true
% 2.74/1.01  --bmc1_property_lemmas                  false
% 2.74/1.01  --bmc1_k_induction                      false
% 2.74/1.01  --bmc1_non_equiv_states                 false
% 2.74/1.01  --bmc1_deadlock                         false
% 2.74/1.01  --bmc1_ucm                              false
% 2.74/1.01  --bmc1_add_unsat_core                   none
% 2.74/1.01  --bmc1_unsat_core_children              false
% 2.74/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/1.01  --bmc1_out_stat                         full
% 2.74/1.01  --bmc1_ground_init                      false
% 2.74/1.01  --bmc1_pre_inst_next_state              false
% 2.74/1.01  --bmc1_pre_inst_state                   false
% 2.74/1.01  --bmc1_pre_inst_reach_state             false
% 2.74/1.01  --bmc1_out_unsat_core                   false
% 2.74/1.01  --bmc1_aig_witness_out                  false
% 2.74/1.01  --bmc1_verbose                          false
% 2.74/1.01  --bmc1_dump_clauses_tptp                false
% 2.74/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.74/1.01  --bmc1_dump_file                        -
% 2.74/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.74/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.74/1.01  --bmc1_ucm_extend_mode                  1
% 2.74/1.01  --bmc1_ucm_init_mode                    2
% 2.74/1.01  --bmc1_ucm_cone_mode                    none
% 2.74/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.74/1.01  --bmc1_ucm_relax_model                  4
% 2.74/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.74/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/1.01  --bmc1_ucm_layered_model                none
% 2.74/1.01  --bmc1_ucm_max_lemma_size               10
% 2.74/1.01  
% 2.74/1.01  ------ AIG Options
% 2.74/1.01  
% 2.74/1.01  --aig_mode                              false
% 2.74/1.01  
% 2.74/1.01  ------ Instantiation Options
% 2.74/1.01  
% 2.74/1.01  --instantiation_flag                    true
% 2.74/1.01  --inst_sos_flag                         false
% 2.74/1.01  --inst_sos_phase                        true
% 2.74/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/1.01  --inst_lit_sel_side                     num_symb
% 2.74/1.01  --inst_solver_per_active                1400
% 2.74/1.01  --inst_solver_calls_frac                1.
% 2.74/1.01  --inst_passive_queue_type               priority_queues
% 2.74/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/1.01  --inst_passive_queues_freq              [25;2]
% 2.74/1.01  --inst_dismatching                      true
% 2.74/1.01  --inst_eager_unprocessed_to_passive     true
% 2.74/1.01  --inst_prop_sim_given                   true
% 2.74/1.01  --inst_prop_sim_new                     false
% 2.74/1.01  --inst_subs_new                         false
% 2.74/1.01  --inst_eq_res_simp                      false
% 2.74/1.01  --inst_subs_given                       false
% 2.74/1.01  --inst_orphan_elimination               true
% 2.74/1.01  --inst_learning_loop_flag               true
% 2.74/1.01  --inst_learning_start                   3000
% 2.74/1.01  --inst_learning_factor                  2
% 2.74/1.01  --inst_start_prop_sim_after_learn       3
% 2.74/1.01  --inst_sel_renew                        solver
% 2.74/1.01  --inst_lit_activity_flag                true
% 2.74/1.01  --inst_restr_to_given                   false
% 2.74/1.01  --inst_activity_threshold               500
% 2.74/1.01  --inst_out_proof                        true
% 2.74/1.01  
% 2.74/1.01  ------ Resolution Options
% 2.74/1.01  
% 2.74/1.01  --resolution_flag                       true
% 2.74/1.01  --res_lit_sel                           adaptive
% 2.74/1.01  --res_lit_sel_side                      none
% 2.74/1.01  --res_ordering                          kbo
% 2.74/1.01  --res_to_prop_solver                    active
% 2.74/1.01  --res_prop_simpl_new                    false
% 2.74/1.01  --res_prop_simpl_given                  true
% 2.74/1.01  --res_passive_queue_type                priority_queues
% 2.74/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/1.01  --res_passive_queues_freq               [15;5]
% 2.74/1.01  --res_forward_subs                      full
% 2.74/1.01  --res_backward_subs                     full
% 2.74/1.01  --res_forward_subs_resolution           true
% 2.74/1.01  --res_backward_subs_resolution          true
% 2.74/1.01  --res_orphan_elimination                true
% 2.74/1.01  --res_time_limit                        2.
% 2.74/1.01  --res_out_proof                         true
% 2.74/1.01  
% 2.74/1.01  ------ Superposition Options
% 2.74/1.01  
% 2.74/1.01  --superposition_flag                    true
% 2.74/1.01  --sup_passive_queue_type                priority_queues
% 2.74/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.74/1.01  --demod_completeness_check              fast
% 2.74/1.01  --demod_use_ground                      true
% 2.74/1.01  --sup_to_prop_solver                    passive
% 2.74/1.01  --sup_prop_simpl_new                    true
% 2.74/1.01  --sup_prop_simpl_given                  true
% 2.74/1.01  --sup_fun_splitting                     false
% 2.74/1.01  --sup_smt_interval                      50000
% 2.74/1.01  
% 2.74/1.01  ------ Superposition Simplification Setup
% 2.74/1.01  
% 2.74/1.01  --sup_indices_passive                   []
% 2.74/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.01  --sup_full_bw                           [BwDemod]
% 2.74/1.01  --sup_immed_triv                        [TrivRules]
% 2.74/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.01  --sup_immed_bw_main                     []
% 2.74/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/1.01  
% 2.74/1.01  ------ Combination Options
% 2.74/1.01  
% 2.74/1.01  --comb_res_mult                         3
% 2.74/1.01  --comb_sup_mult                         2
% 2.74/1.01  --comb_inst_mult                        10
% 2.74/1.01  
% 2.74/1.01  ------ Debug Options
% 2.74/1.01  
% 2.74/1.01  --dbg_backtrace                         false
% 2.74/1.01  --dbg_dump_prop_clauses                 false
% 2.74/1.01  --dbg_dump_prop_clauses_file            -
% 2.74/1.01  --dbg_out_stat                          false
% 2.74/1.01  ------ Parsing...
% 2.74/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.74/1.01  
% 2.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.74/1.01  
% 2.74/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.74/1.01  
% 2.74/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.74/1.01  ------ Proving...
% 2.74/1.01  ------ Problem Properties 
% 2.74/1.01  
% 2.74/1.01  
% 2.74/1.01  clauses                                 11
% 2.74/1.01  conjectures                             1
% 2.74/1.01  EPR                                     5
% 2.74/1.01  Horn                                    11
% 2.74/1.01  unary                                   7
% 2.74/1.01  binary                                  4
% 2.74/1.01  lits                                    15
% 2.74/1.01  lits eq                                 8
% 2.74/1.01  fd_pure                                 0
% 2.74/1.01  fd_pseudo                               0
% 2.74/1.01  fd_cond                                 0
% 2.74/1.01  fd_pseudo_cond                          0
% 2.74/1.01  AC symbols                              0
% 2.74/1.01  
% 2.74/1.01  ------ Schedule dynamic 5 is on 
% 2.74/1.01  
% 2.74/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.74/1.01  
% 2.74/1.01  
% 2.74/1.01  ------ 
% 2.74/1.01  Current options:
% 2.74/1.01  ------ 
% 2.74/1.01  
% 2.74/1.01  ------ Input Options
% 2.74/1.01  
% 2.74/1.01  --out_options                           all
% 2.74/1.01  --tptp_safe_out                         true
% 2.74/1.01  --problem_path                          ""
% 2.74/1.01  --include_path                          ""
% 2.74/1.01  --clausifier                            res/vclausify_rel
% 2.74/1.01  --clausifier_options                    --mode clausify
% 2.74/1.01  --stdin                                 false
% 2.74/1.01  --stats_out                             all
% 2.74/1.01  
% 2.74/1.01  ------ General Options
% 2.74/1.01  
% 2.74/1.01  --fof                                   false
% 2.74/1.01  --time_out_real                         305.
% 2.74/1.01  --time_out_virtual                      -1.
% 2.74/1.01  --symbol_type_check                     false
% 2.74/1.01  --clausify_out                          false
% 2.74/1.01  --sig_cnt_out                           false
% 2.74/1.01  --trig_cnt_out                          false
% 2.74/1.01  --trig_cnt_out_tolerance                1.
% 2.74/1.01  --trig_cnt_out_sk_spl                   false
% 2.74/1.01  --abstr_cl_out                          false
% 2.74/1.01  
% 2.74/1.01  ------ Global Options
% 2.74/1.01  
% 2.74/1.01  --schedule                              default
% 2.74/1.01  --add_important_lit                     false
% 2.74/1.01  --prop_solver_per_cl                    1000
% 2.74/1.01  --min_unsat_core                        false
% 2.74/1.01  --soft_assumptions                      false
% 2.74/1.01  --soft_lemma_size                       3
% 2.74/1.01  --prop_impl_unit_size                   0
% 2.74/1.01  --prop_impl_unit                        []
% 2.74/1.01  --share_sel_clauses                     true
% 2.74/1.01  --reset_solvers                         false
% 2.74/1.01  --bc_imp_inh                            [conj_cone]
% 2.74/1.01  --conj_cone_tolerance                   3.
% 2.74/1.02  --extra_neg_conj                        none
% 2.74/1.02  --large_theory_mode                     true
% 2.74/1.02  --prolific_symb_bound                   200
% 2.74/1.02  --lt_threshold                          2000
% 2.74/1.02  --clause_weak_htbl                      true
% 2.74/1.02  --gc_record_bc_elim                     false
% 2.74/1.02  
% 2.74/1.02  ------ Preprocessing Options
% 2.74/1.02  
% 2.74/1.02  --preprocessing_flag                    true
% 2.74/1.02  --time_out_prep_mult                    0.1
% 2.74/1.02  --splitting_mode                        input
% 2.74/1.02  --splitting_grd                         true
% 2.74/1.02  --splitting_cvd                         false
% 2.74/1.02  --splitting_cvd_svl                     false
% 2.74/1.02  --splitting_nvd                         32
% 2.74/1.02  --sub_typing                            true
% 2.74/1.02  --prep_gs_sim                           true
% 2.74/1.02  --prep_unflatten                        true
% 2.74/1.02  --prep_res_sim                          true
% 2.74/1.02  --prep_upred                            true
% 2.74/1.02  --prep_sem_filter                       exhaustive
% 2.74/1.02  --prep_sem_filter_out                   false
% 2.74/1.02  --pred_elim                             true
% 2.74/1.02  --res_sim_input                         true
% 2.74/1.02  --eq_ax_congr_red                       true
% 2.74/1.02  --pure_diseq_elim                       true
% 2.74/1.02  --brand_transform                       false
% 2.74/1.02  --non_eq_to_eq                          false
% 2.74/1.02  --prep_def_merge                        true
% 2.74/1.02  --prep_def_merge_prop_impl              false
% 2.74/1.02  --prep_def_merge_mbd                    true
% 2.74/1.02  --prep_def_merge_tr_red                 false
% 2.74/1.02  --prep_def_merge_tr_cl                  false
% 2.74/1.02  --smt_preprocessing                     true
% 2.74/1.02  --smt_ac_axioms                         fast
% 2.74/1.02  --preprocessed_out                      false
% 2.74/1.02  --preprocessed_stats                    false
% 2.74/1.02  
% 2.74/1.02  ------ Abstraction refinement Options
% 2.74/1.02  
% 2.74/1.02  --abstr_ref                             []
% 2.74/1.02  --abstr_ref_prep                        false
% 2.74/1.02  --abstr_ref_until_sat                   false
% 2.74/1.02  --abstr_ref_sig_restrict                funpre
% 2.74/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.74/1.02  --abstr_ref_under                       []
% 2.74/1.02  
% 2.74/1.02  ------ SAT Options
% 2.74/1.02  
% 2.74/1.02  --sat_mode                              false
% 2.74/1.02  --sat_fm_restart_options                ""
% 2.74/1.02  --sat_gr_def                            false
% 2.74/1.02  --sat_epr_types                         true
% 2.74/1.02  --sat_non_cyclic_types                  false
% 2.74/1.02  --sat_finite_models                     false
% 2.74/1.02  --sat_fm_lemmas                         false
% 2.74/1.02  --sat_fm_prep                           false
% 2.74/1.02  --sat_fm_uc_incr                        true
% 2.74/1.02  --sat_out_model                         small
% 2.74/1.02  --sat_out_clauses                       false
% 2.74/1.02  
% 2.74/1.02  ------ QBF Options
% 2.74/1.02  
% 2.74/1.02  --qbf_mode                              false
% 2.74/1.02  --qbf_elim_univ                         false
% 2.74/1.02  --qbf_dom_inst                          none
% 2.74/1.02  --qbf_dom_pre_inst                      false
% 2.74/1.02  --qbf_sk_in                             false
% 2.74/1.02  --qbf_pred_elim                         true
% 2.74/1.02  --qbf_split                             512
% 2.74/1.02  
% 2.74/1.02  ------ BMC1 Options
% 2.74/1.02  
% 2.74/1.02  --bmc1_incremental                      false
% 2.74/1.02  --bmc1_axioms                           reachable_all
% 2.74/1.02  --bmc1_min_bound                        0
% 2.74/1.02  --bmc1_max_bound                        -1
% 2.74/1.02  --bmc1_max_bound_default                -1
% 2.74/1.02  --bmc1_symbol_reachability              true
% 2.74/1.02  --bmc1_property_lemmas                  false
% 2.74/1.02  --bmc1_k_induction                      false
% 2.74/1.02  --bmc1_non_equiv_states                 false
% 2.74/1.02  --bmc1_deadlock                         false
% 2.74/1.02  --bmc1_ucm                              false
% 2.74/1.02  --bmc1_add_unsat_core                   none
% 2.74/1.02  --bmc1_unsat_core_children              false
% 2.74/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.74/1.02  --bmc1_out_stat                         full
% 2.74/1.02  --bmc1_ground_init                      false
% 2.74/1.02  --bmc1_pre_inst_next_state              false
% 2.74/1.02  --bmc1_pre_inst_state                   false
% 2.74/1.02  --bmc1_pre_inst_reach_state             false
% 2.74/1.02  --bmc1_out_unsat_core                   false
% 2.74/1.02  --bmc1_aig_witness_out                  false
% 2.74/1.02  --bmc1_verbose                          false
% 2.74/1.02  --bmc1_dump_clauses_tptp                false
% 2.74/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.74/1.02  --bmc1_dump_file                        -
% 2.74/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.74/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.74/1.02  --bmc1_ucm_extend_mode                  1
% 2.74/1.02  --bmc1_ucm_init_mode                    2
% 2.74/1.02  --bmc1_ucm_cone_mode                    none
% 2.74/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.74/1.02  --bmc1_ucm_relax_model                  4
% 2.74/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.74/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.74/1.02  --bmc1_ucm_layered_model                none
% 2.74/1.02  --bmc1_ucm_max_lemma_size               10
% 2.74/1.02  
% 2.74/1.02  ------ AIG Options
% 2.74/1.02  
% 2.74/1.02  --aig_mode                              false
% 2.74/1.02  
% 2.74/1.02  ------ Instantiation Options
% 2.74/1.02  
% 2.74/1.02  --instantiation_flag                    true
% 2.74/1.02  --inst_sos_flag                         false
% 2.74/1.02  --inst_sos_phase                        true
% 2.74/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.74/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.74/1.02  --inst_lit_sel_side                     none
% 2.74/1.02  --inst_solver_per_active                1400
% 2.74/1.02  --inst_solver_calls_frac                1.
% 2.74/1.02  --inst_passive_queue_type               priority_queues
% 2.74/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.74/1.02  --inst_passive_queues_freq              [25;2]
% 2.74/1.02  --inst_dismatching                      true
% 2.74/1.02  --inst_eager_unprocessed_to_passive     true
% 2.74/1.02  --inst_prop_sim_given                   true
% 2.74/1.02  --inst_prop_sim_new                     false
% 2.74/1.02  --inst_subs_new                         false
% 2.74/1.02  --inst_eq_res_simp                      false
% 2.74/1.02  --inst_subs_given                       false
% 2.74/1.02  --inst_orphan_elimination               true
% 2.74/1.02  --inst_learning_loop_flag               true
% 2.74/1.02  --inst_learning_start                   3000
% 2.74/1.02  --inst_learning_factor                  2
% 2.74/1.02  --inst_start_prop_sim_after_learn       3
% 2.74/1.02  --inst_sel_renew                        solver
% 2.74/1.02  --inst_lit_activity_flag                true
% 2.74/1.02  --inst_restr_to_given                   false
% 2.74/1.02  --inst_activity_threshold               500
% 2.74/1.02  --inst_out_proof                        true
% 2.74/1.02  
% 2.74/1.02  ------ Resolution Options
% 2.74/1.02  
% 2.74/1.02  --resolution_flag                       false
% 2.74/1.02  --res_lit_sel                           adaptive
% 2.74/1.02  --res_lit_sel_side                      none
% 2.74/1.02  --res_ordering                          kbo
% 2.74/1.02  --res_to_prop_solver                    active
% 2.74/1.02  --res_prop_simpl_new                    false
% 2.74/1.02  --res_prop_simpl_given                  true
% 2.74/1.02  --res_passive_queue_type                priority_queues
% 2.74/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.74/1.02  --res_passive_queues_freq               [15;5]
% 2.74/1.02  --res_forward_subs                      full
% 2.74/1.02  --res_backward_subs                     full
% 2.74/1.02  --res_forward_subs_resolution           true
% 2.74/1.02  --res_backward_subs_resolution          true
% 2.74/1.02  --res_orphan_elimination                true
% 2.74/1.02  --res_time_limit                        2.
% 2.74/1.02  --res_out_proof                         true
% 2.74/1.02  
% 2.74/1.02  ------ Superposition Options
% 2.74/1.02  
% 2.74/1.02  --superposition_flag                    true
% 2.74/1.02  --sup_passive_queue_type                priority_queues
% 2.74/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.74/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.74/1.02  --demod_completeness_check              fast
% 2.74/1.02  --demod_use_ground                      true
% 2.74/1.02  --sup_to_prop_solver                    passive
% 2.74/1.02  --sup_prop_simpl_new                    true
% 2.74/1.02  --sup_prop_simpl_given                  true
% 2.74/1.02  --sup_fun_splitting                     false
% 2.74/1.02  --sup_smt_interval                      50000
% 2.74/1.02  
% 2.74/1.02  ------ Superposition Simplification Setup
% 2.74/1.02  
% 2.74/1.02  --sup_indices_passive                   []
% 2.74/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.74/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.74/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.02  --sup_full_bw                           [BwDemod]
% 2.74/1.02  --sup_immed_triv                        [TrivRules]
% 2.74/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.74/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.02  --sup_immed_bw_main                     []
% 2.74/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.74/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.74/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.74/1.02  
% 2.74/1.02  ------ Combination Options
% 2.74/1.02  
% 2.74/1.02  --comb_res_mult                         3
% 2.74/1.02  --comb_sup_mult                         2
% 2.74/1.02  --comb_inst_mult                        10
% 2.74/1.02  
% 2.74/1.02  ------ Debug Options
% 2.74/1.02  
% 2.74/1.02  --dbg_backtrace                         false
% 2.74/1.02  --dbg_dump_prop_clauses                 false
% 2.74/1.02  --dbg_dump_prop_clauses_file            -
% 2.74/1.02  --dbg_out_stat                          false
% 2.74/1.02  
% 2.74/1.02  
% 2.74/1.02  
% 2.74/1.02  
% 2.74/1.02  ------ Proving...
% 2.74/1.02  
% 2.74/1.02  
% 2.74/1.02  % SZS status Theorem for theBenchmark.p
% 2.74/1.02  
% 2.74/1.02   Resolution empty clause
% 2.74/1.02  
% 2.74/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.74/1.02  
% 2.74/1.02  fof(f9,conjecture,(
% 2.74/1.02    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 2.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.02  
% 2.74/1.02  fof(f10,negated_conjecture,(
% 2.74/1.02    ~! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 2.74/1.02    inference(negated_conjecture,[],[f9])).
% 2.74/1.02  
% 2.74/1.02  fof(f13,plain,(
% 2.74/1.02    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r1_tarski(X1,X2) & r2_xboole_0(X0,X1)))),
% 2.74/1.02    inference(ennf_transformation,[],[f10])).
% 2.74/1.02  
% 2.74/1.02  fof(f14,plain,(
% 2.74/1.02    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1))),
% 2.74/1.02    inference(flattening,[],[f13])).
% 2.74/1.02  
% 2.74/1.02  fof(f18,plain,(
% 2.74/1.02    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => (~r2_xboole_0(sK0,sK2) & r1_tarski(sK1,sK2) & r2_xboole_0(sK0,sK1))),
% 2.74/1.02    introduced(choice_axiom,[])).
% 2.74/1.02  
% 2.74/1.02  fof(f19,plain,(
% 2.74/1.02    ~r2_xboole_0(sK0,sK2) & r1_tarski(sK1,sK2) & r2_xboole_0(sK0,sK1)),
% 2.74/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f18])).
% 2.74/1.02  
% 2.74/1.02  fof(f32,plain,(
% 2.74/1.02    r1_tarski(sK1,sK2)),
% 2.74/1.02    inference(cnf_transformation,[],[f19])).
% 2.74/1.02  
% 2.74/1.02  fof(f2,axiom,(
% 2.74/1.02    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.02  
% 2.74/1.02  fof(f15,plain,(
% 2.74/1.02    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.74/1.02    inference(nnf_transformation,[],[f2])).
% 2.74/1.02  
% 2.74/1.02  fof(f16,plain,(
% 2.74/1.02    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 2.74/1.02    inference(flattening,[],[f15])).
% 2.74/1.02  
% 2.74/1.02  fof(f21,plain,(
% 2.74/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 2.74/1.02    inference(cnf_transformation,[],[f16])).
% 2.74/1.02  
% 2.74/1.02  fof(f31,plain,(
% 2.74/1.02    r2_xboole_0(sK0,sK1)),
% 2.74/1.02    inference(cnf_transformation,[],[f19])).
% 2.74/1.02  
% 2.74/1.02  fof(f4,axiom,(
% 2.74/1.02    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.02  
% 2.74/1.02  fof(f17,plain,(
% 2.74/1.02    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.74/1.02    inference(nnf_transformation,[],[f4])).
% 2.74/1.02  
% 2.74/1.02  fof(f26,plain,(
% 2.74/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 2.74/1.02    inference(cnf_transformation,[],[f17])).
% 2.74/1.02  
% 2.74/1.02  fof(f6,axiom,(
% 2.74/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.02  
% 2.74/1.02  fof(f28,plain,(
% 2.74/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.74/1.02    inference(cnf_transformation,[],[f6])).
% 2.74/1.02  
% 2.74/1.02  fof(f1,axiom,(
% 2.74/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.02  
% 2.74/1.02  fof(f20,plain,(
% 2.74/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.74/1.02    inference(cnf_transformation,[],[f1])).
% 2.74/1.02  
% 2.74/1.02  fof(f8,axiom,(
% 2.74/1.02    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.02  
% 2.74/1.02  fof(f30,plain,(
% 2.74/1.02    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.74/1.02    inference(cnf_transformation,[],[f8])).
% 2.74/1.02  
% 2.74/1.02  fof(f7,axiom,(
% 2.74/1.02    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.02  
% 2.74/1.02  fof(f29,plain,(
% 2.74/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.74/1.02    inference(cnf_transformation,[],[f7])).
% 2.74/1.02  
% 2.74/1.02  fof(f34,plain,(
% 2.74/1.02    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 2.74/1.02    inference(definition_unfolding,[],[f30,f29])).
% 2.74/1.02  
% 2.74/1.02  fof(f5,axiom,(
% 2.74/1.02    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.74/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.74/1.02  
% 2.74/1.02  fof(f12,plain,(
% 2.74/1.02    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.74/1.02    inference(ennf_transformation,[],[f5])).
% 2.74/1.02  
% 2.74/1.02  fof(f27,plain,(
% 2.74/1.02    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 2.74/1.02    inference(cnf_transformation,[],[f12])).
% 2.74/1.02  
% 2.74/1.02  fof(f23,plain,(
% 2.74/1.02    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.74/1.02    inference(cnf_transformation,[],[f16])).
% 2.74/1.02  
% 2.74/1.02  fof(f33,plain,(
% 2.74/1.02    ~r2_xboole_0(sK0,sK2)),
% 2.74/1.02    inference(cnf_transformation,[],[f19])).
% 2.74/1.02  
% 2.74/1.02  cnf(c_11,negated_conjecture,
% 2.74/1.02      ( r1_tarski(sK1,sK2) ),
% 2.74/1.02      inference(cnf_transformation,[],[f32]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_419,plain,
% 2.74/1.02      ( r1_tarski(sK1,sK2) = iProver_top ),
% 2.74/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_3,plain,
% 2.74/1.02      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 2.74/1.02      inference(cnf_transformation,[],[f21]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_12,negated_conjecture,
% 2.74/1.02      ( r2_xboole_0(sK0,sK1) ),
% 2.74/1.02      inference(cnf_transformation,[],[f31]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_147,plain,
% 2.74/1.02      ( r1_tarski(X0,X1) | sK1 != X1 | sK0 != X0 ),
% 2.74/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_12]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_148,plain,
% 2.74/1.02      ( r1_tarski(sK0,sK1) ),
% 2.74/1.02      inference(unflattening,[status(thm)],[c_147]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_417,plain,
% 2.74/1.02      ( r1_tarski(sK0,sK1) = iProver_top ),
% 2.74/1.02      inference(predicate_to_equality,[status(thm)],[c_148]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_5,plain,
% 2.74/1.02      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 2.74/1.02      inference(cnf_transformation,[],[f26]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_422,plain,
% 2.74/1.02      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 2.74/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_1021,plain,
% 2.74/1.02      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 2.74/1.02      inference(superposition,[status(thm)],[c_417,c_422]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_8,plain,
% 2.74/1.02      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 2.74/1.02      inference(cnf_transformation,[],[f28]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_1143,plain,
% 2.74/1.02      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
% 2.74/1.02      inference(superposition,[status(thm)],[c_1021,c_8]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_1020,plain,
% 2.74/1.02      ( k4_xboole_0(sK1,sK2) = k1_xboole_0 ),
% 2.74/1.02      inference(superposition,[status(thm)],[c_419,c_422]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_0,plain,
% 2.74/1.02      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 2.74/1.02      inference(cnf_transformation,[],[f20]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_9,plain,
% 2.74/1.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 2.74/1.02      inference(cnf_transformation,[],[f34]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_621,plain,
% 2.74/1.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 2.74/1.02      inference(superposition,[status(thm)],[c_0,c_9]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_729,plain,
% 2.74/1.02      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 2.74/1.02      inference(superposition,[status(thm)],[c_621,c_8]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_810,plain,
% 2.74/1.02      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 2.74/1.02      inference(superposition,[status(thm)],[c_0,c_729]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_1028,plain,
% 2.74/1.02      ( k2_xboole_0(sK1,k1_xboole_0) = sK1 ),
% 2.74/1.02      inference(superposition,[status(thm)],[c_1020,c_810]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_1558,plain,
% 2.74/1.02      ( k2_xboole_0(sK1,sK0) = sK1 ),
% 2.74/1.02      inference(light_normalisation,[status(thm)],[c_1143,c_1028]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_7,plain,
% 2.74/1.02      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 2.74/1.02      inference(cnf_transformation,[],[f27]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_420,plain,
% 2.74/1.02      ( r1_tarski(X0,X1) = iProver_top
% 2.74/1.02      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 2.74/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_710,plain,
% 2.74/1.02      ( r1_tarski(X0,X1) = iProver_top
% 2.74/1.02      | r1_tarski(k2_xboole_0(X2,X0),X1) != iProver_top ),
% 2.74/1.02      inference(superposition,[status(thm)],[c_0,c_420]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_1565,plain,
% 2.74/1.02      ( r1_tarski(sK1,X0) != iProver_top | r1_tarski(sK0,X0) = iProver_top ),
% 2.74/1.02      inference(superposition,[status(thm)],[c_1558,c_710]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_3479,plain,
% 2.74/1.02      ( r1_tarski(sK0,sK2) = iProver_top ),
% 2.74/1.02      inference(superposition,[status(thm)],[c_419,c_1565]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_1,plain,
% 2.74/1.02      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 2.74/1.02      inference(cnf_transformation,[],[f23]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_10,negated_conjecture,
% 2.74/1.02      ( ~ r2_xboole_0(sK0,sK2) ),
% 2.74/1.02      inference(cnf_transformation,[],[f33]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_137,plain,
% 2.74/1.02      ( ~ r1_tarski(X0,X1) | X1 = X0 | sK2 != X1 | sK0 != X0 ),
% 2.74/1.02      inference(resolution_lifted,[status(thm)],[c_1,c_10]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_138,plain,
% 2.74/1.02      ( ~ r1_tarski(sK0,sK2) | sK2 = sK0 ),
% 2.74/1.02      inference(unflattening,[status(thm)],[c_137]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_418,plain,
% 2.74/1.02      ( sK2 = sK0 | r1_tarski(sK0,sK2) != iProver_top ),
% 2.74/1.02      inference(predicate_to_equality,[status(thm)],[c_138]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_3588,plain,
% 2.74/1.02      ( sK2 = sK0 ),
% 2.74/1.02      inference(superposition,[status(thm)],[c_3479,c_418]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_1034,plain,
% 2.74/1.02      ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) ),
% 2.74/1.02      inference(superposition,[status(thm)],[c_1020,c_8]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_3605,plain,
% 2.74/1.02      ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k1_xboole_0) ),
% 2.74/1.02      inference(demodulation,[status(thm)],[c_3588,c_1034]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_1137,plain,
% 2.74/1.02      ( k2_xboole_0(sK0,k1_xboole_0) = sK0 ),
% 2.74/1.02      inference(superposition,[status(thm)],[c_1021,c_810]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_1560,plain,
% 2.74/1.02      ( k2_xboole_0(sK0,sK1) = sK1 ),
% 2.74/1.02      inference(superposition,[status(thm)],[c_0,c_1558]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_3616,plain,
% 2.74/1.02      ( sK1 = sK0 ),
% 2.74/1.02      inference(light_normalisation,[status(thm)],[c_3605,c_1137,c_1560]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_159,plain,
% 2.74/1.02      ( sK1 != sK2 | sK0 != sK0 ),
% 2.74/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_12]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_180,plain,
% 2.74/1.02      ( sK1 != sK2 ),
% 2.74/1.02      inference(equality_resolution_simp,[status(thm)],[c_159]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_3607,plain,
% 2.74/1.02      ( sK1 != sK0 ),
% 2.74/1.02      inference(demodulation,[status(thm)],[c_3588,c_180]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_3618,plain,
% 2.74/1.02      ( sK0 != sK0 ),
% 2.74/1.02      inference(demodulation,[status(thm)],[c_3616,c_3607]) ).
% 2.74/1.02  
% 2.74/1.02  cnf(c_3621,plain,
% 2.74/1.02      ( $false ),
% 2.74/1.02      inference(equality_resolution_simp,[status(thm)],[c_3618]) ).
% 2.74/1.02  
% 2.74/1.02  
% 2.74/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.74/1.02  
% 2.74/1.02  ------                               Statistics
% 2.74/1.02  
% 2.74/1.02  ------ General
% 2.74/1.02  
% 2.74/1.02  abstr_ref_over_cycles:                  0
% 2.74/1.02  abstr_ref_under_cycles:                 0
% 2.74/1.02  gc_basic_clause_elim:                   0
% 2.74/1.02  forced_gc_time:                         0
% 2.74/1.02  parsing_time:                           0.015
% 2.74/1.02  unif_index_cands_time:                  0.
% 2.74/1.02  unif_index_add_time:                    0.
% 2.74/1.02  orderings_time:                         0.
% 2.74/1.02  out_proof_time:                         0.005
% 2.74/1.02  total_time:                             0.137
% 2.74/1.02  num_of_symbols:                         39
% 2.74/1.02  num_of_terms:                           3009
% 2.74/1.02  
% 2.74/1.02  ------ Preprocessing
% 2.74/1.02  
% 2.74/1.02  num_of_splits:                          0
% 2.74/1.02  num_of_split_atoms:                     0
% 2.74/1.02  num_of_reused_defs:                     0
% 2.74/1.02  num_eq_ax_congr_red:                    3
% 2.74/1.02  num_of_sem_filtered_clauses:            1
% 2.74/1.02  num_of_subtypes:                        0
% 2.74/1.02  monotx_restored_types:                  0
% 2.74/1.02  sat_num_of_epr_types:                   0
% 2.74/1.02  sat_num_of_non_cyclic_types:            0
% 2.74/1.02  sat_guarded_non_collapsed_types:        0
% 2.74/1.02  num_pure_diseq_elim:                    0
% 2.74/1.02  simp_replaced_by:                       0
% 2.74/1.02  res_preprocessed:                       56
% 2.74/1.02  prep_upred:                             0
% 2.74/1.02  prep_unflattend:                        7
% 2.74/1.02  smt_new_axioms:                         0
% 2.74/1.02  pred_elim_cands:                        1
% 2.74/1.02  pred_elim:                              1
% 2.74/1.02  pred_elim_cl:                           1
% 2.74/1.02  pred_elim_cycles:                       3
% 2.74/1.02  merged_defs:                            8
% 2.74/1.02  merged_defs_ncl:                        0
% 2.74/1.02  bin_hyper_res:                          8
% 2.74/1.02  prep_cycles:                            4
% 2.74/1.02  pred_elim_time:                         0.
% 2.74/1.02  splitting_time:                         0.
% 2.74/1.02  sem_filter_time:                        0.
% 2.74/1.02  monotx_time:                            0.
% 2.74/1.02  subtype_inf_time:                       0.
% 2.74/1.02  
% 2.74/1.02  ------ Problem properties
% 2.74/1.02  
% 2.74/1.02  clauses:                                11
% 2.74/1.02  conjectures:                            1
% 2.74/1.02  epr:                                    5
% 2.74/1.02  horn:                                   11
% 2.74/1.02  ground:                                 5
% 2.74/1.02  unary:                                  7
% 2.74/1.02  binary:                                 4
% 2.74/1.02  lits:                                   15
% 2.74/1.02  lits_eq:                                8
% 2.74/1.02  fd_pure:                                0
% 2.74/1.02  fd_pseudo:                              0
% 2.74/1.02  fd_cond:                                0
% 2.74/1.02  fd_pseudo_cond:                         0
% 2.74/1.02  ac_symbols:                             0
% 2.74/1.02  
% 2.74/1.02  ------ Propositional Solver
% 2.74/1.02  
% 2.74/1.02  prop_solver_calls:                      27
% 2.74/1.02  prop_fast_solver_calls:                 266
% 2.74/1.02  smt_solver_calls:                       0
% 2.74/1.02  smt_fast_solver_calls:                  0
% 2.74/1.02  prop_num_of_clauses:                    1385
% 2.74/1.02  prop_preprocess_simplified:             3114
% 2.74/1.02  prop_fo_subsumed:                       0
% 2.74/1.02  prop_solver_time:                       0.
% 2.74/1.02  smt_solver_time:                        0.
% 2.74/1.02  smt_fast_solver_time:                   0.
% 2.74/1.02  prop_fast_solver_time:                  0.
% 2.74/1.02  prop_unsat_core_time:                   0.
% 2.74/1.02  
% 2.74/1.02  ------ QBF
% 2.74/1.02  
% 2.74/1.02  qbf_q_res:                              0
% 2.74/1.02  qbf_num_tautologies:                    0
% 2.74/1.02  qbf_prep_cycles:                        0
% 2.74/1.02  
% 2.74/1.02  ------ BMC1
% 2.74/1.02  
% 2.74/1.02  bmc1_current_bound:                     -1
% 2.74/1.02  bmc1_last_solved_bound:                 -1
% 2.74/1.02  bmc1_unsat_core_size:                   -1
% 2.74/1.02  bmc1_unsat_core_parents_size:           -1
% 2.74/1.02  bmc1_merge_next_fun:                    0
% 2.74/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.74/1.02  
% 2.74/1.02  ------ Instantiation
% 2.74/1.02  
% 2.74/1.02  inst_num_of_clauses:                    544
% 2.74/1.02  inst_num_in_passive:                    52
% 2.74/1.02  inst_num_in_active:                     260
% 2.74/1.02  inst_num_in_unprocessed:                233
% 2.74/1.02  inst_num_of_loops:                      270
% 2.74/1.02  inst_num_of_learning_restarts:          0
% 2.74/1.02  inst_num_moves_active_passive:          4
% 2.74/1.02  inst_lit_activity:                      0
% 2.74/1.02  inst_lit_activity_moves:                0
% 2.74/1.02  inst_num_tautologies:                   0
% 2.74/1.02  inst_num_prop_implied:                  0
% 2.74/1.02  inst_num_existing_simplified:           0
% 2.74/1.02  inst_num_eq_res_simplified:             0
% 2.74/1.02  inst_num_child_elim:                    0
% 2.74/1.02  inst_num_of_dismatching_blockings:      166
% 2.74/1.02  inst_num_of_non_proper_insts:           535
% 2.74/1.02  inst_num_of_duplicates:                 0
% 2.74/1.02  inst_inst_num_from_inst_to_res:         0
% 2.74/1.02  inst_dismatching_checking_time:         0.
% 2.74/1.02  
% 2.74/1.02  ------ Resolution
% 2.74/1.02  
% 2.74/1.02  res_num_of_clauses:                     0
% 2.74/1.02  res_num_in_passive:                     0
% 2.74/1.02  res_num_in_active:                      0
% 2.74/1.02  res_num_of_loops:                       60
% 2.74/1.02  res_forward_subset_subsumed:            43
% 2.74/1.02  res_backward_subset_subsumed:           6
% 2.74/1.02  res_forward_subsumed:                   0
% 2.74/1.02  res_backward_subsumed:                  0
% 2.74/1.02  res_forward_subsumption_resolution:     0
% 2.74/1.02  res_backward_subsumption_resolution:    0
% 2.74/1.02  res_clause_to_clause_subsumption:       283
% 2.74/1.02  res_orphan_elimination:                 0
% 2.74/1.02  res_tautology_del:                      119
% 2.74/1.02  res_num_eq_res_simplified:              1
% 2.74/1.02  res_num_sel_changes:                    0
% 2.74/1.02  res_moves_from_active_to_pass:          0
% 2.74/1.02  
% 2.74/1.02  ------ Superposition
% 2.74/1.02  
% 2.74/1.02  sup_time_total:                         0.
% 2.74/1.02  sup_time_generating:                    0.
% 2.74/1.02  sup_time_sim_full:                      0.
% 2.74/1.02  sup_time_sim_immed:                     0.
% 2.74/1.02  
% 2.74/1.02  sup_num_of_clauses:                     61
% 2.74/1.02  sup_num_in_active:                      40
% 2.74/1.02  sup_num_in_passive:                     21
% 2.74/1.02  sup_num_of_loops:                       53
% 2.74/1.02  sup_fw_superposition:                   103
% 2.74/1.02  sup_bw_superposition:                   87
% 2.74/1.02  sup_immediate_simplified:               16
% 2.74/1.02  sup_given_eliminated:                   1
% 2.74/1.02  comparisons_done:                       0
% 2.74/1.02  comparisons_avoided:                    0
% 2.74/1.02  
% 2.74/1.02  ------ Simplifications
% 2.74/1.02  
% 2.74/1.02  
% 2.74/1.02  sim_fw_subset_subsumed:                 0
% 2.74/1.02  sim_bw_subset_subsumed:                 1
% 2.74/1.02  sim_fw_subsumed:                        10
% 2.74/1.02  sim_bw_subsumed:                        0
% 2.74/1.02  sim_fw_subsumption_res:                 0
% 2.74/1.02  sim_bw_subsumption_res:                 0
% 2.74/1.02  sim_tautology_del:                      9
% 2.74/1.02  sim_eq_tautology_del:                   0
% 2.74/1.02  sim_eq_res_simp:                        0
% 2.74/1.02  sim_fw_demodulated:                     0
% 2.74/1.02  sim_bw_demodulated:                     15
% 2.74/1.02  sim_light_normalised:                   12
% 2.74/1.02  sim_joinable_taut:                      0
% 2.74/1.02  sim_joinable_simp:                      0
% 2.74/1.02  sim_ac_normalised:                      0
% 2.74/1.02  sim_smt_subsumption:                    0
% 2.74/1.02  
%------------------------------------------------------------------------------
