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
% DateTime   : Thu Dec  3 11:42:54 EST 2020

% Result     : Theorem 7.19s
% Output     : CNFRefutation 7.19s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 146 expanded)
%              Number of clauses        :   29 (  50 expanded)
%              Number of leaves         :   10 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  100 ( 348 expanded)
%              Number of equality atoms :   40 (  76 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(X0,sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15,f14])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k6_subset_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f19,f21])).

fof(f26,plain,(
    ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0)) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_8,negated_conjecture,
    ( v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_227,plain,
    ( v1_relat_1(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k6_subset_1(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_231,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k6_subset_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_228,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_230,plain,
    ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_576,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(X0)) = k1_relat_1(k2_xboole_0(sK1,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_228,c_230])).

cnf(c_1355,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(X0,X1))) = k1_relat_1(k2_xboole_0(sK1,k6_subset_1(X0,X1)))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_231,c_576])).

cnf(c_5506,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X0))) = k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_227,c_1355])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k6_subset_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_233,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6365,plain,
    ( r1_tarski(X0,k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X1)))) != iProver_top
    | r1_tarski(k6_subset_1(X0,k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5506,c_233])).

cnf(c_6,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_229,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_31989,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6365,c_229])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_817,plain,
    ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_227,c_576])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_961,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_817,c_0])).

cnf(c_577,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(X0)) = k1_relat_1(k2_xboole_0(sK0,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_227,c_230])).

cnf(c_1078,plain,
    ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_228,c_577])).

cnf(c_1443,plain,
    ( k1_relat_1(k2_xboole_0(sK0,sK1)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
    inference(light_normalisation,[status(thm)],[c_961,c_1078])).

cnf(c_31990,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_31989,c_1,c_1443])).

cnf(c_3,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_232,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1088,plain,
    ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_232])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31990,c_1088])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:03:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.19/1.42  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.19/1.42  
% 7.19/1.42  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.19/1.42  
% 7.19/1.42  ------  iProver source info
% 7.19/1.42  
% 7.19/1.42  git: date: 2020-06-30 10:37:57 +0100
% 7.19/1.42  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.19/1.42  git: non_committed_changes: false
% 7.19/1.42  git: last_make_outside_of_git: false
% 7.19/1.42  
% 7.19/1.42  ------ 
% 7.19/1.42  
% 7.19/1.42  ------ Input Options
% 7.19/1.42  
% 7.19/1.42  --out_options                           all
% 7.19/1.42  --tptp_safe_out                         true
% 7.19/1.42  --problem_path                          ""
% 7.19/1.42  --include_path                          ""
% 7.19/1.42  --clausifier                            res/vclausify_rel
% 7.19/1.42  --clausifier_options                    --mode clausify
% 7.19/1.42  --stdin                                 false
% 7.19/1.42  --stats_out                             all
% 7.19/1.42  
% 7.19/1.42  ------ General Options
% 7.19/1.42  
% 7.19/1.42  --fof                                   false
% 7.19/1.42  --time_out_real                         305.
% 7.19/1.42  --time_out_virtual                      -1.
% 7.19/1.42  --symbol_type_check                     false
% 7.19/1.42  --clausify_out                          false
% 7.19/1.42  --sig_cnt_out                           false
% 7.19/1.42  --trig_cnt_out                          false
% 7.19/1.42  --trig_cnt_out_tolerance                1.
% 7.19/1.42  --trig_cnt_out_sk_spl                   false
% 7.19/1.42  --abstr_cl_out                          false
% 7.19/1.42  
% 7.19/1.42  ------ Global Options
% 7.19/1.42  
% 7.19/1.42  --schedule                              default
% 7.19/1.42  --add_important_lit                     false
% 7.19/1.42  --prop_solver_per_cl                    1000
% 7.19/1.42  --min_unsat_core                        false
% 7.19/1.42  --soft_assumptions                      false
% 7.19/1.42  --soft_lemma_size                       3
% 7.19/1.42  --prop_impl_unit_size                   0
% 7.19/1.42  --prop_impl_unit                        []
% 7.19/1.42  --share_sel_clauses                     true
% 7.19/1.42  --reset_solvers                         false
% 7.19/1.42  --bc_imp_inh                            [conj_cone]
% 7.19/1.42  --conj_cone_tolerance                   3.
% 7.19/1.42  --extra_neg_conj                        none
% 7.19/1.42  --large_theory_mode                     true
% 7.19/1.42  --prolific_symb_bound                   200
% 7.19/1.42  --lt_threshold                          2000
% 7.19/1.42  --clause_weak_htbl                      true
% 7.19/1.42  --gc_record_bc_elim                     false
% 7.19/1.42  
% 7.19/1.42  ------ Preprocessing Options
% 7.19/1.42  
% 7.19/1.42  --preprocessing_flag                    true
% 7.19/1.42  --time_out_prep_mult                    0.1
% 7.19/1.42  --splitting_mode                        input
% 7.19/1.42  --splitting_grd                         true
% 7.19/1.42  --splitting_cvd                         false
% 7.19/1.42  --splitting_cvd_svl                     false
% 7.19/1.42  --splitting_nvd                         32
% 7.19/1.42  --sub_typing                            true
% 7.19/1.42  --prep_gs_sim                           true
% 7.19/1.42  --prep_unflatten                        true
% 7.19/1.42  --prep_res_sim                          true
% 7.19/1.42  --prep_upred                            true
% 7.19/1.42  --prep_sem_filter                       exhaustive
% 7.19/1.42  --prep_sem_filter_out                   false
% 7.19/1.42  --pred_elim                             true
% 7.19/1.42  --res_sim_input                         true
% 7.19/1.42  --eq_ax_congr_red                       true
% 7.19/1.42  --pure_diseq_elim                       true
% 7.19/1.42  --brand_transform                       false
% 7.19/1.42  --non_eq_to_eq                          false
% 7.19/1.42  --prep_def_merge                        true
% 7.19/1.42  --prep_def_merge_prop_impl              false
% 7.19/1.42  --prep_def_merge_mbd                    true
% 7.19/1.42  --prep_def_merge_tr_red                 false
% 7.19/1.42  --prep_def_merge_tr_cl                  false
% 7.19/1.42  --smt_preprocessing                     true
% 7.19/1.42  --smt_ac_axioms                         fast
% 7.19/1.42  --preprocessed_out                      false
% 7.19/1.42  --preprocessed_stats                    false
% 7.19/1.42  
% 7.19/1.42  ------ Abstraction refinement Options
% 7.19/1.42  
% 7.19/1.42  --abstr_ref                             []
% 7.19/1.42  --abstr_ref_prep                        false
% 7.19/1.42  --abstr_ref_until_sat                   false
% 7.19/1.42  --abstr_ref_sig_restrict                funpre
% 7.19/1.42  --abstr_ref_af_restrict_to_split_sk     false
% 7.19/1.42  --abstr_ref_under                       []
% 7.19/1.42  
% 7.19/1.42  ------ SAT Options
% 7.19/1.42  
% 7.19/1.42  --sat_mode                              false
% 7.19/1.42  --sat_fm_restart_options                ""
% 7.19/1.42  --sat_gr_def                            false
% 7.19/1.42  --sat_epr_types                         true
% 7.19/1.42  --sat_non_cyclic_types                  false
% 7.19/1.42  --sat_finite_models                     false
% 7.19/1.42  --sat_fm_lemmas                         false
% 7.19/1.42  --sat_fm_prep                           false
% 7.19/1.42  --sat_fm_uc_incr                        true
% 7.19/1.42  --sat_out_model                         small
% 7.19/1.42  --sat_out_clauses                       false
% 7.19/1.42  
% 7.19/1.42  ------ QBF Options
% 7.19/1.42  
% 7.19/1.42  --qbf_mode                              false
% 7.19/1.42  --qbf_elim_univ                         false
% 7.19/1.42  --qbf_dom_inst                          none
% 7.19/1.42  --qbf_dom_pre_inst                      false
% 7.19/1.42  --qbf_sk_in                             false
% 7.19/1.42  --qbf_pred_elim                         true
% 7.19/1.42  --qbf_split                             512
% 7.19/1.42  
% 7.19/1.42  ------ BMC1 Options
% 7.19/1.42  
% 7.19/1.42  --bmc1_incremental                      false
% 7.19/1.42  --bmc1_axioms                           reachable_all
% 7.19/1.42  --bmc1_min_bound                        0
% 7.19/1.42  --bmc1_max_bound                        -1
% 7.19/1.42  --bmc1_max_bound_default                -1
% 7.19/1.42  --bmc1_symbol_reachability              true
% 7.19/1.42  --bmc1_property_lemmas                  false
% 7.19/1.42  --bmc1_k_induction                      false
% 7.19/1.42  --bmc1_non_equiv_states                 false
% 7.19/1.42  --bmc1_deadlock                         false
% 7.19/1.42  --bmc1_ucm                              false
% 7.19/1.42  --bmc1_add_unsat_core                   none
% 7.19/1.42  --bmc1_unsat_core_children              false
% 7.19/1.42  --bmc1_unsat_core_extrapolate_axioms    false
% 7.19/1.42  --bmc1_out_stat                         full
% 7.19/1.42  --bmc1_ground_init                      false
% 7.19/1.42  --bmc1_pre_inst_next_state              false
% 7.19/1.42  --bmc1_pre_inst_state                   false
% 7.19/1.42  --bmc1_pre_inst_reach_state             false
% 7.19/1.42  --bmc1_out_unsat_core                   false
% 7.19/1.42  --bmc1_aig_witness_out                  false
% 7.19/1.42  --bmc1_verbose                          false
% 7.19/1.42  --bmc1_dump_clauses_tptp                false
% 7.19/1.42  --bmc1_dump_unsat_core_tptp             false
% 7.19/1.42  --bmc1_dump_file                        -
% 7.19/1.42  --bmc1_ucm_expand_uc_limit              128
% 7.19/1.42  --bmc1_ucm_n_expand_iterations          6
% 7.19/1.42  --bmc1_ucm_extend_mode                  1
% 7.19/1.42  --bmc1_ucm_init_mode                    2
% 7.19/1.42  --bmc1_ucm_cone_mode                    none
% 7.19/1.42  --bmc1_ucm_reduced_relation_type        0
% 7.19/1.42  --bmc1_ucm_relax_model                  4
% 7.19/1.42  --bmc1_ucm_full_tr_after_sat            true
% 7.19/1.42  --bmc1_ucm_expand_neg_assumptions       false
% 7.19/1.42  --bmc1_ucm_layered_model                none
% 7.19/1.42  --bmc1_ucm_max_lemma_size               10
% 7.19/1.42  
% 7.19/1.42  ------ AIG Options
% 7.19/1.42  
% 7.19/1.42  --aig_mode                              false
% 7.19/1.42  
% 7.19/1.42  ------ Instantiation Options
% 7.19/1.42  
% 7.19/1.42  --instantiation_flag                    true
% 7.19/1.42  --inst_sos_flag                         false
% 7.19/1.42  --inst_sos_phase                        true
% 7.19/1.42  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.19/1.42  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.19/1.42  --inst_lit_sel_side                     num_symb
% 7.19/1.42  --inst_solver_per_active                1400
% 7.19/1.42  --inst_solver_calls_frac                1.
% 7.19/1.42  --inst_passive_queue_type               priority_queues
% 7.19/1.42  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.19/1.42  --inst_passive_queues_freq              [25;2]
% 7.19/1.42  --inst_dismatching                      true
% 7.19/1.42  --inst_eager_unprocessed_to_passive     true
% 7.19/1.42  --inst_prop_sim_given                   true
% 7.19/1.42  --inst_prop_sim_new                     false
% 7.19/1.42  --inst_subs_new                         false
% 7.19/1.42  --inst_eq_res_simp                      false
% 7.19/1.42  --inst_subs_given                       false
% 7.19/1.42  --inst_orphan_elimination               true
% 7.19/1.42  --inst_learning_loop_flag               true
% 7.19/1.42  --inst_learning_start                   3000
% 7.19/1.42  --inst_learning_factor                  2
% 7.19/1.42  --inst_start_prop_sim_after_learn       3
% 7.19/1.42  --inst_sel_renew                        solver
% 7.19/1.42  --inst_lit_activity_flag                true
% 7.19/1.42  --inst_restr_to_given                   false
% 7.19/1.42  --inst_activity_threshold               500
% 7.19/1.42  --inst_out_proof                        true
% 7.19/1.42  
% 7.19/1.42  ------ Resolution Options
% 7.19/1.42  
% 7.19/1.42  --resolution_flag                       true
% 7.19/1.42  --res_lit_sel                           adaptive
% 7.19/1.42  --res_lit_sel_side                      none
% 7.19/1.42  --res_ordering                          kbo
% 7.19/1.42  --res_to_prop_solver                    active
% 7.19/1.42  --res_prop_simpl_new                    false
% 7.19/1.42  --res_prop_simpl_given                  true
% 7.19/1.42  --res_passive_queue_type                priority_queues
% 7.19/1.42  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.19/1.42  --res_passive_queues_freq               [15;5]
% 7.19/1.42  --res_forward_subs                      full
% 7.19/1.42  --res_backward_subs                     full
% 7.19/1.42  --res_forward_subs_resolution           true
% 7.19/1.42  --res_backward_subs_resolution          true
% 7.19/1.42  --res_orphan_elimination                true
% 7.19/1.42  --res_time_limit                        2.
% 7.19/1.42  --res_out_proof                         true
% 7.19/1.42  
% 7.19/1.42  ------ Superposition Options
% 7.19/1.42  
% 7.19/1.42  --superposition_flag                    true
% 7.19/1.42  --sup_passive_queue_type                priority_queues
% 7.19/1.42  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.19/1.42  --sup_passive_queues_freq               [8;1;4]
% 7.19/1.42  --demod_completeness_check              fast
% 7.19/1.42  --demod_use_ground                      true
% 7.19/1.42  --sup_to_prop_solver                    passive
% 7.19/1.42  --sup_prop_simpl_new                    true
% 7.19/1.42  --sup_prop_simpl_given                  true
% 7.19/1.42  --sup_fun_splitting                     false
% 7.19/1.42  --sup_smt_interval                      50000
% 7.19/1.42  
% 7.19/1.42  ------ Superposition Simplification Setup
% 7.19/1.42  
% 7.19/1.42  --sup_indices_passive                   []
% 7.19/1.42  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.19/1.42  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.19/1.42  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.19/1.42  --sup_full_triv                         [TrivRules;PropSubs]
% 7.19/1.42  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.19/1.42  --sup_full_bw                           [BwDemod]
% 7.19/1.42  --sup_immed_triv                        [TrivRules]
% 7.19/1.42  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.19/1.42  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.19/1.42  --sup_immed_bw_main                     []
% 7.19/1.42  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.19/1.42  --sup_input_triv                        [Unflattening;TrivRules]
% 7.19/1.42  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.19/1.42  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.19/1.42  
% 7.19/1.42  ------ Combination Options
% 7.19/1.42  
% 7.19/1.42  --comb_res_mult                         3
% 7.19/1.42  --comb_sup_mult                         2
% 7.19/1.42  --comb_inst_mult                        10
% 7.19/1.42  
% 7.19/1.42  ------ Debug Options
% 7.19/1.42  
% 7.19/1.42  --dbg_backtrace                         false
% 7.19/1.42  --dbg_dump_prop_clauses                 false
% 7.19/1.42  --dbg_dump_prop_clauses_file            -
% 7.19/1.42  --dbg_out_stat                          false
% 7.19/1.42  ------ Parsing...
% 7.19/1.42  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.19/1.42  
% 7.19/1.42  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.19/1.42  
% 7.19/1.42  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.19/1.42  
% 7.19/1.42  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.19/1.42  ------ Proving...
% 7.19/1.42  ------ Problem Properties 
% 7.19/1.42  
% 7.19/1.42  
% 7.19/1.42  clauses                                 9
% 7.19/1.42  conjectures                             3
% 7.19/1.42  EPR                                     2
% 7.19/1.42  Horn                                    9
% 7.19/1.42  unary                                   6
% 7.19/1.42  binary                                  2
% 7.19/1.42  lits                                    13
% 7.19/1.42  lits eq                                 3
% 7.19/1.42  fd_pure                                 0
% 7.19/1.42  fd_pseudo                               0
% 7.19/1.42  fd_cond                                 0
% 7.19/1.42  fd_pseudo_cond                          0
% 7.19/1.42  AC symbols                              0
% 7.19/1.42  
% 7.19/1.42  ------ Schedule dynamic 5 is on 
% 7.19/1.42  
% 7.19/1.42  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.19/1.42  
% 7.19/1.42  
% 7.19/1.42  ------ 
% 7.19/1.42  Current options:
% 7.19/1.42  ------ 
% 7.19/1.42  
% 7.19/1.42  ------ Input Options
% 7.19/1.42  
% 7.19/1.42  --out_options                           all
% 7.19/1.42  --tptp_safe_out                         true
% 7.19/1.42  --problem_path                          ""
% 7.19/1.42  --include_path                          ""
% 7.19/1.42  --clausifier                            res/vclausify_rel
% 7.19/1.42  --clausifier_options                    --mode clausify
% 7.19/1.42  --stdin                                 false
% 7.19/1.42  --stats_out                             all
% 7.19/1.42  
% 7.19/1.42  ------ General Options
% 7.19/1.42  
% 7.19/1.42  --fof                                   false
% 7.19/1.42  --time_out_real                         305.
% 7.19/1.42  --time_out_virtual                      -1.
% 7.19/1.42  --symbol_type_check                     false
% 7.19/1.42  --clausify_out                          false
% 7.19/1.42  --sig_cnt_out                           false
% 7.19/1.42  --trig_cnt_out                          false
% 7.19/1.42  --trig_cnt_out_tolerance                1.
% 7.19/1.42  --trig_cnt_out_sk_spl                   false
% 7.19/1.42  --abstr_cl_out                          false
% 7.19/1.42  
% 7.19/1.42  ------ Global Options
% 7.19/1.42  
% 7.19/1.42  --schedule                              default
% 7.19/1.42  --add_important_lit                     false
% 7.19/1.42  --prop_solver_per_cl                    1000
% 7.19/1.42  --min_unsat_core                        false
% 7.19/1.42  --soft_assumptions                      false
% 7.19/1.42  --soft_lemma_size                       3
% 7.19/1.42  --prop_impl_unit_size                   0
% 7.19/1.42  --prop_impl_unit                        []
% 7.19/1.42  --share_sel_clauses                     true
% 7.19/1.42  --reset_solvers                         false
% 7.19/1.42  --bc_imp_inh                            [conj_cone]
% 7.19/1.42  --conj_cone_tolerance                   3.
% 7.19/1.42  --extra_neg_conj                        none
% 7.19/1.42  --large_theory_mode                     true
% 7.19/1.42  --prolific_symb_bound                   200
% 7.19/1.42  --lt_threshold                          2000
% 7.19/1.42  --clause_weak_htbl                      true
% 7.19/1.42  --gc_record_bc_elim                     false
% 7.19/1.42  
% 7.19/1.42  ------ Preprocessing Options
% 7.19/1.42  
% 7.19/1.42  --preprocessing_flag                    true
% 7.19/1.42  --time_out_prep_mult                    0.1
% 7.19/1.42  --splitting_mode                        input
% 7.19/1.42  --splitting_grd                         true
% 7.19/1.42  --splitting_cvd                         false
% 7.19/1.42  --splitting_cvd_svl                     false
% 7.19/1.42  --splitting_nvd                         32
% 7.19/1.42  --sub_typing                            true
% 7.19/1.42  --prep_gs_sim                           true
% 7.19/1.42  --prep_unflatten                        true
% 7.19/1.42  --prep_res_sim                          true
% 7.19/1.42  --prep_upred                            true
% 7.19/1.42  --prep_sem_filter                       exhaustive
% 7.19/1.42  --prep_sem_filter_out                   false
% 7.19/1.42  --pred_elim                             true
% 7.19/1.42  --res_sim_input                         true
% 7.19/1.42  --eq_ax_congr_red                       true
% 7.19/1.42  --pure_diseq_elim                       true
% 7.19/1.42  --brand_transform                       false
% 7.19/1.42  --non_eq_to_eq                          false
% 7.19/1.42  --prep_def_merge                        true
% 7.19/1.42  --prep_def_merge_prop_impl              false
% 7.19/1.42  --prep_def_merge_mbd                    true
% 7.19/1.42  --prep_def_merge_tr_red                 false
% 7.19/1.42  --prep_def_merge_tr_cl                  false
% 7.19/1.42  --smt_preprocessing                     true
% 7.19/1.42  --smt_ac_axioms                         fast
% 7.19/1.42  --preprocessed_out                      false
% 7.19/1.42  --preprocessed_stats                    false
% 7.19/1.42  
% 7.19/1.42  ------ Abstraction refinement Options
% 7.19/1.42  
% 7.19/1.42  --abstr_ref                             []
% 7.19/1.42  --abstr_ref_prep                        false
% 7.19/1.42  --abstr_ref_until_sat                   false
% 7.19/1.42  --abstr_ref_sig_restrict                funpre
% 7.19/1.42  --abstr_ref_af_restrict_to_split_sk     false
% 7.19/1.42  --abstr_ref_under                       []
% 7.19/1.42  
% 7.19/1.42  ------ SAT Options
% 7.19/1.42  
% 7.19/1.42  --sat_mode                              false
% 7.19/1.42  --sat_fm_restart_options                ""
% 7.19/1.42  --sat_gr_def                            false
% 7.19/1.42  --sat_epr_types                         true
% 7.19/1.42  --sat_non_cyclic_types                  false
% 7.19/1.42  --sat_finite_models                     false
% 7.19/1.42  --sat_fm_lemmas                         false
% 7.19/1.42  --sat_fm_prep                           false
% 7.19/1.42  --sat_fm_uc_incr                        true
% 7.19/1.42  --sat_out_model                         small
% 7.19/1.42  --sat_out_clauses                       false
% 7.19/1.42  
% 7.19/1.42  ------ QBF Options
% 7.19/1.42  
% 7.19/1.42  --qbf_mode                              false
% 7.19/1.42  --qbf_elim_univ                         false
% 7.19/1.42  --qbf_dom_inst                          none
% 7.19/1.42  --qbf_dom_pre_inst                      false
% 7.19/1.42  --qbf_sk_in                             false
% 7.19/1.42  --qbf_pred_elim                         true
% 7.19/1.42  --qbf_split                             512
% 7.19/1.42  
% 7.19/1.42  ------ BMC1 Options
% 7.19/1.42  
% 7.19/1.42  --bmc1_incremental                      false
% 7.19/1.42  --bmc1_axioms                           reachable_all
% 7.19/1.42  --bmc1_min_bound                        0
% 7.19/1.42  --bmc1_max_bound                        -1
% 7.19/1.42  --bmc1_max_bound_default                -1
% 7.19/1.42  --bmc1_symbol_reachability              true
% 7.19/1.42  --bmc1_property_lemmas                  false
% 7.19/1.42  --bmc1_k_induction                      false
% 7.19/1.42  --bmc1_non_equiv_states                 false
% 7.19/1.42  --bmc1_deadlock                         false
% 7.19/1.42  --bmc1_ucm                              false
% 7.19/1.42  --bmc1_add_unsat_core                   none
% 7.19/1.42  --bmc1_unsat_core_children              false
% 7.19/1.42  --bmc1_unsat_core_extrapolate_axioms    false
% 7.19/1.42  --bmc1_out_stat                         full
% 7.19/1.42  --bmc1_ground_init                      false
% 7.19/1.42  --bmc1_pre_inst_next_state              false
% 7.19/1.42  --bmc1_pre_inst_state                   false
% 7.19/1.42  --bmc1_pre_inst_reach_state             false
% 7.19/1.42  --bmc1_out_unsat_core                   false
% 7.19/1.42  --bmc1_aig_witness_out                  false
% 7.19/1.42  --bmc1_verbose                          false
% 7.19/1.42  --bmc1_dump_clauses_tptp                false
% 7.19/1.42  --bmc1_dump_unsat_core_tptp             false
% 7.19/1.42  --bmc1_dump_file                        -
% 7.19/1.42  --bmc1_ucm_expand_uc_limit              128
% 7.19/1.42  --bmc1_ucm_n_expand_iterations          6
% 7.19/1.42  --bmc1_ucm_extend_mode                  1
% 7.19/1.42  --bmc1_ucm_init_mode                    2
% 7.19/1.42  --bmc1_ucm_cone_mode                    none
% 7.19/1.42  --bmc1_ucm_reduced_relation_type        0
% 7.19/1.42  --bmc1_ucm_relax_model                  4
% 7.19/1.42  --bmc1_ucm_full_tr_after_sat            true
% 7.19/1.42  --bmc1_ucm_expand_neg_assumptions       false
% 7.19/1.42  --bmc1_ucm_layered_model                none
% 7.19/1.42  --bmc1_ucm_max_lemma_size               10
% 7.19/1.42  
% 7.19/1.42  ------ AIG Options
% 7.19/1.42  
% 7.19/1.42  --aig_mode                              false
% 7.19/1.42  
% 7.19/1.42  ------ Instantiation Options
% 7.19/1.42  
% 7.19/1.42  --instantiation_flag                    true
% 7.19/1.42  --inst_sos_flag                         false
% 7.19/1.42  --inst_sos_phase                        true
% 7.19/1.42  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.19/1.42  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.19/1.42  --inst_lit_sel_side                     none
% 7.19/1.42  --inst_solver_per_active                1400
% 7.19/1.42  --inst_solver_calls_frac                1.
% 7.19/1.42  --inst_passive_queue_type               priority_queues
% 7.19/1.42  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.19/1.42  --inst_passive_queues_freq              [25;2]
% 7.19/1.42  --inst_dismatching                      true
% 7.19/1.42  --inst_eager_unprocessed_to_passive     true
% 7.19/1.42  --inst_prop_sim_given                   true
% 7.19/1.42  --inst_prop_sim_new                     false
% 7.19/1.42  --inst_subs_new                         false
% 7.19/1.42  --inst_eq_res_simp                      false
% 7.19/1.42  --inst_subs_given                       false
% 7.19/1.42  --inst_orphan_elimination               true
% 7.19/1.42  --inst_learning_loop_flag               true
% 7.19/1.42  --inst_learning_start                   3000
% 7.19/1.42  --inst_learning_factor                  2
% 7.19/1.42  --inst_start_prop_sim_after_learn       3
% 7.19/1.42  --inst_sel_renew                        solver
% 7.19/1.42  --inst_lit_activity_flag                true
% 7.19/1.42  --inst_restr_to_given                   false
% 7.19/1.42  --inst_activity_threshold               500
% 7.19/1.42  --inst_out_proof                        true
% 7.19/1.42  
% 7.19/1.42  ------ Resolution Options
% 7.19/1.42  
% 7.19/1.42  --resolution_flag                       false
% 7.19/1.42  --res_lit_sel                           adaptive
% 7.19/1.42  --res_lit_sel_side                      none
% 7.19/1.42  --res_ordering                          kbo
% 7.19/1.42  --res_to_prop_solver                    active
% 7.19/1.42  --res_prop_simpl_new                    false
% 7.19/1.42  --res_prop_simpl_given                  true
% 7.19/1.42  --res_passive_queue_type                priority_queues
% 7.19/1.42  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.19/1.42  --res_passive_queues_freq               [15;5]
% 7.19/1.42  --res_forward_subs                      full
% 7.19/1.42  --res_backward_subs                     full
% 7.19/1.42  --res_forward_subs_resolution           true
% 7.19/1.42  --res_backward_subs_resolution          true
% 7.19/1.42  --res_orphan_elimination                true
% 7.19/1.42  --res_time_limit                        2.
% 7.19/1.42  --res_out_proof                         true
% 7.19/1.42  
% 7.19/1.42  ------ Superposition Options
% 7.19/1.42  
% 7.19/1.42  --superposition_flag                    true
% 7.19/1.42  --sup_passive_queue_type                priority_queues
% 7.19/1.42  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.19/1.42  --sup_passive_queues_freq               [8;1;4]
% 7.19/1.42  --demod_completeness_check              fast
% 7.19/1.42  --demod_use_ground                      true
% 7.19/1.42  --sup_to_prop_solver                    passive
% 7.19/1.42  --sup_prop_simpl_new                    true
% 7.19/1.42  --sup_prop_simpl_given                  true
% 7.19/1.42  --sup_fun_splitting                     false
% 7.19/1.42  --sup_smt_interval                      50000
% 7.19/1.42  
% 7.19/1.42  ------ Superposition Simplification Setup
% 7.19/1.42  
% 7.19/1.42  --sup_indices_passive                   []
% 7.19/1.42  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.19/1.42  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.19/1.42  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.19/1.42  --sup_full_triv                         [TrivRules;PropSubs]
% 7.19/1.42  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.19/1.42  --sup_full_bw                           [BwDemod]
% 7.19/1.42  --sup_immed_triv                        [TrivRules]
% 7.19/1.42  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.19/1.42  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.19/1.42  --sup_immed_bw_main                     []
% 7.19/1.42  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.19/1.42  --sup_input_triv                        [Unflattening;TrivRules]
% 7.19/1.42  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.19/1.42  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.19/1.42  
% 7.19/1.42  ------ Combination Options
% 7.19/1.42  
% 7.19/1.42  --comb_res_mult                         3
% 7.19/1.42  --comb_sup_mult                         2
% 7.19/1.42  --comb_inst_mult                        10
% 7.19/1.42  
% 7.19/1.42  ------ Debug Options
% 7.19/1.42  
% 7.19/1.42  --dbg_backtrace                         false
% 7.19/1.42  --dbg_dump_prop_clauses                 false
% 7.19/1.42  --dbg_dump_prop_clauses_file            -
% 7.19/1.42  --dbg_out_stat                          false
% 7.19/1.42  
% 7.19/1.42  
% 7.19/1.42  
% 7.19/1.42  
% 7.19/1.42  ------ Proving...
% 7.19/1.42  
% 7.19/1.42  
% 7.19/1.42  % SZS status Theorem for theBenchmark.p
% 7.19/1.42  
% 7.19/1.42  % SZS output start CNFRefutation for theBenchmark.p
% 7.19/1.42  
% 7.19/1.42  fof(f8,conjecture,(
% 7.19/1.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 7.19/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.19/1.42  
% 7.19/1.42  fof(f9,negated_conjecture,(
% 7.19/1.42    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))))),
% 7.19/1.42    inference(negated_conjecture,[],[f8])).
% 7.19/1.42  
% 7.19/1.42  fof(f13,plain,(
% 7.19/1.42    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 7.19/1.42    inference(ennf_transformation,[],[f9])).
% 7.19/1.42  
% 7.19/1.42  fof(f15,plain,(
% 7.19/1.42    ( ! [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) => (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(X0,sK1))) & v1_relat_1(sK1))) )),
% 7.19/1.42    introduced(choice_axiom,[])).
% 7.19/1.42  
% 7.19/1.42  fof(f14,plain,(
% 7.19/1.42    ? [X0] : (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(sK0,X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 7.19/1.42    introduced(choice_axiom,[])).
% 7.19/1.42  
% 7.19/1.42  fof(f16,plain,(
% 7.19/1.42    (~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 7.19/1.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15,f14])).
% 7.19/1.42  
% 7.19/1.42  fof(f24,plain,(
% 7.19/1.42    v1_relat_1(sK0)),
% 7.19/1.42    inference(cnf_transformation,[],[f16])).
% 7.19/1.42  
% 7.19/1.42  fof(f6,axiom,(
% 7.19/1.42    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 7.19/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.19/1.42  
% 7.19/1.42  fof(f11,plain,(
% 7.19/1.42    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 7.19/1.42    inference(ennf_transformation,[],[f6])).
% 7.19/1.42  
% 7.19/1.42  fof(f22,plain,(
% 7.19/1.42    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.19/1.42    inference(cnf_transformation,[],[f11])).
% 7.19/1.42  
% 7.19/1.42  fof(f5,axiom,(
% 7.19/1.42    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 7.19/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.19/1.42  
% 7.19/1.42  fof(f21,plain,(
% 7.19/1.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 7.19/1.42    inference(cnf_transformation,[],[f5])).
% 7.19/1.42  
% 7.19/1.42  fof(f29,plain,(
% 7.19/1.42    ( ! [X0,X1] : (v1_relat_1(k6_subset_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.19/1.42    inference(definition_unfolding,[],[f22,f21])).
% 7.19/1.42  
% 7.19/1.42  fof(f25,plain,(
% 7.19/1.42    v1_relat_1(sK1)),
% 7.19/1.42    inference(cnf_transformation,[],[f16])).
% 7.19/1.42  
% 7.19/1.42  fof(f7,axiom,(
% 7.19/1.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))))),
% 7.19/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.19/1.42  
% 7.19/1.42  fof(f12,plain,(
% 7.19/1.42    ! [X0] : (! [X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.19/1.42    inference(ennf_transformation,[],[f7])).
% 7.19/1.42  
% 7.19/1.42  fof(f23,plain,(
% 7.19/1.42    ( ! [X0,X1] : (k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.19/1.42    inference(cnf_transformation,[],[f12])).
% 7.19/1.42  
% 7.19/1.42  fof(f3,axiom,(
% 7.19/1.42    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 7.19/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.19/1.42  
% 7.19/1.42  fof(f10,plain,(
% 7.19/1.42    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 7.19/1.42    inference(ennf_transformation,[],[f3])).
% 7.19/1.42  
% 7.19/1.42  fof(f19,plain,(
% 7.19/1.42    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.19/1.42    inference(cnf_transformation,[],[f10])).
% 7.19/1.42  
% 7.19/1.42  fof(f28,plain,(
% 7.19/1.42    ( ! [X2,X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 7.19/1.42    inference(definition_unfolding,[],[f19,f21])).
% 7.19/1.42  
% 7.19/1.42  fof(f26,plain,(
% 7.19/1.42    ~r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1)))),
% 7.19/1.42    inference(cnf_transformation,[],[f16])).
% 7.19/1.42  
% 7.19/1.42  fof(f2,axiom,(
% 7.19/1.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.19/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.19/1.42  
% 7.19/1.42  fof(f18,plain,(
% 7.19/1.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.19/1.42    inference(cnf_transformation,[],[f2])).
% 7.19/1.42  
% 7.19/1.42  fof(f27,plain,(
% 7.19/1.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k6_subset_1(X1,X0))) )),
% 7.19/1.42    inference(definition_unfolding,[],[f18,f21])).
% 7.19/1.42  
% 7.19/1.42  fof(f1,axiom,(
% 7.19/1.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.19/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.19/1.42  
% 7.19/1.42  fof(f17,plain,(
% 7.19/1.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.19/1.42    inference(cnf_transformation,[],[f1])).
% 7.19/1.42  
% 7.19/1.42  fof(f4,axiom,(
% 7.19/1.42    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 7.19/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.19/1.42  
% 7.19/1.42  fof(f20,plain,(
% 7.19/1.42    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 7.19/1.42    inference(cnf_transformation,[],[f4])).
% 7.19/1.42  
% 7.19/1.42  cnf(c_8,negated_conjecture,
% 7.19/1.42      ( v1_relat_1(sK0) ),
% 7.19/1.42      inference(cnf_transformation,[],[f24]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_227,plain,
% 7.19/1.42      ( v1_relat_1(sK0) = iProver_top ),
% 7.19/1.42      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_4,plain,
% 7.19/1.42      ( ~ v1_relat_1(X0) | v1_relat_1(k6_subset_1(X0,X1)) ),
% 7.19/1.42      inference(cnf_transformation,[],[f29]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_231,plain,
% 7.19/1.42      ( v1_relat_1(X0) != iProver_top
% 7.19/1.42      | v1_relat_1(k6_subset_1(X0,X1)) = iProver_top ),
% 7.19/1.42      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_7,negated_conjecture,
% 7.19/1.42      ( v1_relat_1(sK1) ),
% 7.19/1.42      inference(cnf_transformation,[],[f25]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_228,plain,
% 7.19/1.42      ( v1_relat_1(sK1) = iProver_top ),
% 7.19/1.42      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_5,plain,
% 7.19/1.42      ( ~ v1_relat_1(X0)
% 7.19/1.42      | ~ v1_relat_1(X1)
% 7.19/1.42      | k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1)) ),
% 7.19/1.42      inference(cnf_transformation,[],[f23]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_230,plain,
% 7.19/1.42      ( k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) = k1_relat_1(k2_xboole_0(X0,X1))
% 7.19/1.42      | v1_relat_1(X0) != iProver_top
% 7.19/1.42      | v1_relat_1(X1) != iProver_top ),
% 7.19/1.42      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_576,plain,
% 7.19/1.42      ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(X0)) = k1_relat_1(k2_xboole_0(sK1,X0))
% 7.19/1.42      | v1_relat_1(X0) != iProver_top ),
% 7.19/1.42      inference(superposition,[status(thm)],[c_228,c_230]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_1355,plain,
% 7.19/1.42      ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(X0,X1))) = k1_relat_1(k2_xboole_0(sK1,k6_subset_1(X0,X1)))
% 7.19/1.42      | v1_relat_1(X0) != iProver_top ),
% 7.19/1.42      inference(superposition,[status(thm)],[c_231,c_576]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_5506,plain,
% 7.19/1.42      ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(k6_subset_1(sK0,X0))) = k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X0))) ),
% 7.19/1.42      inference(superposition,[status(thm)],[c_227,c_1355]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_2,plain,
% 7.19/1.42      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 7.19/1.42      | r1_tarski(k6_subset_1(X0,X1),X2) ),
% 7.19/1.42      inference(cnf_transformation,[],[f28]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_233,plain,
% 7.19/1.42      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 7.19/1.42      | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
% 7.19/1.42      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_6365,plain,
% 7.19/1.42      ( r1_tarski(X0,k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,X1)))) != iProver_top
% 7.19/1.42      | r1_tarski(k6_subset_1(X0,k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,X1))) = iProver_top ),
% 7.19/1.42      inference(superposition,[status(thm)],[c_5506,c_233]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_6,negated_conjecture,
% 7.19/1.42      ( ~ r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) ),
% 7.19/1.42      inference(cnf_transformation,[],[f26]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_229,plain,
% 7.19/1.42      ( r1_tarski(k6_subset_1(k1_relat_1(sK0),k1_relat_1(sK1)),k1_relat_1(k6_subset_1(sK0,sK1))) != iProver_top ),
% 7.19/1.42      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_31989,plain,
% 7.19/1.42      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) != iProver_top ),
% 7.19/1.42      inference(superposition,[status(thm)],[c_6365,c_229]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_1,plain,
% 7.19/1.42      ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = k2_xboole_0(X0,X1) ),
% 7.19/1.42      inference(cnf_transformation,[],[f27]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_817,plain,
% 7.19/1.42      ( k2_xboole_0(k1_relat_1(sK1),k1_relat_1(sK0)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
% 7.19/1.42      inference(superposition,[status(thm)],[c_227,c_576]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_0,plain,
% 7.19/1.42      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.19/1.42      inference(cnf_transformation,[],[f17]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_961,plain,
% 7.19/1.42      ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
% 7.19/1.42      inference(superposition,[status(thm)],[c_817,c_0]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_577,plain,
% 7.19/1.42      ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(X0)) = k1_relat_1(k2_xboole_0(sK0,X0))
% 7.19/1.42      | v1_relat_1(X0) != iProver_top ),
% 7.19/1.42      inference(superposition,[status(thm)],[c_227,c_230]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_1078,plain,
% 7.19/1.42      ( k2_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) = k1_relat_1(k2_xboole_0(sK0,sK1)) ),
% 7.19/1.42      inference(superposition,[status(thm)],[c_228,c_577]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_1443,plain,
% 7.19/1.42      ( k1_relat_1(k2_xboole_0(sK0,sK1)) = k1_relat_1(k2_xboole_0(sK1,sK0)) ),
% 7.19/1.42      inference(light_normalisation,[status(thm)],[c_961,c_1078]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_31990,plain,
% 7.19/1.42      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) != iProver_top ),
% 7.19/1.42      inference(demodulation,[status(thm)],[c_31989,c_1,c_1443]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_3,plain,
% 7.19/1.42      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 7.19/1.42      inference(cnf_transformation,[],[f20]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_232,plain,
% 7.19/1.42      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 7.19/1.42      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(c_1088,plain,
% 7.19/1.42      ( r1_tarski(k1_relat_1(sK0),k1_relat_1(k2_xboole_0(sK0,sK1))) = iProver_top ),
% 7.19/1.42      inference(superposition,[status(thm)],[c_1078,c_232]) ).
% 7.19/1.42  
% 7.19/1.42  cnf(contradiction,plain,
% 7.19/1.42      ( $false ),
% 7.19/1.42      inference(minisat,[status(thm)],[c_31990,c_1088]) ).
% 7.19/1.42  
% 7.19/1.42  
% 7.19/1.42  % SZS output end CNFRefutation for theBenchmark.p
% 7.19/1.42  
% 7.19/1.42  ------                               Statistics
% 7.19/1.42  
% 7.19/1.42  ------ General
% 7.19/1.42  
% 7.19/1.42  abstr_ref_over_cycles:                  0
% 7.19/1.42  abstr_ref_under_cycles:                 0
% 7.19/1.42  gc_basic_clause_elim:                   0
% 7.19/1.42  forced_gc_time:                         0
% 7.19/1.42  parsing_time:                           0.017
% 7.19/1.42  unif_index_cands_time:                  0.
% 7.19/1.42  unif_index_add_time:                    0.
% 7.19/1.42  orderings_time:                         0.
% 7.19/1.42  out_proof_time:                         0.017
% 7.19/1.42  total_time:                             0.874
% 7.19/1.42  num_of_symbols:                         38
% 7.19/1.42  num_of_terms:                           25342
% 7.19/1.42  
% 7.19/1.42  ------ Preprocessing
% 7.19/1.42  
% 7.19/1.42  num_of_splits:                          0
% 7.19/1.42  num_of_split_atoms:                     0
% 7.19/1.42  num_of_reused_defs:                     0
% 7.19/1.42  num_eq_ax_congr_red:                    0
% 7.19/1.42  num_of_sem_filtered_clauses:            1
% 7.19/1.42  num_of_subtypes:                        1
% 7.19/1.42  monotx_restored_types:                  0
% 7.19/1.42  sat_num_of_epr_types:                   0
% 7.19/1.42  sat_num_of_non_cyclic_types:            0
% 7.19/1.42  sat_guarded_non_collapsed_types:        0
% 7.19/1.42  num_pure_diseq_elim:                    0
% 7.19/1.42  simp_replaced_by:                       0
% 7.19/1.42  res_preprocessed:                       42
% 7.19/1.42  prep_upred:                             0
% 7.19/1.42  prep_unflattend:                        0
% 7.19/1.42  smt_new_axioms:                         0
% 7.19/1.42  pred_elim_cands:                        2
% 7.19/1.42  pred_elim:                              0
% 7.19/1.42  pred_elim_cl:                           0
% 7.19/1.42  pred_elim_cycles:                       1
% 7.19/1.42  merged_defs:                            0
% 7.19/1.42  merged_defs_ncl:                        0
% 7.19/1.42  bin_hyper_res:                          0
% 7.19/1.42  prep_cycles:                            3
% 7.19/1.42  pred_elim_time:                         0.
% 7.19/1.42  splitting_time:                         0.
% 7.19/1.42  sem_filter_time:                        0.
% 7.19/1.42  monotx_time:                            0.
% 7.19/1.42  subtype_inf_time:                       0.
% 7.19/1.42  
% 7.19/1.42  ------ Problem properties
% 7.19/1.42  
% 7.19/1.42  clauses:                                9
% 7.19/1.42  conjectures:                            3
% 7.19/1.42  epr:                                    2
% 7.19/1.42  horn:                                   9
% 7.19/1.42  ground:                                 3
% 7.19/1.42  unary:                                  6
% 7.19/1.42  binary:                                 2
% 7.19/1.42  lits:                                   13
% 7.19/1.42  lits_eq:                                3
% 7.19/1.42  fd_pure:                                0
% 7.19/1.42  fd_pseudo:                              0
% 7.19/1.42  fd_cond:                                0
% 7.19/1.42  fd_pseudo_cond:                         0
% 7.19/1.42  ac_symbols:                             0
% 7.19/1.42  
% 7.19/1.42  ------ Propositional Solver
% 7.19/1.42  
% 7.19/1.42  prop_solver_calls:                      30
% 7.19/1.42  prop_fast_solver_calls:                 444
% 7.19/1.42  smt_solver_calls:                       0
% 7.19/1.42  smt_fast_solver_calls:                  0
% 7.19/1.42  prop_num_of_clauses:                    7532
% 7.19/1.42  prop_preprocess_simplified:             16375
% 7.19/1.42  prop_fo_subsumed:                       0
% 7.19/1.42  prop_solver_time:                       0.
% 7.19/1.42  smt_solver_time:                        0.
% 7.19/1.42  smt_fast_solver_time:                   0.
% 7.19/1.42  prop_fast_solver_time:                  0.
% 7.19/1.42  prop_unsat_core_time:                   0.001
% 7.19/1.42  
% 7.19/1.42  ------ QBF
% 7.19/1.42  
% 7.19/1.42  qbf_q_res:                              0
% 7.19/1.42  qbf_num_tautologies:                    0
% 7.19/1.42  qbf_prep_cycles:                        0
% 7.19/1.42  
% 7.19/1.42  ------ BMC1
% 7.19/1.42  
% 7.19/1.42  bmc1_current_bound:                     -1
% 7.19/1.42  bmc1_last_solved_bound:                 -1
% 7.19/1.42  bmc1_unsat_core_size:                   -1
% 7.19/1.42  bmc1_unsat_core_parents_size:           -1
% 7.19/1.42  bmc1_merge_next_fun:                    0
% 7.19/1.42  bmc1_unsat_core_clauses_time:           0.
% 7.19/1.42  
% 7.19/1.42  ------ Instantiation
% 7.19/1.42  
% 7.19/1.42  inst_num_of_clauses:                    2535
% 7.19/1.42  inst_num_in_passive:                    1479
% 7.19/1.42  inst_num_in_active:                     1055
% 7.19/1.42  inst_num_in_unprocessed:                1
% 7.19/1.42  inst_num_of_loops:                      1120
% 7.19/1.42  inst_num_of_learning_restarts:          0
% 7.19/1.42  inst_num_moves_active_passive:          56
% 7.19/1.42  inst_lit_activity:                      0
% 7.19/1.42  inst_lit_activity_moves:                0
% 7.19/1.42  inst_num_tautologies:                   0
% 7.19/1.42  inst_num_prop_implied:                  0
% 7.19/1.42  inst_num_existing_simplified:           0
% 7.19/1.42  inst_num_eq_res_simplified:             0
% 7.19/1.42  inst_num_child_elim:                    0
% 7.19/1.42  inst_num_of_dismatching_blockings:      7401
% 7.19/1.42  inst_num_of_non_proper_insts:           7393
% 7.19/1.42  inst_num_of_duplicates:                 0
% 7.19/1.42  inst_inst_num_from_inst_to_res:         0
% 7.19/1.42  inst_dismatching_checking_time:         0.
% 7.19/1.42  
% 7.19/1.42  ------ Resolution
% 7.19/1.42  
% 7.19/1.42  res_num_of_clauses:                     0
% 7.19/1.42  res_num_in_passive:                     0
% 7.19/1.42  res_num_in_active:                      0
% 7.19/1.42  res_num_of_loops:                       45
% 7.19/1.42  res_forward_subset_subsumed:            1634
% 7.19/1.42  res_backward_subset_subsumed:           8
% 7.19/1.42  res_forward_subsumed:                   0
% 7.19/1.42  res_backward_subsumed:                  0
% 7.19/1.42  res_forward_subsumption_resolution:     0
% 7.19/1.42  res_backward_subsumption_resolution:    0
% 7.19/1.42  res_clause_to_clause_subsumption:       5483
% 7.19/1.42  res_orphan_elimination:                 0
% 7.19/1.42  res_tautology_del:                      697
% 7.19/1.42  res_num_eq_res_simplified:              0
% 7.19/1.42  res_num_sel_changes:                    0
% 7.19/1.42  res_moves_from_active_to_pass:          0
% 7.19/1.42  
% 7.19/1.42  ------ Superposition
% 7.19/1.42  
% 7.19/1.42  sup_time_total:                         0.
% 7.19/1.42  sup_time_generating:                    0.
% 7.19/1.42  sup_time_sim_full:                      0.
% 7.19/1.42  sup_time_sim_immed:                     0.
% 7.19/1.42  
% 7.19/1.42  sup_num_of_clauses:                     672
% 7.19/1.42  sup_num_in_active:                      209
% 7.19/1.42  sup_num_in_passive:                     463
% 7.19/1.42  sup_num_of_loops:                       222
% 7.19/1.42  sup_fw_superposition:                   694
% 7.19/1.42  sup_bw_superposition:                   464
% 7.19/1.42  sup_immediate_simplified:               14
% 7.19/1.42  sup_given_eliminated:                   4
% 7.19/1.42  comparisons_done:                       0
% 7.19/1.42  comparisons_avoided:                    0
% 7.19/1.42  
% 7.19/1.42  ------ Simplifications
% 7.19/1.42  
% 7.19/1.42  
% 7.19/1.42  sim_fw_subset_subsumed:                 0
% 7.19/1.42  sim_bw_subset_subsumed:                 0
% 7.19/1.42  sim_fw_subsumed:                        0
% 7.19/1.42  sim_bw_subsumed:                        0
% 7.19/1.42  sim_fw_subsumption_res:                 0
% 7.19/1.42  sim_bw_subsumption_res:                 0
% 7.19/1.42  sim_tautology_del:                      0
% 7.19/1.42  sim_eq_tautology_del:                   0
% 7.19/1.42  sim_eq_res_simp:                        0
% 7.19/1.42  sim_fw_demodulated:                     1
% 7.19/1.42  sim_bw_demodulated:                     22
% 7.19/1.42  sim_light_normalised:                   56
% 7.19/1.42  sim_joinable_taut:                      0
% 7.19/1.42  sim_joinable_simp:                      0
% 7.19/1.42  sim_ac_normalised:                      0
% 7.19/1.42  sim_smt_subsumption:                    0
% 7.19/1.42  
%------------------------------------------------------------------------------
