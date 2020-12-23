%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:42:45 EST 2020

% Result     : Theorem 0.60s
% Output     : CNFRefutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   60 (  80 expanded)
%              Number of clauses        :   18 (  18 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :   16
%              Number of atoms          :   94 ( 114 expanded)
%              Number of equality atoms :   20 (  40 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f29,f41])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f28,f42])).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f27,f43])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f26,f44])).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f25,f45])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f46])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,conjecture,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(negated_conjecture,[],[f14])).

fof(f20,plain,(
    ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(ennf_transformation,[],[f15])).

fof(f23,plain,
    ( ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))
   => ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f23])).

fof(f40,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f49,plain,(
    ~ m1_subset_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(definition_unfolding,[],[f40,f46])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_367,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_129,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(resolution,[status(thm)],[c_2,c_4])).

cnf(c_361,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_76,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
    inference(prop_impl,[status(thm)],[c_0])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_80,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_81,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_80])).

cnf(c_145,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(resolution,[status(thm)],[c_76,c_81])).

cnf(c_244,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_145])).

cnf(c_245,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_244])).

cnf(c_348,plain,
    ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_353,plain,
    ( m1_subset_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_348])).

cnf(c_8,negated_conjecture,
    ( ~ m1_subset_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_367,c_361,c_353,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n011.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 13:07:57 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running in FOF mode
% 0.60/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.60/0.97  
% 0.60/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.60/0.97  
% 0.60/0.97  ------  iProver source info
% 0.60/0.97  
% 0.60/0.97  git: date: 2020-06-30 10:37:57 +0100
% 0.60/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.60/0.97  git: non_committed_changes: false
% 0.60/0.97  git: last_make_outside_of_git: false
% 0.60/0.97  
% 0.60/0.97  ------ 
% 0.60/0.97  
% 0.60/0.97  ------ Input Options
% 0.60/0.97  
% 0.60/0.97  --out_options                           all
% 0.60/0.97  --tptp_safe_out                         true
% 0.60/0.97  --problem_path                          ""
% 0.60/0.97  --include_path                          ""
% 0.60/0.97  --clausifier                            res/vclausify_rel
% 0.60/0.97  --clausifier_options                    --mode clausify
% 0.60/0.97  --stdin                                 false
% 0.60/0.97  --stats_out                             all
% 0.60/0.97  
% 0.60/0.97  ------ General Options
% 0.60/0.97  
% 0.60/0.97  --fof                                   false
% 0.60/0.97  --time_out_real                         305.
% 0.60/0.97  --time_out_virtual                      -1.
% 0.60/0.97  --symbol_type_check                     false
% 0.60/0.97  --clausify_out                          false
% 0.60/0.97  --sig_cnt_out                           false
% 0.60/0.97  --trig_cnt_out                          false
% 0.60/0.97  --trig_cnt_out_tolerance                1.
% 0.60/0.97  --trig_cnt_out_sk_spl                   false
% 0.60/0.97  --abstr_cl_out                          false
% 0.60/0.97  
% 0.60/0.97  ------ Global Options
% 0.60/0.97  
% 0.60/0.97  --schedule                              default
% 0.60/0.97  --add_important_lit                     false
% 0.60/0.97  --prop_solver_per_cl                    1000
% 0.60/0.97  --min_unsat_core                        false
% 0.60/0.97  --soft_assumptions                      false
% 0.60/0.97  --soft_lemma_size                       3
% 0.60/0.97  --prop_impl_unit_size                   0
% 0.60/0.97  --prop_impl_unit                        []
% 0.60/0.97  --share_sel_clauses                     true
% 0.60/0.97  --reset_solvers                         false
% 0.60/0.97  --bc_imp_inh                            [conj_cone]
% 0.60/0.97  --conj_cone_tolerance                   3.
% 0.60/0.97  --extra_neg_conj                        none
% 0.60/0.97  --large_theory_mode                     true
% 0.60/0.97  --prolific_symb_bound                   200
% 0.60/0.97  --lt_threshold                          2000
% 0.60/0.97  --clause_weak_htbl                      true
% 0.60/0.97  --gc_record_bc_elim                     false
% 0.60/0.97  
% 0.60/0.97  ------ Preprocessing Options
% 0.60/0.97  
% 0.60/0.97  --preprocessing_flag                    true
% 0.60/0.97  --time_out_prep_mult                    0.1
% 0.60/0.97  --splitting_mode                        input
% 0.60/0.97  --splitting_grd                         true
% 0.60/0.97  --splitting_cvd                         false
% 0.60/0.97  --splitting_cvd_svl                     false
% 0.60/0.97  --splitting_nvd                         32
% 0.60/0.97  --sub_typing                            true
% 0.60/0.97  --prep_gs_sim                           true
% 0.60/0.97  --prep_unflatten                        true
% 0.60/0.97  --prep_res_sim                          true
% 0.60/0.97  --prep_upred                            true
% 0.60/0.97  --prep_sem_filter                       exhaustive
% 0.60/0.97  --prep_sem_filter_out                   false
% 0.60/0.97  --pred_elim                             true
% 0.60/0.97  --res_sim_input                         true
% 0.60/0.97  --eq_ax_congr_red                       true
% 0.60/0.97  --pure_diseq_elim                       true
% 0.60/0.97  --brand_transform                       false
% 0.60/0.97  --non_eq_to_eq                          false
% 0.60/0.97  --prep_def_merge                        true
% 0.60/0.97  --prep_def_merge_prop_impl              false
% 0.60/0.97  --prep_def_merge_mbd                    true
% 0.60/0.97  --prep_def_merge_tr_red                 false
% 0.60/0.97  --prep_def_merge_tr_cl                  false
% 0.60/0.97  --smt_preprocessing                     true
% 0.60/0.97  --smt_ac_axioms                         fast
% 0.60/0.97  --preprocessed_out                      false
% 0.60/0.97  --preprocessed_stats                    false
% 0.60/0.97  
% 0.60/0.97  ------ Abstraction refinement Options
% 0.60/0.97  
% 0.60/0.97  --abstr_ref                             []
% 0.60/0.97  --abstr_ref_prep                        false
% 0.60/0.97  --abstr_ref_until_sat                   false
% 0.60/0.97  --abstr_ref_sig_restrict                funpre
% 0.60/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 0.60/0.97  --abstr_ref_under                       []
% 0.60/0.97  
% 0.60/0.97  ------ SAT Options
% 0.60/0.97  
% 0.60/0.97  --sat_mode                              false
% 0.60/0.97  --sat_fm_restart_options                ""
% 0.60/0.97  --sat_gr_def                            false
% 0.60/0.97  --sat_epr_types                         true
% 0.60/0.97  --sat_non_cyclic_types                  false
% 0.60/0.97  --sat_finite_models                     false
% 0.60/0.97  --sat_fm_lemmas                         false
% 0.60/0.97  --sat_fm_prep                           false
% 0.60/0.97  --sat_fm_uc_incr                        true
% 0.60/0.97  --sat_out_model                         small
% 0.60/0.97  --sat_out_clauses                       false
% 0.60/0.97  
% 0.60/0.97  ------ QBF Options
% 0.60/0.97  
% 0.60/0.97  --qbf_mode                              false
% 0.60/0.97  --qbf_elim_univ                         false
% 0.60/0.97  --qbf_dom_inst                          none
% 0.60/0.97  --qbf_dom_pre_inst                      false
% 0.60/0.97  --qbf_sk_in                             false
% 0.60/0.97  --qbf_pred_elim                         true
% 0.60/0.97  --qbf_split                             512
% 0.60/0.97  
% 0.60/0.97  ------ BMC1 Options
% 0.60/0.97  
% 0.60/0.97  --bmc1_incremental                      false
% 0.60/0.97  --bmc1_axioms                           reachable_all
% 0.60/0.97  --bmc1_min_bound                        0
% 0.60/0.97  --bmc1_max_bound                        -1
% 0.60/0.97  --bmc1_max_bound_default                -1
% 0.60/0.97  --bmc1_symbol_reachability              true
% 0.60/0.97  --bmc1_property_lemmas                  false
% 0.60/0.97  --bmc1_k_induction                      false
% 0.60/0.97  --bmc1_non_equiv_states                 false
% 0.60/0.97  --bmc1_deadlock                         false
% 0.60/0.97  --bmc1_ucm                              false
% 0.60/0.97  --bmc1_add_unsat_core                   none
% 0.60/0.97  --bmc1_unsat_core_children              false
% 0.60/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 0.60/0.97  --bmc1_out_stat                         full
% 0.60/0.97  --bmc1_ground_init                      false
% 0.60/0.97  --bmc1_pre_inst_next_state              false
% 0.60/0.97  --bmc1_pre_inst_state                   false
% 0.60/0.97  --bmc1_pre_inst_reach_state             false
% 0.60/0.97  --bmc1_out_unsat_core                   false
% 0.60/0.97  --bmc1_aig_witness_out                  false
% 0.60/0.97  --bmc1_verbose                          false
% 0.60/0.97  --bmc1_dump_clauses_tptp                false
% 0.60/0.97  --bmc1_dump_unsat_core_tptp             false
% 0.60/0.97  --bmc1_dump_file                        -
% 0.60/0.97  --bmc1_ucm_expand_uc_limit              128
% 0.60/0.97  --bmc1_ucm_n_expand_iterations          6
% 0.60/0.97  --bmc1_ucm_extend_mode                  1
% 0.60/0.97  --bmc1_ucm_init_mode                    2
% 0.60/0.97  --bmc1_ucm_cone_mode                    none
% 0.60/0.97  --bmc1_ucm_reduced_relation_type        0
% 0.60/0.97  --bmc1_ucm_relax_model                  4
% 0.60/0.97  --bmc1_ucm_full_tr_after_sat            true
% 0.60/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 0.60/0.97  --bmc1_ucm_layered_model                none
% 0.60/0.97  --bmc1_ucm_max_lemma_size               10
% 0.60/0.97  
% 0.60/0.97  ------ AIG Options
% 0.60/0.97  
% 0.60/0.97  --aig_mode                              false
% 0.60/0.97  
% 0.60/0.97  ------ Instantiation Options
% 0.60/0.97  
% 0.60/0.97  --instantiation_flag                    true
% 0.60/0.97  --inst_sos_flag                         false
% 0.60/0.97  --inst_sos_phase                        true
% 0.60/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.60/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.60/0.97  --inst_lit_sel_side                     num_symb
% 0.60/0.97  --inst_solver_per_active                1400
% 0.60/0.97  --inst_solver_calls_frac                1.
% 0.60/0.97  --inst_passive_queue_type               priority_queues
% 0.60/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.60/0.97  --inst_passive_queues_freq              [25;2]
% 0.60/0.97  --inst_dismatching                      true
% 0.60/0.97  --inst_eager_unprocessed_to_passive     true
% 0.60/0.97  --inst_prop_sim_given                   true
% 0.60/0.97  --inst_prop_sim_new                     false
% 0.60/0.97  --inst_subs_new                         false
% 0.60/0.97  --inst_eq_res_simp                      false
% 0.60/0.97  --inst_subs_given                       false
% 0.60/0.97  --inst_orphan_elimination               true
% 0.60/0.97  --inst_learning_loop_flag               true
% 0.60/0.97  --inst_learning_start                   3000
% 0.60/0.97  --inst_learning_factor                  2
% 0.60/0.97  --inst_start_prop_sim_after_learn       3
% 0.60/0.97  --inst_sel_renew                        solver
% 0.60/0.97  --inst_lit_activity_flag                true
% 0.60/0.97  --inst_restr_to_given                   false
% 0.60/0.97  --inst_activity_threshold               500
% 0.60/0.97  --inst_out_proof                        true
% 0.60/0.97  
% 0.60/0.97  ------ Resolution Options
% 0.60/0.97  
% 0.60/0.97  --resolution_flag                       true
% 0.60/0.97  --res_lit_sel                           adaptive
% 0.60/0.97  --res_lit_sel_side                      none
% 0.60/0.97  --res_ordering                          kbo
% 0.60/0.97  --res_to_prop_solver                    active
% 0.60/0.97  --res_prop_simpl_new                    false
% 0.60/0.97  --res_prop_simpl_given                  true
% 0.60/0.97  --res_passive_queue_type                priority_queues
% 0.60/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.60/0.97  --res_passive_queues_freq               [15;5]
% 0.60/0.97  --res_forward_subs                      full
% 0.60/0.97  --res_backward_subs                     full
% 0.60/0.97  --res_forward_subs_resolution           true
% 0.60/0.97  --res_backward_subs_resolution          true
% 0.60/0.97  --res_orphan_elimination                true
% 0.60/0.97  --res_time_limit                        2.
% 0.60/0.97  --res_out_proof                         true
% 0.60/0.97  
% 0.60/0.97  ------ Superposition Options
% 0.60/0.97  
% 0.60/0.97  --superposition_flag                    true
% 0.60/0.97  --sup_passive_queue_type                priority_queues
% 0.60/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.60/0.97  --sup_passive_queues_freq               [8;1;4]
% 0.60/0.97  --demod_completeness_check              fast
% 0.60/0.97  --demod_use_ground                      true
% 0.60/0.97  --sup_to_prop_solver                    passive
% 0.60/0.97  --sup_prop_simpl_new                    true
% 0.60/0.97  --sup_prop_simpl_given                  true
% 0.60/0.97  --sup_fun_splitting                     false
% 0.60/0.97  --sup_smt_interval                      50000
% 0.60/0.97  
% 0.60/0.97  ------ Superposition Simplification Setup
% 0.60/0.97  
% 0.60/0.97  --sup_indices_passive                   []
% 0.60/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.60/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.60/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.60/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 0.60/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.60/0.97  --sup_full_bw                           [BwDemod]
% 0.60/0.97  --sup_immed_triv                        [TrivRules]
% 0.60/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.60/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.60/0.97  --sup_immed_bw_main                     []
% 0.60/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.60/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 0.60/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.60/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.60/0.97  
% 0.60/0.97  ------ Combination Options
% 0.60/0.97  
% 0.60/0.97  --comb_res_mult                         3
% 0.60/0.97  --comb_sup_mult                         2
% 0.60/0.97  --comb_inst_mult                        10
% 0.60/0.97  
% 0.60/0.97  ------ Debug Options
% 0.60/0.97  
% 0.60/0.97  --dbg_backtrace                         false
% 0.60/0.97  --dbg_dump_prop_clauses                 false
% 0.60/0.97  --dbg_dump_prop_clauses_file            -
% 0.60/0.97  --dbg_out_stat                          false
% 0.60/0.97  ------ Parsing...
% 0.60/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.60/0.97  
% 0.60/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 0.60/0.97  
% 0.60/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.60/0.97  ------ Proving...
% 0.60/0.97  ------ Problem Properties 
% 0.60/0.97  
% 0.60/0.97  
% 0.60/0.97  clauses                                 6
% 0.60/0.97  conjectures                             1
% 0.60/0.97  EPR                                     0
% 0.60/0.97  Horn                                    6
% 0.60/0.97  unary                                   2
% 0.60/0.97  binary                                  3
% 0.60/0.97  lits                                    11
% 0.60/0.97  lits eq                                 0
% 0.60/0.97  fd_pure                                 0
% 0.60/0.97  fd_pseudo                               0
% 0.60/0.97  fd_cond                                 0
% 0.60/0.97  fd_pseudo_cond                          0
% 0.60/0.97  AC symbols                              0
% 0.60/0.97  
% 0.60/0.97  ------ Schedule dynamic 5 is on 
% 0.60/0.97  
% 0.60/0.97  ------ no equalities: superposition off 
% 0.60/0.97  
% 0.60/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.60/0.97  
% 0.60/0.97  
% 0.60/0.97  ------ 
% 0.60/0.97  Current options:
% 0.60/0.97  ------ 
% 0.60/0.97  
% 0.60/0.97  ------ Input Options
% 0.60/0.97  
% 0.60/0.97  --out_options                           all
% 0.60/0.97  --tptp_safe_out                         true
% 0.60/0.97  --problem_path                          ""
% 0.60/0.97  --include_path                          ""
% 0.60/0.97  --clausifier                            res/vclausify_rel
% 0.60/0.97  --clausifier_options                    --mode clausify
% 0.60/0.97  --stdin                                 false
% 0.60/0.97  --stats_out                             all
% 0.60/0.97  
% 0.60/0.97  ------ General Options
% 0.60/0.97  
% 0.60/0.97  --fof                                   false
% 0.60/0.97  --time_out_real                         305.
% 0.60/0.97  --time_out_virtual                      -1.
% 0.60/0.97  --symbol_type_check                     false
% 0.60/0.97  --clausify_out                          false
% 0.60/0.97  --sig_cnt_out                           false
% 0.60/0.97  --trig_cnt_out                          false
% 0.60/0.97  --trig_cnt_out_tolerance                1.
% 0.60/0.97  --trig_cnt_out_sk_spl                   false
% 0.60/0.97  --abstr_cl_out                          false
% 0.60/0.97  
% 0.60/0.97  ------ Global Options
% 0.60/0.97  
% 0.60/0.97  --schedule                              default
% 0.60/0.97  --add_important_lit                     false
% 0.60/0.97  --prop_solver_per_cl                    1000
% 0.60/0.97  --min_unsat_core                        false
% 0.60/0.97  --soft_assumptions                      false
% 0.60/0.97  --soft_lemma_size                       3
% 0.60/0.97  --prop_impl_unit_size                   0
% 0.60/0.97  --prop_impl_unit                        []
% 0.60/0.97  --share_sel_clauses                     true
% 0.60/0.97  --reset_solvers                         false
% 0.60/0.97  --bc_imp_inh                            [conj_cone]
% 0.60/0.97  --conj_cone_tolerance                   3.
% 0.60/0.97  --extra_neg_conj                        none
% 0.60/0.97  --large_theory_mode                     true
% 0.60/0.97  --prolific_symb_bound                   200
% 0.60/0.97  --lt_threshold                          2000
% 0.60/0.97  --clause_weak_htbl                      true
% 0.60/0.97  --gc_record_bc_elim                     false
% 0.60/0.97  
% 0.60/0.97  ------ Preprocessing Options
% 0.60/0.97  
% 0.60/0.97  --preprocessing_flag                    true
% 0.60/0.97  --time_out_prep_mult                    0.1
% 0.60/0.97  --splitting_mode                        input
% 0.60/0.97  --splitting_grd                         true
% 0.60/0.97  --splitting_cvd                         false
% 0.60/0.97  --splitting_cvd_svl                     false
% 0.60/0.97  --splitting_nvd                         32
% 0.60/0.97  --sub_typing                            true
% 0.60/0.97  --prep_gs_sim                           true
% 0.60/0.97  --prep_unflatten                        true
% 0.60/0.97  --prep_res_sim                          true
% 0.60/0.97  --prep_upred                            true
% 0.60/0.97  --prep_sem_filter                       exhaustive
% 0.60/0.97  --prep_sem_filter_out                   false
% 0.60/0.97  --pred_elim                             true
% 0.60/0.97  --res_sim_input                         true
% 0.60/0.97  --eq_ax_congr_red                       true
% 0.60/0.97  --pure_diseq_elim                       true
% 0.60/0.97  --brand_transform                       false
% 0.60/0.97  --non_eq_to_eq                          false
% 0.60/0.97  --prep_def_merge                        true
% 0.60/0.97  --prep_def_merge_prop_impl              false
% 0.60/0.97  --prep_def_merge_mbd                    true
% 0.60/0.97  --prep_def_merge_tr_red                 false
% 0.60/0.97  --prep_def_merge_tr_cl                  false
% 0.60/0.97  --smt_preprocessing                     true
% 0.60/0.97  --smt_ac_axioms                         fast
% 0.60/0.97  --preprocessed_out                      false
% 0.60/0.97  --preprocessed_stats                    false
% 0.60/0.97  
% 0.60/0.97  ------ Abstraction refinement Options
% 0.60/0.97  
% 0.60/0.97  --abstr_ref                             []
% 0.60/0.97  --abstr_ref_prep                        false
% 0.60/0.97  --abstr_ref_until_sat                   false
% 0.60/0.97  --abstr_ref_sig_restrict                funpre
% 0.60/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 0.60/0.97  --abstr_ref_under                       []
% 0.60/0.97  
% 0.60/0.97  ------ SAT Options
% 0.60/0.97  
% 0.60/0.97  --sat_mode                              false
% 0.60/0.97  --sat_fm_restart_options                ""
% 0.60/0.97  --sat_gr_def                            false
% 0.60/0.97  --sat_epr_types                         true
% 0.60/0.97  --sat_non_cyclic_types                  false
% 0.60/0.97  --sat_finite_models                     false
% 0.60/0.97  --sat_fm_lemmas                         false
% 0.60/0.97  --sat_fm_prep                           false
% 0.60/0.97  --sat_fm_uc_incr                        true
% 0.60/0.97  --sat_out_model                         small
% 0.60/0.97  --sat_out_clauses                       false
% 0.60/0.97  
% 0.60/0.97  ------ QBF Options
% 0.60/0.97  
% 0.60/0.97  --qbf_mode                              false
% 0.60/0.97  --qbf_elim_univ                         false
% 0.60/0.97  --qbf_dom_inst                          none
% 0.60/0.97  --qbf_dom_pre_inst                      false
% 0.60/0.97  --qbf_sk_in                             false
% 0.60/0.97  --qbf_pred_elim                         true
% 0.60/0.97  --qbf_split                             512
% 0.60/0.97  
% 0.60/0.97  ------ BMC1 Options
% 0.60/0.97  
% 0.60/0.97  --bmc1_incremental                      false
% 0.60/0.97  --bmc1_axioms                           reachable_all
% 0.60/0.97  --bmc1_min_bound                        0
% 0.60/0.97  --bmc1_max_bound                        -1
% 0.60/0.97  --bmc1_max_bound_default                -1
% 0.60/0.97  --bmc1_symbol_reachability              true
% 0.60/0.97  --bmc1_property_lemmas                  false
% 0.60/0.97  --bmc1_k_induction                      false
% 0.60/0.97  --bmc1_non_equiv_states                 false
% 0.60/0.97  --bmc1_deadlock                         false
% 0.60/0.97  --bmc1_ucm                              false
% 0.60/0.97  --bmc1_add_unsat_core                   none
% 0.60/0.97  --bmc1_unsat_core_children              false
% 0.60/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 0.60/0.97  --bmc1_out_stat                         full
% 0.60/0.97  --bmc1_ground_init                      false
% 0.60/0.97  --bmc1_pre_inst_next_state              false
% 0.60/0.97  --bmc1_pre_inst_state                   false
% 0.60/0.97  --bmc1_pre_inst_reach_state             false
% 0.60/0.97  --bmc1_out_unsat_core                   false
% 0.60/0.97  --bmc1_aig_witness_out                  false
% 0.60/0.97  --bmc1_verbose                          false
% 0.60/0.97  --bmc1_dump_clauses_tptp                false
% 0.60/0.97  --bmc1_dump_unsat_core_tptp             false
% 0.60/0.97  --bmc1_dump_file                        -
% 0.60/0.97  --bmc1_ucm_expand_uc_limit              128
% 0.60/0.97  --bmc1_ucm_n_expand_iterations          6
% 0.60/0.97  --bmc1_ucm_extend_mode                  1
% 0.60/0.97  --bmc1_ucm_init_mode                    2
% 0.60/0.97  --bmc1_ucm_cone_mode                    none
% 0.60/0.97  --bmc1_ucm_reduced_relation_type        0
% 0.60/0.97  --bmc1_ucm_relax_model                  4
% 0.60/0.97  --bmc1_ucm_full_tr_after_sat            true
% 0.60/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 0.60/0.97  --bmc1_ucm_layered_model                none
% 0.60/0.97  --bmc1_ucm_max_lemma_size               10
% 0.60/0.97  
% 0.60/0.97  ------ AIG Options
% 0.60/0.97  
% 0.60/0.97  --aig_mode                              false
% 0.60/0.97  
% 0.60/0.97  ------ Instantiation Options
% 0.60/0.97  
% 0.60/0.97  --instantiation_flag                    true
% 0.60/0.97  --inst_sos_flag                         false
% 0.60/0.97  --inst_sos_phase                        true
% 0.60/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.60/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.60/0.97  --inst_lit_sel_side                     none
% 0.60/0.97  --inst_solver_per_active                1400
% 0.60/0.97  --inst_solver_calls_frac                1.
% 0.60/0.97  --inst_passive_queue_type               priority_queues
% 0.60/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.60/0.97  --inst_passive_queues_freq              [25;2]
% 0.60/0.97  --inst_dismatching                      true
% 0.60/0.97  --inst_eager_unprocessed_to_passive     true
% 0.60/0.97  --inst_prop_sim_given                   true
% 0.60/0.97  --inst_prop_sim_new                     false
% 0.60/0.97  --inst_subs_new                         false
% 0.60/0.97  --inst_eq_res_simp                      false
% 0.60/0.97  --inst_subs_given                       false
% 0.60/0.97  --inst_orphan_elimination               true
% 0.60/0.97  --inst_learning_loop_flag               true
% 0.60/0.97  --inst_learning_start                   3000
% 0.60/0.97  --inst_learning_factor                  2
% 0.60/0.97  --inst_start_prop_sim_after_learn       3
% 0.60/0.97  --inst_sel_renew                        solver
% 0.60/0.97  --inst_lit_activity_flag                true
% 0.60/0.97  --inst_restr_to_given                   false
% 0.60/0.97  --inst_activity_threshold               500
% 0.60/0.97  --inst_out_proof                        true
% 0.60/0.97  
% 0.60/0.97  ------ Resolution Options
% 0.60/0.97  
% 0.60/0.97  --resolution_flag                       false
% 0.60/0.97  --res_lit_sel                           adaptive
% 0.60/0.97  --res_lit_sel_side                      none
% 0.60/0.97  --res_ordering                          kbo
% 0.60/0.97  --res_to_prop_solver                    active
% 0.60/0.97  --res_prop_simpl_new                    false
% 0.60/0.97  --res_prop_simpl_given                  true
% 0.60/0.97  --res_passive_queue_type                priority_queues
% 0.60/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.60/0.97  --res_passive_queues_freq               [15;5]
% 0.60/0.97  --res_forward_subs                      full
% 0.60/0.97  --res_backward_subs                     full
% 0.60/0.97  --res_forward_subs_resolution           true
% 0.60/0.97  --res_backward_subs_resolution          true
% 0.60/0.97  --res_orphan_elimination                true
% 0.60/0.97  --res_time_limit                        2.
% 0.60/0.97  --res_out_proof                         true
% 0.60/0.97  
% 0.60/0.97  ------ Superposition Options
% 0.60/0.97  
% 0.60/0.97  --superposition_flag                    false
% 0.60/0.97  --sup_passive_queue_type                priority_queues
% 0.60/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.60/0.97  --sup_passive_queues_freq               [8;1;4]
% 0.60/0.97  --demod_completeness_check              fast
% 0.60/0.97  --demod_use_ground                      true
% 0.60/0.97  --sup_to_prop_solver                    passive
% 0.60/0.97  --sup_prop_simpl_new                    true
% 0.60/0.97  --sup_prop_simpl_given                  true
% 0.60/0.97  --sup_fun_splitting                     false
% 0.60/0.97  --sup_smt_interval                      50000
% 0.60/0.97  
% 0.60/0.97  ------ Superposition Simplification Setup
% 0.60/0.97  
% 0.60/0.97  --sup_indices_passive                   []
% 0.60/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.60/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.60/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.60/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 0.60/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.60/0.97  --sup_full_bw                           [BwDemod]
% 0.60/0.97  --sup_immed_triv                        [TrivRules]
% 0.60/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.60/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.60/0.97  --sup_immed_bw_main                     []
% 0.60/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.60/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 0.60/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.60/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.60/0.97  
% 0.60/0.97  ------ Combination Options
% 0.60/0.97  
% 0.60/0.97  --comb_res_mult                         3
% 0.60/0.97  --comb_sup_mult                         2
% 0.60/0.97  --comb_inst_mult                        10
% 0.60/0.97  
% 0.60/0.97  ------ Debug Options
% 0.60/0.97  
% 0.60/0.97  --dbg_backtrace                         false
% 0.60/0.97  --dbg_dump_prop_clauses                 false
% 0.60/0.97  --dbg_dump_prop_clauses_file            -
% 0.60/0.97  --dbg_out_stat                          false
% 0.60/0.97  
% 0.60/0.97  
% 0.60/0.97  
% 0.60/0.97  
% 0.60/0.97  ------ Proving...
% 0.60/0.97  
% 0.60/0.97  
% 0.60/0.97  % SZS status Theorem for theBenchmark.p
% 0.60/0.97  
% 0.60/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 0.60/0.97  
% 0.60/0.97  fof(f10,axiom,(
% 0.60/0.97    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.60/0.97  
% 0.60/0.97  fof(f35,plain,(
% 0.60/0.97    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.60/0.97    inference(cnf_transformation,[],[f10])).
% 0.60/0.97  
% 0.60/0.97  fof(f9,axiom,(
% 0.60/0.97    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.60/0.97  
% 0.60/0.97  fof(f34,plain,(
% 0.60/0.97    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.60/0.97    inference(cnf_transformation,[],[f9])).
% 0.60/0.97  
% 0.60/0.97  fof(f11,axiom,(
% 0.60/0.97    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.60/0.97  
% 0.60/0.97  fof(f16,plain,(
% 0.60/0.97    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.60/0.97    inference(ennf_transformation,[],[f11])).
% 0.60/0.97  
% 0.60/0.97  fof(f17,plain,(
% 0.60/0.97    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.60/0.97    inference(flattening,[],[f16])).
% 0.60/0.97  
% 0.60/0.97  fof(f36,plain,(
% 0.60/0.97    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.60/0.97    inference(cnf_transformation,[],[f17])).
% 0.60/0.97  
% 0.60/0.97  fof(f8,axiom,(
% 0.60/0.97    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.60/0.97  
% 0.60/0.97  fof(f21,plain,(
% 0.60/0.97    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.60/0.97    inference(nnf_transformation,[],[f8])).
% 0.60/0.97  
% 0.60/0.97  fof(f33,plain,(
% 0.60/0.97    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.60/0.97    inference(cnf_transformation,[],[f21])).
% 0.60/0.97  
% 0.60/0.97  fof(f1,axiom,(
% 0.60/0.97    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.60/0.97  
% 0.60/0.97  fof(f25,plain,(
% 0.60/0.97    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.60/0.97    inference(cnf_transformation,[],[f1])).
% 0.60/0.97  
% 0.60/0.97  fof(f2,axiom,(
% 0.60/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.60/0.97  
% 0.60/0.97  fof(f26,plain,(
% 0.60/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.60/0.97    inference(cnf_transformation,[],[f2])).
% 0.60/0.97  
% 0.60/0.97  fof(f3,axiom,(
% 0.60/0.97    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.60/0.97  
% 0.60/0.97  fof(f27,plain,(
% 0.60/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.60/0.97    inference(cnf_transformation,[],[f3])).
% 0.60/0.97  
% 0.60/0.97  fof(f4,axiom,(
% 0.60/0.97    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.60/0.97  
% 0.60/0.97  fof(f28,plain,(
% 0.60/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.60/0.97    inference(cnf_transformation,[],[f4])).
% 0.60/0.97  
% 0.60/0.97  fof(f5,axiom,(
% 0.60/0.97    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.60/0.97  
% 0.60/0.97  fof(f29,plain,(
% 0.60/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.60/0.97    inference(cnf_transformation,[],[f5])).
% 0.60/0.97  
% 0.60/0.97  fof(f6,axiom,(
% 0.60/0.97    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.60/0.97  
% 0.60/0.97  fof(f30,plain,(
% 0.60/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.60/0.97    inference(cnf_transformation,[],[f6])).
% 0.60/0.97  
% 0.60/0.97  fof(f7,axiom,(
% 0.60/0.97    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.60/0.97  
% 0.60/0.97  fof(f31,plain,(
% 0.60/0.97    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.60/0.97    inference(cnf_transformation,[],[f7])).
% 0.60/0.97  
% 0.60/0.97  fof(f41,plain,(
% 0.60/0.97    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.60/0.97    inference(definition_unfolding,[],[f30,f31])).
% 0.60/0.97  
% 0.60/0.97  fof(f42,plain,(
% 0.60/0.97    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.60/0.97    inference(definition_unfolding,[],[f29,f41])).
% 0.60/0.97  
% 0.60/0.97  fof(f43,plain,(
% 0.60/0.97    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.60/0.97    inference(definition_unfolding,[],[f28,f42])).
% 0.60/0.97  
% 0.60/0.97  fof(f44,plain,(
% 0.60/0.97    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.60/0.97    inference(definition_unfolding,[],[f27,f43])).
% 0.60/0.97  
% 0.60/0.97  fof(f45,plain,(
% 0.60/0.97    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.60/0.97    inference(definition_unfolding,[],[f26,f44])).
% 0.60/0.97  
% 0.60/0.97  fof(f46,plain,(
% 0.60/0.97    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.60/0.97    inference(definition_unfolding,[],[f25,f45])).
% 0.60/0.97  
% 0.60/0.97  fof(f47,plain,(
% 0.60/0.97    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.60/0.97    inference(definition_unfolding,[],[f33,f46])).
% 0.60/0.97  
% 0.60/0.97  fof(f12,axiom,(
% 0.60/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.60/0.97  
% 0.60/0.97  fof(f22,plain,(
% 0.60/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.60/0.97    inference(nnf_transformation,[],[f12])).
% 0.60/0.97  
% 0.60/0.97  fof(f38,plain,(
% 0.60/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.60/0.97    inference(cnf_transformation,[],[f22])).
% 0.60/0.97  
% 0.60/0.97  fof(f14,conjecture,(
% 0.60/0.97    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.60/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.60/0.97  
% 0.60/0.97  fof(f15,negated_conjecture,(
% 0.60/0.97    ~! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.60/0.97    inference(negated_conjecture,[],[f14])).
% 0.60/0.97  
% 0.60/0.97  fof(f20,plain,(
% 0.60/0.97    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.60/0.97    inference(ennf_transformation,[],[f15])).
% 0.60/0.97  
% 0.60/0.97  fof(f23,plain,(
% 0.60/0.97    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) => ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.60/0.97    introduced(choice_axiom,[])).
% 0.60/0.97  
% 0.60/0.97  fof(f24,plain,(
% 0.60/0.97    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.60/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f23])).
% 0.60/0.97  
% 0.60/0.97  fof(f40,plain,(
% 0.60/0.97    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.60/0.97    inference(cnf_transformation,[],[f24])).
% 0.60/0.97  
% 0.60/0.97  fof(f49,plain,(
% 0.60/0.97    ~m1_subset_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.60/0.97    inference(definition_unfolding,[],[f40,f46])).
% 0.60/0.97  
% 0.60/0.97  cnf(c_3,plain,
% 0.60/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 0.60/0.97      inference(cnf_transformation,[],[f35]) ).
% 0.60/0.97  
% 0.60/0.97  cnf(c_367,plain,
% 0.60/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
% 0.60/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 0.60/0.97  
% 0.60/0.97  cnf(c_2,plain,
% 0.60/0.97      ( ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
% 0.60/0.97      inference(cnf_transformation,[],[f34]) ).
% 0.60/0.97  
% 0.60/0.97  cnf(c_4,plain,
% 0.60/0.97      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 0.60/0.97      inference(cnf_transformation,[],[f36]) ).
% 0.60/0.97  
% 0.60/0.97  cnf(c_129,plain,
% 0.60/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.60/0.97      | r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 0.60/0.97      inference(resolution,[status(thm)],[c_2,c_4]) ).
% 0.60/0.97  
% 0.60/0.97  cnf(c_361,plain,
% 0.60/0.97      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
% 0.60/0.97      | r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) ),
% 0.60/0.97      inference(instantiation,[status(thm)],[c_129]) ).
% 0.60/0.97  
% 0.60/0.97  cnf(c_0,plain,
% 0.60/0.97      ( ~ r2_hidden(X0,X1)
% 0.60/0.97      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 0.60/0.97      inference(cnf_transformation,[],[f47]) ).
% 0.60/0.97  
% 0.60/0.97  cnf(c_76,plain,
% 0.60/0.97      ( ~ r2_hidden(X0,X1)
% 0.60/0.97      | r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ),
% 0.60/0.97      inference(prop_impl,[status(thm)],[c_0]) ).
% 0.60/0.97  
% 0.60/0.97  cnf(c_5,plain,
% 0.60/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 0.60/0.97      inference(cnf_transformation,[],[f38]) ).
% 0.60/0.97  
% 0.60/0.97  cnf(c_80,plain,
% 0.60/0.97      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 0.60/0.97      inference(prop_impl,[status(thm)],[c_5]) ).
% 0.60/0.97  
% 0.60/0.97  cnf(c_81,plain,
% 0.60/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 0.60/0.97      inference(renaming,[status(thm)],[c_80]) ).
% 0.60/0.97  
% 0.60/0.97  cnf(c_145,plain,
% 0.60/0.97      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
% 0.60/0.97      | ~ r2_hidden(X0,X1) ),
% 0.60/0.97      inference(resolution,[status(thm)],[c_76,c_81]) ).
% 0.60/0.97  
% 0.60/0.97  cnf(c_244,plain,
% 0.60/0.97      ( ~ r2_hidden(X0,X1)
% 0.60/0.97      | m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1)) ),
% 0.60/0.97      inference(prop_impl,[status(thm)],[c_145]) ).
% 0.60/0.97  
% 0.60/0.97  cnf(c_245,plain,
% 0.60/0.97      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(X1))
% 0.60/0.97      | ~ r2_hidden(X0,X1) ),
% 0.60/0.97      inference(renaming,[status(thm)],[c_244]) ).
% 0.60/0.97  
% 0.60/0.97  cnf(c_348,plain,
% 0.60/0.97      ( m1_subset_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
% 0.60/0.97      | ~ r2_hidden(X0,k1_zfmisc_1(X1)) ),
% 0.60/0.97      inference(instantiation,[status(thm)],[c_245]) ).
% 0.60/0.97  
% 0.60/0.97  cnf(c_353,plain,
% 0.60/0.97      ( m1_subset_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
% 0.60/0.97      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) ),
% 0.60/0.97      inference(instantiation,[status(thm)],[c_348]) ).
% 0.60/0.97  
% 0.60/0.97  cnf(c_8,negated_conjecture,
% 0.60/0.97      ( ~ m1_subset_1(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
% 0.60/0.97      inference(cnf_transformation,[],[f49]) ).
% 0.60/0.97  
% 0.60/0.97  cnf(contradiction,plain,
% 0.60/0.97      ( $false ),
% 0.60/0.97      inference(minisat,[status(thm)],[c_367,c_361,c_353,c_8]) ).
% 0.60/0.97  
% 0.60/0.97  
% 0.60/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 0.60/0.97  
% 0.60/0.97  ------                               Statistics
% 0.60/0.97  
% 0.60/0.97  ------ General
% 0.60/0.97  
% 0.60/0.97  abstr_ref_over_cycles:                  0
% 0.60/0.97  abstr_ref_under_cycles:                 0
% 0.60/0.97  gc_basic_clause_elim:                   0
% 0.60/0.97  forced_gc_time:                         0
% 0.60/0.97  parsing_time:                           0.01
% 0.60/0.97  unif_index_cands_time:                  0.
% 0.60/0.97  unif_index_add_time:                    0.
% 0.60/0.97  orderings_time:                         0.
% 0.60/0.97  out_proof_time:                         0.007
% 0.60/0.97  total_time:                             0.043
% 0.60/0.97  num_of_symbols:                         36
% 0.60/0.97  num_of_terms:                           161
% 0.60/0.97  
% 0.60/0.97  ------ Preprocessing
% 0.60/0.97  
% 0.60/0.97  num_of_splits:                          0
% 0.60/0.97  num_of_split_atoms:                     0
% 0.60/0.97  num_of_reused_defs:                     0
% 0.60/0.97  num_eq_ax_congr_red:                    0
% 0.60/0.97  num_of_sem_filtered_clauses:            0
% 0.60/0.97  num_of_subtypes:                        1
% 0.60/0.97  monotx_restored_types:                  0
% 0.60/0.97  sat_num_of_epr_types:                   0
% 0.60/0.97  sat_num_of_non_cyclic_types:            0
% 0.60/0.97  sat_guarded_non_collapsed_types:        0
% 0.60/0.97  num_pure_diseq_elim:                    0
% 0.60/0.97  simp_replaced_by:                       0
% 0.60/0.97  res_preprocessed:                       15
% 0.60/0.97  prep_upred:                             0
% 0.60/0.97  prep_unflattend:                        0
% 0.60/0.97  smt_new_axioms:                         0
% 0.60/0.97  pred_elim_cands:                        2
% 0.60/0.97  pred_elim:                              2
% 0.60/0.97  pred_elim_cl:                           3
% 0.60/0.97  pred_elim_cycles:                       4
% 0.60/0.97  merged_defs:                            6
% 0.60/0.97  merged_defs_ncl:                        0
% 0.60/0.97  bin_hyper_res:                          6
% 0.60/0.97  prep_cycles:                            2
% 0.60/0.97  pred_elim_time:                         0.002
% 0.60/0.97  splitting_time:                         0.
% 0.60/0.97  sem_filter_time:                        0.
% 0.60/0.97  monotx_time:                            0.
% 0.60/0.97  subtype_inf_time:                       0.
% 0.60/0.97  
% 0.60/0.97  ------ Problem properties
% 0.60/0.97  
% 0.60/0.97  clauses:                                6
% 0.60/0.97  conjectures:                            1
% 0.60/0.97  epr:                                    0
% 0.60/0.97  horn:                                   6
% 0.60/0.97  ground:                                 1
% 0.60/0.97  unary:                                  2
% 0.60/0.97  binary:                                 3
% 0.60/0.97  lits:                                   11
% 0.60/0.97  lits_eq:                                0
% 0.60/0.97  fd_pure:                                0
% 0.60/0.97  fd_pseudo:                              0
% 0.60/0.97  fd_cond:                                0
% 0.60/0.97  fd_pseudo_cond:                         0
% 0.60/0.97  ac_symbols:                             0
% 0.60/0.97  
% 0.60/0.97  ------ Propositional Solver
% 0.60/0.97  
% 0.60/0.97  prop_solver_calls:                      14
% 0.60/0.97  prop_fast_solver_calls:                 78
% 0.60/0.97  smt_solver_calls:                       0
% 0.60/0.97  smt_fast_solver_calls:                  0
% 0.60/0.97  prop_num_of_clauses:                    74
% 0.60/0.97  prop_preprocess_simplified:             562
% 0.60/0.97  prop_fo_subsumed:                       0
% 0.60/0.97  prop_solver_time:                       0.
% 0.60/0.97  smt_solver_time:                        0.
% 0.60/0.97  smt_fast_solver_time:                   0.
% 0.60/0.97  prop_fast_solver_time:                  0.
% 0.60/0.97  prop_unsat_core_time:                   0.
% 0.60/0.97  
% 0.60/0.97  ------ QBF
% 0.60/0.97  
% 0.60/0.97  qbf_q_res:                              0
% 0.60/0.97  qbf_num_tautologies:                    0
% 0.60/0.97  qbf_prep_cycles:                        0
% 0.60/0.97  
% 0.60/0.97  ------ BMC1
% 0.60/0.97  
% 0.60/0.97  bmc1_current_bound:                     -1
% 0.60/0.97  bmc1_last_solved_bound:                 -1
% 0.60/0.97  bmc1_unsat_core_size:                   -1
% 0.60/0.97  bmc1_unsat_core_parents_size:           -1
% 0.60/0.97  bmc1_merge_next_fun:                    0
% 0.60/0.97  bmc1_unsat_core_clauses_time:           0.
% 0.60/0.97  
% 0.60/0.97  ------ Instantiation
% 0.60/0.97  
% 0.60/0.97  inst_num_of_clauses:                    11
% 0.60/0.97  inst_num_in_passive:                    0
% 0.60/0.97  inst_num_in_active:                     10
% 0.60/0.97  inst_num_in_unprocessed:                0
% 0.60/0.97  inst_num_of_loops:                      14
% 0.60/0.97  inst_num_of_learning_restarts:          0
% 0.60/0.97  inst_num_moves_active_passive:          0
% 0.60/0.97  inst_lit_activity:                      0
% 0.60/0.97  inst_lit_activity_moves:                0
% 0.60/0.97  inst_num_tautologies:                   0
% 0.60/0.97  inst_num_prop_implied:                  0
% 0.60/0.97  inst_num_existing_simplified:           0
% 0.60/0.97  inst_num_eq_res_simplified:             0
% 0.60/0.97  inst_num_child_elim:                    0
% 0.60/0.97  inst_num_of_dismatching_blockings:      0
% 0.60/0.97  inst_num_of_non_proper_insts:           8
% 0.60/0.97  inst_num_of_duplicates:                 0
% 0.60/0.97  inst_inst_num_from_inst_to_res:         0
% 0.60/0.97  inst_dismatching_checking_time:         0.
% 0.60/0.97  
% 0.60/0.97  ------ Resolution
% 0.60/0.97  
% 0.60/0.97  res_num_of_clauses:                     0
% 0.60/0.97  res_num_in_passive:                     0
% 0.60/0.97  res_num_in_active:                      0
% 0.60/0.97  res_num_of_loops:                       17
% 0.60/0.97  res_forward_subset_subsumed:            1
% 0.60/0.97  res_backward_subset_subsumed:           0
% 0.60/0.97  res_forward_subsumed:                   0
% 0.60/0.97  res_backward_subsumed:                  0
% 0.60/0.97  res_forward_subsumption_resolution:     0
% 0.60/0.97  res_backward_subsumption_resolution:    0
% 0.60/0.97  res_clause_to_clause_subsumption:       4
% 0.60/0.97  res_orphan_elimination:                 0
% 0.60/0.97  res_tautology_del:                      16
% 0.60/0.97  res_num_eq_res_simplified:              0
% 0.60/0.97  res_num_sel_changes:                    0
% 0.60/0.97  res_moves_from_active_to_pass:          0
% 0.60/0.97  
% 0.60/0.97  ------ Superposition
% 0.60/0.97  
% 0.60/0.97  sup_time_total:                         0.
% 0.60/0.97  sup_time_generating:                    0.
% 0.60/0.97  sup_time_sim_full:                      0.
% 0.60/0.97  sup_time_sim_immed:                     0.
% 0.60/0.97  
% 0.60/0.97  sup_num_of_clauses:                     0
% 0.60/0.97  sup_num_in_active:                      0
% 0.60/0.97  sup_num_in_passive:                     0
% 0.60/0.97  sup_num_of_loops:                       0
% 0.60/0.97  sup_fw_superposition:                   0
% 0.60/0.97  sup_bw_superposition:                   0
% 0.60/0.97  sup_immediate_simplified:               0
% 0.60/0.97  sup_given_eliminated:                   0
% 0.60/0.97  comparisons_done:                       0
% 0.60/0.97  comparisons_avoided:                    0
% 0.60/0.97  
% 0.60/0.97  ------ Simplifications
% 0.60/0.97  
% 0.60/0.97  
% 0.60/0.97  sim_fw_subset_subsumed:                 0
% 0.60/0.97  sim_bw_subset_subsumed:                 0
% 0.60/0.97  sim_fw_subsumed:                        0
% 0.60/0.97  sim_bw_subsumed:                        0
% 0.60/0.97  sim_fw_subsumption_res:                 0
% 0.60/0.97  sim_bw_subsumption_res:                 0
% 0.60/0.97  sim_tautology_del:                      0
% 0.60/0.97  sim_eq_tautology_del:                   0
% 0.60/0.97  sim_eq_res_simp:                        0
% 0.60/0.97  sim_fw_demodulated:                     0
% 0.60/0.97  sim_bw_demodulated:                     0
% 0.60/0.97  sim_light_normalised:                   0
% 0.60/0.97  sim_joinable_taut:                      0
% 0.60/0.97  sim_joinable_simp:                      0
% 0.60/0.97  sim_ac_normalised:                      0
% 0.60/0.97  sim_smt_subsumption:                    0
% 0.60/0.97  
%------------------------------------------------------------------------------
