%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:22:48 EST 2020

% Result     : Theorem 51.03s
% Output     : CNFRefutation 51.03s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 141 expanded)
%              Number of clauses        :   38 (  67 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :   73 ( 154 expanded)
%              Number of equality atoms :   65 ( 139 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f16,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f28,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_8,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_86,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_8,c_7])).

cnf(c_87,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_86,c_7])).

cnf(c_178,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(superposition,[status(thm)],[c_7,c_87])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_80,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_6,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_47,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X3
    | k2_xboole_0(X3,X1) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_6])).

cnf(c_48,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_47])).

cnf(c_152,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_80,c_48])).

cnf(c_190,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_178,c_152])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_5,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_102,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2,c_5])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_113,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_102,c_4])).

cnf(c_120,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_48,c_113])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_203,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_120,c_1])).

cnf(c_657,plain,
    ( k3_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_203,c_5])).

cnf(c_240463,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_190,c_657])).

cnf(c_115,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_113])).

cnf(c_241988,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_240463,c_115])).

cnf(c_246006,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_241988,c_8])).

cnf(c_66,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_4])).

cnf(c_9,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_147,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    inference(superposition,[status(thm)],[c_7,c_80])).

cnf(c_156,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_147,c_80])).

cnf(c_448,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_9,c_156])).

cnf(c_470,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(light_normalisation,[status(thm)],[c_448,c_9])).

cnf(c_29132,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(X2,X1))) ),
    inference(superposition,[status(thm)],[c_66,c_470])).

cnf(c_29355,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_29132,c_9,c_66])).

cnf(c_246302,plain,
    ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_246006,c_29355])).

cnf(c_10,negated_conjecture,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_249265,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_246302,c_10])).

cnf(c_249266,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_249265])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 51.03/7.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.03/7.00  
% 51.03/7.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.03/7.00  
% 51.03/7.00  ------  iProver source info
% 51.03/7.00  
% 51.03/7.00  git: date: 2020-06-30 10:37:57 +0100
% 51.03/7.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.03/7.00  git: non_committed_changes: false
% 51.03/7.00  git: last_make_outside_of_git: false
% 51.03/7.00  
% 51.03/7.00  ------ 
% 51.03/7.00  
% 51.03/7.00  ------ Input Options
% 51.03/7.00  
% 51.03/7.00  --out_options                           all
% 51.03/7.00  --tptp_safe_out                         true
% 51.03/7.00  --problem_path                          ""
% 51.03/7.00  --include_path                          ""
% 51.03/7.00  --clausifier                            res/vclausify_rel
% 51.03/7.00  --clausifier_options                    --mode clausify
% 51.03/7.00  --stdin                                 false
% 51.03/7.00  --stats_out                             all
% 51.03/7.00  
% 51.03/7.00  ------ General Options
% 51.03/7.00  
% 51.03/7.00  --fof                                   false
% 51.03/7.00  --time_out_real                         305.
% 51.03/7.00  --time_out_virtual                      -1.
% 51.03/7.00  --symbol_type_check                     false
% 51.03/7.00  --clausify_out                          false
% 51.03/7.00  --sig_cnt_out                           false
% 51.03/7.00  --trig_cnt_out                          false
% 51.03/7.00  --trig_cnt_out_tolerance                1.
% 51.03/7.00  --trig_cnt_out_sk_spl                   false
% 51.03/7.00  --abstr_cl_out                          false
% 51.03/7.00  
% 51.03/7.00  ------ Global Options
% 51.03/7.00  
% 51.03/7.00  --schedule                              default
% 51.03/7.00  --add_important_lit                     false
% 51.03/7.00  --prop_solver_per_cl                    1000
% 51.03/7.00  --min_unsat_core                        false
% 51.03/7.00  --soft_assumptions                      false
% 51.03/7.00  --soft_lemma_size                       3
% 51.03/7.00  --prop_impl_unit_size                   0
% 51.03/7.00  --prop_impl_unit                        []
% 51.03/7.00  --share_sel_clauses                     true
% 51.03/7.00  --reset_solvers                         false
% 51.03/7.00  --bc_imp_inh                            [conj_cone]
% 51.03/7.00  --conj_cone_tolerance                   3.
% 51.03/7.00  --extra_neg_conj                        none
% 51.03/7.00  --large_theory_mode                     true
% 51.03/7.00  --prolific_symb_bound                   200
% 51.03/7.00  --lt_threshold                          2000
% 51.03/7.00  --clause_weak_htbl                      true
% 51.03/7.00  --gc_record_bc_elim                     false
% 51.03/7.00  
% 51.03/7.00  ------ Preprocessing Options
% 51.03/7.00  
% 51.03/7.00  --preprocessing_flag                    true
% 51.03/7.00  --time_out_prep_mult                    0.1
% 51.03/7.00  --splitting_mode                        input
% 51.03/7.00  --splitting_grd                         true
% 51.03/7.00  --splitting_cvd                         false
% 51.03/7.00  --splitting_cvd_svl                     false
% 51.03/7.00  --splitting_nvd                         32
% 51.03/7.00  --sub_typing                            true
% 51.03/7.00  --prep_gs_sim                           true
% 51.03/7.00  --prep_unflatten                        true
% 51.03/7.00  --prep_res_sim                          true
% 51.03/7.00  --prep_upred                            true
% 51.03/7.00  --prep_sem_filter                       exhaustive
% 51.03/7.00  --prep_sem_filter_out                   false
% 51.03/7.00  --pred_elim                             true
% 51.03/7.00  --res_sim_input                         true
% 51.03/7.00  --eq_ax_congr_red                       true
% 51.03/7.00  --pure_diseq_elim                       true
% 51.03/7.00  --brand_transform                       false
% 51.03/7.00  --non_eq_to_eq                          false
% 51.03/7.00  --prep_def_merge                        true
% 51.03/7.00  --prep_def_merge_prop_impl              false
% 51.03/7.00  --prep_def_merge_mbd                    true
% 51.03/7.00  --prep_def_merge_tr_red                 false
% 51.03/7.00  --prep_def_merge_tr_cl                  false
% 51.03/7.00  --smt_preprocessing                     true
% 51.03/7.00  --smt_ac_axioms                         fast
% 51.03/7.00  --preprocessed_out                      false
% 51.03/7.00  --preprocessed_stats                    false
% 51.03/7.00  
% 51.03/7.00  ------ Abstraction refinement Options
% 51.03/7.00  
% 51.03/7.00  --abstr_ref                             []
% 51.03/7.00  --abstr_ref_prep                        false
% 51.03/7.00  --abstr_ref_until_sat                   false
% 51.03/7.00  --abstr_ref_sig_restrict                funpre
% 51.03/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 51.03/7.00  --abstr_ref_under                       []
% 51.03/7.00  
% 51.03/7.00  ------ SAT Options
% 51.03/7.00  
% 51.03/7.00  --sat_mode                              false
% 51.03/7.00  --sat_fm_restart_options                ""
% 51.03/7.00  --sat_gr_def                            false
% 51.03/7.00  --sat_epr_types                         true
% 51.03/7.00  --sat_non_cyclic_types                  false
% 51.03/7.00  --sat_finite_models                     false
% 51.03/7.00  --sat_fm_lemmas                         false
% 51.03/7.00  --sat_fm_prep                           false
% 51.03/7.00  --sat_fm_uc_incr                        true
% 51.03/7.00  --sat_out_model                         small
% 51.03/7.00  --sat_out_clauses                       false
% 51.03/7.00  
% 51.03/7.00  ------ QBF Options
% 51.03/7.00  
% 51.03/7.00  --qbf_mode                              false
% 51.03/7.00  --qbf_elim_univ                         false
% 51.03/7.00  --qbf_dom_inst                          none
% 51.03/7.00  --qbf_dom_pre_inst                      false
% 51.03/7.00  --qbf_sk_in                             false
% 51.03/7.00  --qbf_pred_elim                         true
% 51.03/7.00  --qbf_split                             512
% 51.03/7.00  
% 51.03/7.00  ------ BMC1 Options
% 51.03/7.00  
% 51.03/7.00  --bmc1_incremental                      false
% 51.03/7.00  --bmc1_axioms                           reachable_all
% 51.03/7.00  --bmc1_min_bound                        0
% 51.03/7.00  --bmc1_max_bound                        -1
% 51.03/7.00  --bmc1_max_bound_default                -1
% 51.03/7.00  --bmc1_symbol_reachability              true
% 51.03/7.00  --bmc1_property_lemmas                  false
% 51.03/7.00  --bmc1_k_induction                      false
% 51.03/7.00  --bmc1_non_equiv_states                 false
% 51.03/7.00  --bmc1_deadlock                         false
% 51.03/7.00  --bmc1_ucm                              false
% 51.03/7.00  --bmc1_add_unsat_core                   none
% 51.03/7.00  --bmc1_unsat_core_children              false
% 51.03/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 51.03/7.00  --bmc1_out_stat                         full
% 51.03/7.00  --bmc1_ground_init                      false
% 51.03/7.00  --bmc1_pre_inst_next_state              false
% 51.03/7.00  --bmc1_pre_inst_state                   false
% 51.03/7.00  --bmc1_pre_inst_reach_state             false
% 51.03/7.00  --bmc1_out_unsat_core                   false
% 51.03/7.00  --bmc1_aig_witness_out                  false
% 51.03/7.00  --bmc1_verbose                          false
% 51.03/7.00  --bmc1_dump_clauses_tptp                false
% 51.03/7.00  --bmc1_dump_unsat_core_tptp             false
% 51.03/7.00  --bmc1_dump_file                        -
% 51.03/7.00  --bmc1_ucm_expand_uc_limit              128
% 51.03/7.00  --bmc1_ucm_n_expand_iterations          6
% 51.03/7.00  --bmc1_ucm_extend_mode                  1
% 51.03/7.00  --bmc1_ucm_init_mode                    2
% 51.03/7.00  --bmc1_ucm_cone_mode                    none
% 51.03/7.00  --bmc1_ucm_reduced_relation_type        0
% 51.03/7.00  --bmc1_ucm_relax_model                  4
% 51.03/7.00  --bmc1_ucm_full_tr_after_sat            true
% 51.03/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 51.03/7.00  --bmc1_ucm_layered_model                none
% 51.03/7.00  --bmc1_ucm_max_lemma_size               10
% 51.03/7.00  
% 51.03/7.00  ------ AIG Options
% 51.03/7.00  
% 51.03/7.00  --aig_mode                              false
% 51.03/7.00  
% 51.03/7.00  ------ Instantiation Options
% 51.03/7.00  
% 51.03/7.00  --instantiation_flag                    true
% 51.03/7.00  --inst_sos_flag                         false
% 51.03/7.00  --inst_sos_phase                        true
% 51.03/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.03/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.03/7.00  --inst_lit_sel_side                     num_symb
% 51.03/7.00  --inst_solver_per_active                1400
% 51.03/7.00  --inst_solver_calls_frac                1.
% 51.03/7.00  --inst_passive_queue_type               priority_queues
% 51.03/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.03/7.00  --inst_passive_queues_freq              [25;2]
% 51.03/7.00  --inst_dismatching                      true
% 51.03/7.00  --inst_eager_unprocessed_to_passive     true
% 51.03/7.00  --inst_prop_sim_given                   true
% 51.03/7.00  --inst_prop_sim_new                     false
% 51.03/7.00  --inst_subs_new                         false
% 51.03/7.00  --inst_eq_res_simp                      false
% 51.03/7.00  --inst_subs_given                       false
% 51.03/7.00  --inst_orphan_elimination               true
% 51.03/7.00  --inst_learning_loop_flag               true
% 51.03/7.00  --inst_learning_start                   3000
% 51.03/7.00  --inst_learning_factor                  2
% 51.03/7.00  --inst_start_prop_sim_after_learn       3
% 51.03/7.00  --inst_sel_renew                        solver
% 51.03/7.00  --inst_lit_activity_flag                true
% 51.03/7.00  --inst_restr_to_given                   false
% 51.03/7.00  --inst_activity_threshold               500
% 51.03/7.00  --inst_out_proof                        true
% 51.03/7.00  
% 51.03/7.00  ------ Resolution Options
% 51.03/7.00  
% 51.03/7.00  --resolution_flag                       true
% 51.03/7.00  --res_lit_sel                           adaptive
% 51.03/7.00  --res_lit_sel_side                      none
% 51.03/7.00  --res_ordering                          kbo
% 51.03/7.00  --res_to_prop_solver                    active
% 51.03/7.00  --res_prop_simpl_new                    false
% 51.03/7.00  --res_prop_simpl_given                  true
% 51.03/7.00  --res_passive_queue_type                priority_queues
% 51.03/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.03/7.00  --res_passive_queues_freq               [15;5]
% 51.03/7.00  --res_forward_subs                      full
% 51.03/7.00  --res_backward_subs                     full
% 51.03/7.00  --res_forward_subs_resolution           true
% 51.03/7.00  --res_backward_subs_resolution          true
% 51.03/7.00  --res_orphan_elimination                true
% 51.03/7.00  --res_time_limit                        2.
% 51.03/7.00  --res_out_proof                         true
% 51.03/7.00  
% 51.03/7.00  ------ Superposition Options
% 51.03/7.00  
% 51.03/7.00  --superposition_flag                    true
% 51.03/7.00  --sup_passive_queue_type                priority_queues
% 51.03/7.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.03/7.00  --sup_passive_queues_freq               [8;1;4]
% 51.03/7.00  --demod_completeness_check              fast
% 51.03/7.00  --demod_use_ground                      true
% 51.03/7.00  --sup_to_prop_solver                    passive
% 51.03/7.00  --sup_prop_simpl_new                    true
% 51.03/7.00  --sup_prop_simpl_given                  true
% 51.03/7.00  --sup_fun_splitting                     false
% 51.03/7.00  --sup_smt_interval                      50000
% 51.03/7.00  
% 51.03/7.00  ------ Superposition Simplification Setup
% 51.03/7.00  
% 51.03/7.00  --sup_indices_passive                   []
% 51.03/7.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.03/7.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.03/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.03/7.00  --sup_full_triv                         [TrivRules;PropSubs]
% 51.03/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.03/7.00  --sup_full_bw                           [BwDemod]
% 51.03/7.00  --sup_immed_triv                        [TrivRules]
% 51.03/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.03/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.03/7.00  --sup_immed_bw_main                     []
% 51.03/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.03/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 51.03/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 51.03/7.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 51.03/7.00  
% 51.03/7.00  ------ Combination Options
% 51.03/7.00  
% 51.03/7.00  --comb_res_mult                         3
% 51.03/7.00  --comb_sup_mult                         2
% 51.03/7.00  --comb_inst_mult                        10
% 51.03/7.00  
% 51.03/7.00  ------ Debug Options
% 51.03/7.00  
% 51.03/7.00  --dbg_backtrace                         false
% 51.03/7.00  --dbg_dump_prop_clauses                 false
% 51.03/7.00  --dbg_dump_prop_clauses_file            -
% 51.03/7.00  --dbg_out_stat                          false
% 51.03/7.00  ------ Parsing...
% 51.03/7.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.03/7.00  
% 51.03/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 51.03/7.00  
% 51.03/7.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.03/7.00  
% 51.03/7.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 51.03/7.00  ------ Proving...
% 51.03/7.00  ------ Problem Properties 
% 51.03/7.00  
% 51.03/7.00  
% 51.03/7.00  clauses                                 10
% 51.03/7.00  conjectures                             1
% 51.03/7.00  EPR                                     0
% 51.03/7.00  Horn                                    10
% 51.03/7.00  unary                                   10
% 51.03/7.00  binary                                  0
% 51.03/7.00  lits                                    10
% 51.03/7.00  lits eq                                 10
% 51.03/7.00  fd_pure                                 0
% 51.03/7.00  fd_pseudo                               0
% 51.03/7.00  fd_cond                                 0
% 51.03/7.00  fd_pseudo_cond                          0
% 51.03/7.00  AC symbols                              0
% 51.03/7.00  
% 51.03/7.00  ------ Schedule UEQ
% 51.03/7.00  
% 51.03/7.00  ------ pure equality problem: resolution off 
% 51.03/7.00  
% 51.03/7.00  ------ Option_UEQ Time Limit: Unbounded
% 51.03/7.00  
% 51.03/7.00  
% 51.03/7.00  ------ 
% 51.03/7.00  Current options:
% 51.03/7.00  ------ 
% 51.03/7.00  
% 51.03/7.00  ------ Input Options
% 51.03/7.00  
% 51.03/7.00  --out_options                           all
% 51.03/7.00  --tptp_safe_out                         true
% 51.03/7.00  --problem_path                          ""
% 51.03/7.00  --include_path                          ""
% 51.03/7.00  --clausifier                            res/vclausify_rel
% 51.03/7.00  --clausifier_options                    --mode clausify
% 51.03/7.00  --stdin                                 false
% 51.03/7.00  --stats_out                             all
% 51.03/7.00  
% 51.03/7.00  ------ General Options
% 51.03/7.00  
% 51.03/7.00  --fof                                   false
% 51.03/7.00  --time_out_real                         305.
% 51.03/7.00  --time_out_virtual                      -1.
% 51.03/7.00  --symbol_type_check                     false
% 51.03/7.00  --clausify_out                          false
% 51.03/7.00  --sig_cnt_out                           false
% 51.03/7.00  --trig_cnt_out                          false
% 51.03/7.00  --trig_cnt_out_tolerance                1.
% 51.03/7.00  --trig_cnt_out_sk_spl                   false
% 51.03/7.00  --abstr_cl_out                          false
% 51.03/7.00  
% 51.03/7.00  ------ Global Options
% 51.03/7.00  
% 51.03/7.00  --schedule                              default
% 51.03/7.00  --add_important_lit                     false
% 51.03/7.00  --prop_solver_per_cl                    1000
% 51.03/7.00  --min_unsat_core                        false
% 51.03/7.00  --soft_assumptions                      false
% 51.03/7.00  --soft_lemma_size                       3
% 51.03/7.00  --prop_impl_unit_size                   0
% 51.03/7.00  --prop_impl_unit                        []
% 51.03/7.00  --share_sel_clauses                     true
% 51.03/7.00  --reset_solvers                         false
% 51.03/7.00  --bc_imp_inh                            [conj_cone]
% 51.03/7.00  --conj_cone_tolerance                   3.
% 51.03/7.00  --extra_neg_conj                        none
% 51.03/7.00  --large_theory_mode                     true
% 51.03/7.00  --prolific_symb_bound                   200
% 51.03/7.00  --lt_threshold                          2000
% 51.03/7.00  --clause_weak_htbl                      true
% 51.03/7.00  --gc_record_bc_elim                     false
% 51.03/7.00  
% 51.03/7.00  ------ Preprocessing Options
% 51.03/7.00  
% 51.03/7.00  --preprocessing_flag                    true
% 51.03/7.00  --time_out_prep_mult                    0.1
% 51.03/7.00  --splitting_mode                        input
% 51.03/7.00  --splitting_grd                         true
% 51.03/7.00  --splitting_cvd                         false
% 51.03/7.00  --splitting_cvd_svl                     false
% 51.03/7.00  --splitting_nvd                         32
% 51.03/7.00  --sub_typing                            true
% 51.03/7.00  --prep_gs_sim                           true
% 51.03/7.00  --prep_unflatten                        true
% 51.03/7.00  --prep_res_sim                          true
% 51.03/7.00  --prep_upred                            true
% 51.03/7.00  --prep_sem_filter                       exhaustive
% 51.03/7.00  --prep_sem_filter_out                   false
% 51.03/7.00  --pred_elim                             true
% 51.03/7.00  --res_sim_input                         true
% 51.03/7.00  --eq_ax_congr_red                       true
% 51.03/7.00  --pure_diseq_elim                       true
% 51.03/7.00  --brand_transform                       false
% 51.03/7.00  --non_eq_to_eq                          false
% 51.03/7.00  --prep_def_merge                        true
% 51.03/7.00  --prep_def_merge_prop_impl              false
% 51.03/7.00  --prep_def_merge_mbd                    true
% 51.03/7.00  --prep_def_merge_tr_red                 false
% 51.03/7.00  --prep_def_merge_tr_cl                  false
% 51.03/7.00  --smt_preprocessing                     true
% 51.03/7.00  --smt_ac_axioms                         fast
% 51.03/7.00  --preprocessed_out                      false
% 51.03/7.00  --preprocessed_stats                    false
% 51.03/7.00  
% 51.03/7.00  ------ Abstraction refinement Options
% 51.03/7.00  
% 51.03/7.00  --abstr_ref                             []
% 51.03/7.00  --abstr_ref_prep                        false
% 51.03/7.00  --abstr_ref_until_sat                   false
% 51.03/7.00  --abstr_ref_sig_restrict                funpre
% 51.03/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 51.03/7.00  --abstr_ref_under                       []
% 51.03/7.00  
% 51.03/7.00  ------ SAT Options
% 51.03/7.00  
% 51.03/7.00  --sat_mode                              false
% 51.03/7.00  --sat_fm_restart_options                ""
% 51.03/7.00  --sat_gr_def                            false
% 51.03/7.00  --sat_epr_types                         true
% 51.03/7.00  --sat_non_cyclic_types                  false
% 51.03/7.00  --sat_finite_models                     false
% 51.03/7.00  --sat_fm_lemmas                         false
% 51.03/7.00  --sat_fm_prep                           false
% 51.03/7.00  --sat_fm_uc_incr                        true
% 51.03/7.00  --sat_out_model                         small
% 51.03/7.00  --sat_out_clauses                       false
% 51.03/7.00  
% 51.03/7.00  ------ QBF Options
% 51.03/7.00  
% 51.03/7.00  --qbf_mode                              false
% 51.03/7.00  --qbf_elim_univ                         false
% 51.03/7.00  --qbf_dom_inst                          none
% 51.03/7.00  --qbf_dom_pre_inst                      false
% 51.03/7.00  --qbf_sk_in                             false
% 51.03/7.00  --qbf_pred_elim                         true
% 51.03/7.00  --qbf_split                             512
% 51.03/7.00  
% 51.03/7.00  ------ BMC1 Options
% 51.03/7.00  
% 51.03/7.00  --bmc1_incremental                      false
% 51.03/7.00  --bmc1_axioms                           reachable_all
% 51.03/7.00  --bmc1_min_bound                        0
% 51.03/7.00  --bmc1_max_bound                        -1
% 51.03/7.00  --bmc1_max_bound_default                -1
% 51.03/7.00  --bmc1_symbol_reachability              true
% 51.03/7.00  --bmc1_property_lemmas                  false
% 51.03/7.00  --bmc1_k_induction                      false
% 51.03/7.00  --bmc1_non_equiv_states                 false
% 51.03/7.00  --bmc1_deadlock                         false
% 51.03/7.00  --bmc1_ucm                              false
% 51.03/7.00  --bmc1_add_unsat_core                   none
% 51.03/7.00  --bmc1_unsat_core_children              false
% 51.03/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 51.03/7.00  --bmc1_out_stat                         full
% 51.03/7.00  --bmc1_ground_init                      false
% 51.03/7.00  --bmc1_pre_inst_next_state              false
% 51.03/7.00  --bmc1_pre_inst_state                   false
% 51.03/7.00  --bmc1_pre_inst_reach_state             false
% 51.03/7.00  --bmc1_out_unsat_core                   false
% 51.03/7.00  --bmc1_aig_witness_out                  false
% 51.03/7.00  --bmc1_verbose                          false
% 51.03/7.00  --bmc1_dump_clauses_tptp                false
% 51.03/7.00  --bmc1_dump_unsat_core_tptp             false
% 51.03/7.00  --bmc1_dump_file                        -
% 51.03/7.00  --bmc1_ucm_expand_uc_limit              128
% 51.03/7.00  --bmc1_ucm_n_expand_iterations          6
% 51.03/7.00  --bmc1_ucm_extend_mode                  1
% 51.03/7.00  --bmc1_ucm_init_mode                    2
% 51.03/7.00  --bmc1_ucm_cone_mode                    none
% 51.03/7.00  --bmc1_ucm_reduced_relation_type        0
% 51.03/7.00  --bmc1_ucm_relax_model                  4
% 51.03/7.00  --bmc1_ucm_full_tr_after_sat            true
% 51.03/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 51.03/7.00  --bmc1_ucm_layered_model                none
% 51.03/7.00  --bmc1_ucm_max_lemma_size               10
% 51.03/7.00  
% 51.03/7.00  ------ AIG Options
% 51.03/7.00  
% 51.03/7.00  --aig_mode                              false
% 51.03/7.00  
% 51.03/7.00  ------ Instantiation Options
% 51.03/7.00  
% 51.03/7.00  --instantiation_flag                    false
% 51.03/7.00  --inst_sos_flag                         false
% 51.03/7.00  --inst_sos_phase                        true
% 51.03/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.03/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.03/7.00  --inst_lit_sel_side                     num_symb
% 51.03/7.00  --inst_solver_per_active                1400
% 51.03/7.00  --inst_solver_calls_frac                1.
% 51.03/7.00  --inst_passive_queue_type               priority_queues
% 51.03/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.03/7.00  --inst_passive_queues_freq              [25;2]
% 51.03/7.00  --inst_dismatching                      true
% 51.03/7.00  --inst_eager_unprocessed_to_passive     true
% 51.03/7.00  --inst_prop_sim_given                   true
% 51.03/7.00  --inst_prop_sim_new                     false
% 51.03/7.00  --inst_subs_new                         false
% 51.03/7.00  --inst_eq_res_simp                      false
% 51.03/7.00  --inst_subs_given                       false
% 51.03/7.00  --inst_orphan_elimination               true
% 51.03/7.00  --inst_learning_loop_flag               true
% 51.03/7.00  --inst_learning_start                   3000
% 51.03/7.00  --inst_learning_factor                  2
% 51.03/7.00  --inst_start_prop_sim_after_learn       3
% 51.03/7.00  --inst_sel_renew                        solver
% 51.03/7.00  --inst_lit_activity_flag                true
% 51.03/7.00  --inst_restr_to_given                   false
% 51.03/7.00  --inst_activity_threshold               500
% 51.03/7.00  --inst_out_proof                        true
% 51.03/7.00  
% 51.03/7.00  ------ Resolution Options
% 51.03/7.00  
% 51.03/7.00  --resolution_flag                       false
% 51.03/7.00  --res_lit_sel                           adaptive
% 51.03/7.00  --res_lit_sel_side                      none
% 51.03/7.00  --res_ordering                          kbo
% 51.03/7.00  --res_to_prop_solver                    active
% 51.03/7.00  --res_prop_simpl_new                    false
% 51.03/7.00  --res_prop_simpl_given                  true
% 51.03/7.00  --res_passive_queue_type                priority_queues
% 51.03/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.03/7.00  --res_passive_queues_freq               [15;5]
% 51.03/7.00  --res_forward_subs                      full
% 51.03/7.00  --res_backward_subs                     full
% 51.03/7.00  --res_forward_subs_resolution           true
% 51.03/7.00  --res_backward_subs_resolution          true
% 51.03/7.00  --res_orphan_elimination                true
% 51.03/7.00  --res_time_limit                        2.
% 51.03/7.00  --res_out_proof                         true
% 51.03/7.00  
% 51.03/7.00  ------ Superposition Options
% 51.03/7.00  
% 51.03/7.00  --superposition_flag                    true
% 51.03/7.00  --sup_passive_queue_type                priority_queues
% 51.03/7.00  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.03/7.00  --sup_passive_queues_freq               [8;1;4]
% 51.03/7.00  --demod_completeness_check              fast
% 51.03/7.00  --demod_use_ground                      true
% 51.03/7.00  --sup_to_prop_solver                    active
% 51.03/7.00  --sup_prop_simpl_new                    false
% 51.03/7.00  --sup_prop_simpl_given                  false
% 51.03/7.00  --sup_fun_splitting                     true
% 51.03/7.00  --sup_smt_interval                      10000
% 51.03/7.00  
% 51.03/7.00  ------ Superposition Simplification Setup
% 51.03/7.00  
% 51.03/7.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.03/7.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.03/7.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.03/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 51.03/7.00  --sup_full_triv                         [TrivRules]
% 51.03/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.03/7.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.03/7.00  --sup_immed_triv                        [TrivRules]
% 51.03/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.03/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.03/7.00  --sup_immed_bw_main                     []
% 51.03/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.03/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 51.03/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.03/7.00  --sup_input_bw                          [BwDemod;BwSubsumption]
% 51.03/7.00  
% 51.03/7.00  ------ Combination Options
% 51.03/7.00  
% 51.03/7.00  --comb_res_mult                         1
% 51.03/7.00  --comb_sup_mult                         1
% 51.03/7.00  --comb_inst_mult                        1000000
% 51.03/7.00  
% 51.03/7.00  ------ Debug Options
% 51.03/7.00  
% 51.03/7.00  --dbg_backtrace                         false
% 51.03/7.00  --dbg_dump_prop_clauses                 false
% 51.03/7.00  --dbg_dump_prop_clauses_file            -
% 51.03/7.00  --dbg_out_stat                          false
% 51.03/7.00  
% 51.03/7.00  
% 51.03/7.00  
% 51.03/7.00  
% 51.03/7.00  ------ Proving...
% 51.03/7.00  
% 51.03/7.00  
% 51.03/7.00  % SZS status Theorem for theBenchmark.p
% 51.03/7.00  
% 51.03/7.00   Resolution empty clause
% 51.03/7.00  
% 51.03/7.00  % SZS output start CNFRefutation for theBenchmark.p
% 51.03/7.00  
% 51.03/7.00  fof(f8,axiom,(
% 51.03/7.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 51.03/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.03/7.00  
% 51.03/7.00  fof(f25,plain,(
% 51.03/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 51.03/7.00    inference(cnf_transformation,[],[f8])).
% 51.03/7.00  
% 51.03/7.00  fof(f9,axiom,(
% 51.03/7.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 51.03/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.03/7.00  
% 51.03/7.00  fof(f26,plain,(
% 51.03/7.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 51.03/7.00    inference(cnf_transformation,[],[f9])).
% 51.03/7.00  
% 51.03/7.00  fof(f1,axiom,(
% 51.03/7.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 51.03/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.03/7.00  
% 51.03/7.00  fof(f18,plain,(
% 51.03/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 51.03/7.00    inference(cnf_transformation,[],[f1])).
% 51.03/7.00  
% 51.03/7.00  fof(f4,axiom,(
% 51.03/7.00    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 51.03/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.03/7.00  
% 51.03/7.00  fof(f14,plain,(
% 51.03/7.00    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 51.03/7.00    inference(ennf_transformation,[],[f4])).
% 51.03/7.00  
% 51.03/7.00  fof(f21,plain,(
% 51.03/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 51.03/7.00    inference(cnf_transformation,[],[f14])).
% 51.03/7.00  
% 51.03/7.00  fof(f7,axiom,(
% 51.03/7.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 51.03/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.03/7.00  
% 51.03/7.00  fof(f24,plain,(
% 51.03/7.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 51.03/7.00    inference(cnf_transformation,[],[f7])).
% 51.03/7.00  
% 51.03/7.00  fof(f3,axiom,(
% 51.03/7.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 51.03/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.03/7.00  
% 51.03/7.00  fof(f13,plain,(
% 51.03/7.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 51.03/7.00    inference(rectify,[],[f3])).
% 51.03/7.00  
% 51.03/7.00  fof(f20,plain,(
% 51.03/7.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 51.03/7.00    inference(cnf_transformation,[],[f13])).
% 51.03/7.00  
% 51.03/7.00  fof(f6,axiom,(
% 51.03/7.00    ! [X0,X1,X2] : k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))),
% 51.03/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.03/7.00  
% 51.03/7.00  fof(f23,plain,(
% 51.03/7.00    ( ! [X2,X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 51.03/7.00    inference(cnf_transformation,[],[f6])).
% 51.03/7.00  
% 51.03/7.00  fof(f5,axiom,(
% 51.03/7.00    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 51.03/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.03/7.00  
% 51.03/7.00  fof(f22,plain,(
% 51.03/7.00    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 51.03/7.00    inference(cnf_transformation,[],[f5])).
% 51.03/7.00  
% 51.03/7.00  fof(f2,axiom,(
% 51.03/7.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 51.03/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.03/7.00  
% 51.03/7.00  fof(f19,plain,(
% 51.03/7.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 51.03/7.00    inference(cnf_transformation,[],[f2])).
% 51.03/7.00  
% 51.03/7.00  fof(f10,axiom,(
% 51.03/7.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 51.03/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.03/7.00  
% 51.03/7.00  fof(f27,plain,(
% 51.03/7.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 51.03/7.00    inference(cnf_transformation,[],[f10])).
% 51.03/7.00  
% 51.03/7.00  fof(f11,conjecture,(
% 51.03/7.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 51.03/7.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.03/7.00  
% 51.03/7.00  fof(f12,negated_conjecture,(
% 51.03/7.00    ~! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 51.03/7.00    inference(negated_conjecture,[],[f11])).
% 51.03/7.00  
% 51.03/7.00  fof(f15,plain,(
% 51.03/7.00    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 51.03/7.00    inference(ennf_transformation,[],[f12])).
% 51.03/7.00  
% 51.03/7.00  fof(f16,plain,(
% 51.03/7.00    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 51.03/7.00    introduced(choice_axiom,[])).
% 51.03/7.00  
% 51.03/7.00  fof(f17,plain,(
% 51.03/7.00    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 51.03/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 51.03/7.00  
% 51.03/7.00  fof(f28,plain,(
% 51.03/7.00    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 51.03/7.00    inference(cnf_transformation,[],[f17])).
% 51.03/7.00  
% 51.03/7.00  cnf(c_7,plain,
% 51.03/7.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 51.03/7.00      inference(cnf_transformation,[],[f25]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_8,plain,
% 51.03/7.00      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 51.03/7.00      inference(cnf_transformation,[],[f26]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_86,plain,
% 51.03/7.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 51.03/7.00      inference(superposition,[status(thm)],[c_8,c_7]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_87,plain,
% 51.03/7.00      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 51.03/7.00      inference(light_normalisation,[status(thm)],[c_86,c_7]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_178,plain,
% 51.03/7.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 51.03/7.00      inference(superposition,[status(thm)],[c_7,c_87]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_0,plain,
% 51.03/7.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 51.03/7.00      inference(cnf_transformation,[],[f18]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_80,plain,
% 51.03/7.00      ( k4_xboole_0(k2_xboole_0(X0,X1),X0) = k4_xboole_0(X1,X0) ),
% 51.03/7.00      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_3,plain,
% 51.03/7.00      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 51.03/7.00      inference(cnf_transformation,[],[f21]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_6,plain,
% 51.03/7.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 51.03/7.00      inference(cnf_transformation,[],[f24]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_47,plain,
% 51.03/7.00      ( X0 != X1 | k4_xboole_0(X0,X2) != X3 | k2_xboole_0(X3,X1) = X1 ),
% 51.03/7.00      inference(resolution_lifted,[status(thm)],[c_3,c_6]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_48,plain,
% 51.03/7.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 51.03/7.00      inference(unflattening,[status(thm)],[c_47]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_152,plain,
% 51.03/7.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 51.03/7.00      inference(superposition,[status(thm)],[c_80,c_48]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_190,plain,
% 51.03/7.00      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X1,X0) ),
% 51.03/7.00      inference(light_normalisation,[status(thm)],[c_178,c_152]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_2,plain,
% 51.03/7.00      ( k3_xboole_0(X0,X0) = X0 ),
% 51.03/7.00      inference(cnf_transformation,[],[f20]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_5,plain,
% 51.03/7.00      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 51.03/7.00      inference(cnf_transformation,[],[f23]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_102,plain,
% 51.03/7.00      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 51.03/7.00      inference(superposition,[status(thm)],[c_2,c_5]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_4,plain,
% 51.03/7.00      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 51.03/7.00      inference(cnf_transformation,[],[f22]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_113,plain,
% 51.03/7.00      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 51.03/7.00      inference(light_normalisation,[status(thm)],[c_102,c_4]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_120,plain,
% 51.03/7.00      ( k3_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X1) ),
% 51.03/7.00      inference(superposition,[status(thm)],[c_48,c_113]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_1,plain,
% 51.03/7.00      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 51.03/7.00      inference(cnf_transformation,[],[f19]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_203,plain,
% 51.03/7.00      ( k3_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 51.03/7.00      inference(superposition,[status(thm)],[c_120,c_1]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_657,plain,
% 51.03/7.00      ( k3_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
% 51.03/7.00      inference(superposition,[status(thm)],[c_203,c_5]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_240463,plain,
% 51.03/7.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k2_xboole_0(X1,X0)) ),
% 51.03/7.00      inference(superposition,[status(thm)],[c_190,c_657]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_115,plain,
% 51.03/7.00      ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
% 51.03/7.00      inference(superposition,[status(thm)],[c_0,c_113]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_241988,plain,
% 51.03/7.00      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = X0 ),
% 51.03/7.00      inference(light_normalisation,[status(thm)],[c_240463,c_115]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_246006,plain,
% 51.03/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 51.03/7.00      inference(superposition,[status(thm)],[c_241988,c_8]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_66,plain,
% 51.03/7.00      ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
% 51.03/7.00      inference(superposition,[status(thm)],[c_1,c_4]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_9,plain,
% 51.03/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 51.03/7.00      inference(cnf_transformation,[],[f27]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_147,plain,
% 51.03/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
% 51.03/7.00      inference(superposition,[status(thm)],[c_7,c_80]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_156,plain,
% 51.03/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 51.03/7.00      inference(demodulation,[status(thm)],[c_147,c_80]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_448,plain,
% 51.03/7.00      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 51.03/7.00      inference(superposition,[status(thm)],[c_9,c_156]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_470,plain,
% 51.03/7.00      ( k4_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 51.03/7.00      inference(light_normalisation,[status(thm)],[c_448,c_9]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_29132,plain,
% 51.03/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k3_xboole_0(X2,X1))) ),
% 51.03/7.00      inference(superposition,[status(thm)],[c_66,c_470]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_29355,plain,
% 51.03/7.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k4_xboole_0(X0,X1) ),
% 51.03/7.00      inference(demodulation,[status(thm)],[c_29132,c_9,c_66]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_246302,plain,
% 51.03/7.00      ( k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
% 51.03/7.00      inference(demodulation,[status(thm)],[c_246006,c_29355]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_10,negated_conjecture,
% 51.03/7.00      ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
% 51.03/7.00      inference(cnf_transformation,[],[f28]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_249265,plain,
% 51.03/7.00      ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
% 51.03/7.00      inference(demodulation,[status(thm)],[c_246302,c_10]) ).
% 51.03/7.00  
% 51.03/7.00  cnf(c_249266,plain,
% 51.03/7.00      ( $false ),
% 51.03/7.00      inference(theory_normalisation,[status(thm)],[c_249265]) ).
% 51.03/7.00  
% 51.03/7.00  
% 51.03/7.00  % SZS output end CNFRefutation for theBenchmark.p
% 51.03/7.00  
% 51.03/7.00  ------                               Statistics
% 51.03/7.00  
% 51.03/7.00  ------ General
% 51.03/7.00  
% 51.03/7.00  abstr_ref_over_cycles:                  0
% 51.03/7.00  abstr_ref_under_cycles:                 0
% 51.03/7.00  gc_basic_clause_elim:                   0
% 51.03/7.00  forced_gc_time:                         0
% 51.03/7.00  parsing_time:                           0.008
% 51.03/7.00  unif_index_cands_time:                  0.
% 51.03/7.00  unif_index_add_time:                    0.
% 51.03/7.00  orderings_time:                         0.
% 51.03/7.00  out_proof_time:                         0.005
% 51.03/7.00  total_time:                             6.419
% 51.03/7.00  num_of_symbols:                         38
% 51.03/7.00  num_of_terms:                           280725
% 51.03/7.00  
% 51.03/7.00  ------ Preprocessing
% 51.03/7.00  
% 51.03/7.00  num_of_splits:                          0
% 51.03/7.00  num_of_split_atoms:                     1
% 51.03/7.00  num_of_reused_defs:                     0
% 51.03/7.00  num_eq_ax_congr_red:                    1
% 51.03/7.00  num_of_sem_filtered_clauses:            0
% 51.03/7.00  num_of_subtypes:                        0
% 51.03/7.00  monotx_restored_types:                  0
% 51.03/7.00  sat_num_of_epr_types:                   0
% 51.03/7.00  sat_num_of_non_cyclic_types:            0
% 51.03/7.00  sat_guarded_non_collapsed_types:        0
% 51.03/7.00  num_pure_diseq_elim:                    0
% 51.03/7.00  simp_replaced_by:                       0
% 51.03/7.00  res_preprocessed:                       36
% 51.03/7.00  prep_upred:                             0
% 51.03/7.00  prep_unflattend:                        2
% 51.03/7.00  smt_new_axioms:                         0
% 51.03/7.00  pred_elim_cands:                        0
% 51.03/7.00  pred_elim:                              1
% 51.03/7.00  pred_elim_cl:                           1
% 51.03/7.00  pred_elim_cycles:                       2
% 51.03/7.00  merged_defs:                            0
% 51.03/7.00  merged_defs_ncl:                        0
% 51.03/7.00  bin_hyper_res:                          0
% 51.03/7.00  prep_cycles:                            3
% 51.03/7.00  pred_elim_time:                         0.
% 51.03/7.00  splitting_time:                         0.
% 51.03/7.00  sem_filter_time:                        0.
% 51.03/7.00  monotx_time:                            0.
% 51.03/7.00  subtype_inf_time:                       0.
% 51.03/7.00  
% 51.03/7.00  ------ Problem properties
% 51.03/7.00  
% 51.03/7.00  clauses:                                10
% 51.03/7.00  conjectures:                            1
% 51.03/7.00  epr:                                    0
% 51.03/7.00  horn:                                   10
% 51.03/7.00  ground:                                 1
% 51.03/7.00  unary:                                  10
% 51.03/7.00  binary:                                 0
% 51.03/7.00  lits:                                   10
% 51.03/7.00  lits_eq:                                10
% 51.03/7.00  fd_pure:                                0
% 51.03/7.00  fd_pseudo:                              0
% 51.03/7.00  fd_cond:                                0
% 51.03/7.00  fd_pseudo_cond:                         0
% 51.03/7.00  ac_symbols:                             1
% 51.03/7.00  
% 51.03/7.00  ------ Propositional Solver
% 51.03/7.00  
% 51.03/7.00  prop_solver_calls:                      17
% 51.03/7.00  prop_fast_solver_calls:                 91
% 51.03/7.00  smt_solver_calls:                       0
% 51.03/7.00  smt_fast_solver_calls:                  0
% 51.03/7.00  prop_num_of_clauses:                    854
% 51.03/7.00  prop_preprocess_simplified:             770
% 51.03/7.00  prop_fo_subsumed:                       0
% 51.03/7.00  prop_solver_time:                       0.
% 51.03/7.00  smt_solver_time:                        0.
% 51.03/7.00  smt_fast_solver_time:                   0.
% 51.03/7.00  prop_fast_solver_time:                  0.
% 51.03/7.00  prop_unsat_core_time:                   0.
% 51.03/7.00  
% 51.03/7.00  ------ QBF
% 51.03/7.00  
% 51.03/7.00  qbf_q_res:                              0
% 51.03/7.00  qbf_num_tautologies:                    0
% 51.03/7.00  qbf_prep_cycles:                        0
% 51.03/7.00  
% 51.03/7.00  ------ BMC1
% 51.03/7.00  
% 51.03/7.00  bmc1_current_bound:                     -1
% 51.03/7.00  bmc1_last_solved_bound:                 -1
% 51.03/7.00  bmc1_unsat_core_size:                   -1
% 51.03/7.00  bmc1_unsat_core_parents_size:           -1
% 51.03/7.00  bmc1_merge_next_fun:                    0
% 51.03/7.00  bmc1_unsat_core_clauses_time:           0.
% 51.03/7.00  
% 51.03/7.00  ------ Instantiation
% 51.03/7.00  
% 51.03/7.00  inst_num_of_clauses:                    0
% 51.03/7.00  inst_num_in_passive:                    0
% 51.03/7.00  inst_num_in_active:                     0
% 51.03/7.00  inst_num_in_unprocessed:                0
% 51.03/7.00  inst_num_of_loops:                      0
% 51.03/7.00  inst_num_of_learning_restarts:          0
% 51.03/7.00  inst_num_moves_active_passive:          0
% 51.03/7.00  inst_lit_activity:                      0
% 51.03/7.00  inst_lit_activity_moves:                0
% 51.03/7.00  inst_num_tautologies:                   0
% 51.03/7.00  inst_num_prop_implied:                  0
% 51.03/7.00  inst_num_existing_simplified:           0
% 51.03/7.00  inst_num_eq_res_simplified:             0
% 51.03/7.00  inst_num_child_elim:                    0
% 51.03/7.00  inst_num_of_dismatching_blockings:      0
% 51.03/7.00  inst_num_of_non_proper_insts:           0
% 51.03/7.00  inst_num_of_duplicates:                 0
% 51.03/7.00  inst_inst_num_from_inst_to_res:         0
% 51.03/7.00  inst_dismatching_checking_time:         0.
% 51.03/7.00  
% 51.03/7.00  ------ Resolution
% 51.03/7.00  
% 51.03/7.00  res_num_of_clauses:                     0
% 51.03/7.00  res_num_in_passive:                     0
% 51.03/7.00  res_num_in_active:                      0
% 51.03/7.00  res_num_of_loops:                       39
% 51.03/7.00  res_forward_subset_subsumed:            0
% 51.03/7.00  res_backward_subset_subsumed:           0
% 51.03/7.00  res_forward_subsumed:                   0
% 51.03/7.00  res_backward_subsumed:                  0
% 51.03/7.00  res_forward_subsumption_resolution:     0
% 51.03/7.00  res_backward_subsumption_resolution:    0
% 51.03/7.00  res_clause_to_clause_subsumption:       751645
% 51.03/7.00  res_orphan_elimination:                 0
% 51.03/7.00  res_tautology_del:                      0
% 51.03/7.00  res_num_eq_res_simplified:              0
% 51.03/7.00  res_num_sel_changes:                    0
% 51.03/7.00  res_moves_from_active_to_pass:          0
% 51.03/7.00  
% 51.03/7.00  ------ Superposition
% 51.03/7.00  
% 51.03/7.00  sup_time_total:                         0.
% 51.03/7.00  sup_time_generating:                    0.
% 51.03/7.00  sup_time_sim_full:                      0.
% 51.03/7.00  sup_time_sim_immed:                     0.
% 51.03/7.00  
% 51.03/7.00  sup_num_of_clauses:                     22566
% 51.03/7.00  sup_num_in_active:                      496
% 51.03/7.00  sup_num_in_passive:                     22070
% 51.03/7.00  sup_num_of_loops:                       549
% 51.03/7.00  sup_fw_superposition:                   100278
% 51.03/7.00  sup_bw_superposition:                   83724
% 51.03/7.00  sup_immediate_simplified:               68685
% 51.03/7.00  sup_given_eliminated:                   3
% 51.03/7.00  comparisons_done:                       0
% 51.03/7.00  comparisons_avoided:                    0
% 51.03/7.00  
% 51.03/7.00  ------ Simplifications
% 51.03/7.00  
% 51.03/7.00  
% 51.03/7.00  sim_fw_subset_subsumed:                 0
% 51.03/7.00  sim_bw_subset_subsumed:                 0
% 51.03/7.00  sim_fw_subsumed:                        13423
% 51.03/7.00  sim_bw_subsumed:                        208
% 51.03/7.00  sim_fw_subsumption_res:                 0
% 51.03/7.00  sim_bw_subsumption_res:                 0
% 51.03/7.00  sim_tautology_del:                      0
% 51.03/7.00  sim_eq_tautology_del:                   18134
% 51.03/7.00  sim_eq_res_simp:                        0
% 51.03/7.00  sim_fw_demodulated:                     36335
% 51.03/7.00  sim_bw_demodulated:                     218
% 51.03/7.00  sim_light_normalised:                   28221
% 51.03/7.00  sim_joinable_taut:                      216
% 51.03/7.00  sim_joinable_simp:                      1
% 51.03/7.00  sim_ac_normalised:                      0
% 51.03/7.00  sim_smt_subsumption:                    0
% 51.03/7.00  
%------------------------------------------------------------------------------
