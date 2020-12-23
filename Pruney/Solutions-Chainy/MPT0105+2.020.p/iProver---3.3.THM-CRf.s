%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:14 EST 2020

% Result     : Theorem 7.69s
% Output     : CNFRefutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 161 expanded)
%              Number of clauses        :   29 (  61 expanded)
%              Number of leaves         :   12 (  44 expanded)
%              Depth                    :   17
%              Number of atoms          :   60 ( 162 expanded)
%              Number of equality atoms :   59 ( 161 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f20,f25])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f19,f25])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k3_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f17,f25,f25])).

fof(f11,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f12])).

fof(f14,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f26,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(definition_unfolding,[],[f26,f25])).

cnf(c_6,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_5,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_217,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(k3_xboole_0(X0,X1),X2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5,c_4])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1157,plain,
    ( k3_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k3_xboole_0(X0,X1)),X2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_217,c_3])).

cnf(c_1170,plain,
    ( k3_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_1157])).

cnf(c_1215,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1170,c_6])).

cnf(c_8,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_118,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7,c_4])).

cnf(c_235,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_118])).

cnf(c_1898,plain,
    ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_235,c_7,c_1215])).

cnf(c_1914,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X0),X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1898,c_3])).

cnf(c_7117,plain,
    ( k4_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0),X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1215,c_1914])).

cnf(c_7270,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7117,c_7])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_214,plain,
    ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X1,k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_5])).

cnf(c_708,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,k4_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_214,c_5])).

cnf(c_7356,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_7270,c_708])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_993,plain,
    ( k3_xboole_0(k4_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_708,c_0])).

cnf(c_7364,plain,
    ( k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7356,c_2,c_993,c_1215])).

cnf(c_1,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k3_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_7534,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7364,c_1])).

cnf(c_7535,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_7534,c_7])).

cnf(c_9,negated_conjecture,
    ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_24050,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_7535,c_9])).

cnf(c_24055,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_24050])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n006.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 14:54:37 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 7.69/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.69/1.51  
% 7.69/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.69/1.51  
% 7.69/1.51  ------  iProver source info
% 7.69/1.51  
% 7.69/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.69/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.69/1.51  git: non_committed_changes: false
% 7.69/1.51  git: last_make_outside_of_git: false
% 7.69/1.51  
% 7.69/1.51  ------ 
% 7.69/1.51  
% 7.69/1.51  ------ Input Options
% 7.69/1.51  
% 7.69/1.51  --out_options                           all
% 7.69/1.51  --tptp_safe_out                         true
% 7.69/1.51  --problem_path                          ""
% 7.69/1.51  --include_path                          ""
% 7.69/1.51  --clausifier                            res/vclausify_rel
% 7.69/1.51  --clausifier_options                    --mode clausify
% 7.69/1.51  --stdin                                 false
% 7.69/1.51  --stats_out                             sel
% 7.69/1.51  
% 7.69/1.51  ------ General Options
% 7.69/1.51  
% 7.69/1.51  --fof                                   false
% 7.69/1.51  --time_out_real                         604.99
% 7.69/1.51  --time_out_virtual                      -1.
% 7.69/1.51  --symbol_type_check                     false
% 7.69/1.51  --clausify_out                          false
% 7.69/1.51  --sig_cnt_out                           false
% 7.69/1.51  --trig_cnt_out                          false
% 7.69/1.51  --trig_cnt_out_tolerance                1.
% 7.69/1.51  --trig_cnt_out_sk_spl                   false
% 7.69/1.51  --abstr_cl_out                          false
% 7.69/1.51  
% 7.69/1.51  ------ Global Options
% 7.69/1.51  
% 7.69/1.51  --schedule                              none
% 7.69/1.51  --add_important_lit                     false
% 7.69/1.51  --prop_solver_per_cl                    1000
% 7.69/1.51  --min_unsat_core                        false
% 7.69/1.51  --soft_assumptions                      false
% 7.69/1.51  --soft_lemma_size                       3
% 7.69/1.51  --prop_impl_unit_size                   0
% 7.69/1.51  --prop_impl_unit                        []
% 7.69/1.51  --share_sel_clauses                     true
% 7.69/1.51  --reset_solvers                         false
% 7.69/1.51  --bc_imp_inh                            [conj_cone]
% 7.69/1.51  --conj_cone_tolerance                   3.
% 7.69/1.51  --extra_neg_conj                        none
% 7.69/1.51  --large_theory_mode                     true
% 7.69/1.51  --prolific_symb_bound                   200
% 7.69/1.51  --lt_threshold                          2000
% 7.69/1.51  --clause_weak_htbl                      true
% 7.69/1.51  --gc_record_bc_elim                     false
% 7.69/1.51  
% 7.69/1.51  ------ Preprocessing Options
% 7.69/1.51  
% 7.69/1.51  --preprocessing_flag                    true
% 7.69/1.51  --time_out_prep_mult                    0.1
% 7.69/1.51  --splitting_mode                        input
% 7.69/1.51  --splitting_grd                         true
% 7.69/1.51  --splitting_cvd                         false
% 7.69/1.51  --splitting_cvd_svl                     false
% 7.69/1.51  --splitting_nvd                         32
% 7.69/1.51  --sub_typing                            true
% 7.69/1.51  --prep_gs_sim                           false
% 7.69/1.51  --prep_unflatten                        true
% 7.69/1.51  --prep_res_sim                          true
% 7.69/1.51  --prep_upred                            true
% 7.69/1.51  --prep_sem_filter                       exhaustive
% 7.69/1.51  --prep_sem_filter_out                   false
% 7.69/1.51  --pred_elim                             false
% 7.69/1.51  --res_sim_input                         true
% 7.69/1.51  --eq_ax_congr_red                       true
% 7.69/1.51  --pure_diseq_elim                       true
% 7.69/1.51  --brand_transform                       false
% 7.69/1.51  --non_eq_to_eq                          false
% 7.69/1.51  --prep_def_merge                        true
% 7.69/1.51  --prep_def_merge_prop_impl              false
% 7.69/1.51  --prep_def_merge_mbd                    true
% 7.69/1.51  --prep_def_merge_tr_red                 false
% 7.69/1.51  --prep_def_merge_tr_cl                  false
% 7.69/1.51  --smt_preprocessing                     true
% 7.69/1.51  --smt_ac_axioms                         fast
% 7.69/1.51  --preprocessed_out                      false
% 7.69/1.51  --preprocessed_stats                    false
% 7.69/1.51  
% 7.69/1.51  ------ Abstraction refinement Options
% 7.69/1.51  
% 7.69/1.51  --abstr_ref                             []
% 7.69/1.51  --abstr_ref_prep                        false
% 7.69/1.51  --abstr_ref_until_sat                   false
% 7.69/1.51  --abstr_ref_sig_restrict                funpre
% 7.69/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.69/1.51  --abstr_ref_under                       []
% 7.69/1.51  
% 7.69/1.51  ------ SAT Options
% 7.69/1.51  
% 7.69/1.51  --sat_mode                              false
% 7.69/1.51  --sat_fm_restart_options                ""
% 7.69/1.51  --sat_gr_def                            false
% 7.69/1.51  --sat_epr_types                         true
% 7.69/1.51  --sat_non_cyclic_types                  false
% 7.69/1.51  --sat_finite_models                     false
% 7.69/1.51  --sat_fm_lemmas                         false
% 7.69/1.51  --sat_fm_prep                           false
% 7.69/1.51  --sat_fm_uc_incr                        true
% 7.69/1.51  --sat_out_model                         small
% 7.69/1.51  --sat_out_clauses                       false
% 7.69/1.51  
% 7.69/1.51  ------ QBF Options
% 7.69/1.51  
% 7.69/1.51  --qbf_mode                              false
% 7.69/1.51  --qbf_elim_univ                         false
% 7.69/1.51  --qbf_dom_inst                          none
% 7.69/1.51  --qbf_dom_pre_inst                      false
% 7.69/1.51  --qbf_sk_in                             false
% 7.69/1.51  --qbf_pred_elim                         true
% 7.69/1.51  --qbf_split                             512
% 7.69/1.51  
% 7.69/1.51  ------ BMC1 Options
% 7.69/1.51  
% 7.69/1.51  --bmc1_incremental                      false
% 7.69/1.51  --bmc1_axioms                           reachable_all
% 7.69/1.51  --bmc1_min_bound                        0
% 7.69/1.51  --bmc1_max_bound                        -1
% 7.69/1.51  --bmc1_max_bound_default                -1
% 7.69/1.51  --bmc1_symbol_reachability              true
% 7.69/1.51  --bmc1_property_lemmas                  false
% 7.69/1.51  --bmc1_k_induction                      false
% 7.69/1.51  --bmc1_non_equiv_states                 false
% 7.69/1.51  --bmc1_deadlock                         false
% 7.69/1.51  --bmc1_ucm                              false
% 7.69/1.51  --bmc1_add_unsat_core                   none
% 7.69/1.51  --bmc1_unsat_core_children              false
% 7.69/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.69/1.51  --bmc1_out_stat                         full
% 7.69/1.51  --bmc1_ground_init                      false
% 7.69/1.51  --bmc1_pre_inst_next_state              false
% 7.69/1.51  --bmc1_pre_inst_state                   false
% 7.69/1.51  --bmc1_pre_inst_reach_state             false
% 7.69/1.51  --bmc1_out_unsat_core                   false
% 7.69/1.51  --bmc1_aig_witness_out                  false
% 7.69/1.51  --bmc1_verbose                          false
% 7.69/1.51  --bmc1_dump_clauses_tptp                false
% 7.69/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.69/1.51  --bmc1_dump_file                        -
% 7.69/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.69/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.69/1.51  --bmc1_ucm_extend_mode                  1
% 7.69/1.51  --bmc1_ucm_init_mode                    2
% 7.69/1.51  --bmc1_ucm_cone_mode                    none
% 7.69/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.69/1.51  --bmc1_ucm_relax_model                  4
% 7.69/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.69/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.69/1.51  --bmc1_ucm_layered_model                none
% 7.69/1.51  --bmc1_ucm_max_lemma_size               10
% 7.69/1.51  
% 7.69/1.51  ------ AIG Options
% 7.69/1.51  
% 7.69/1.51  --aig_mode                              false
% 7.69/1.51  
% 7.69/1.51  ------ Instantiation Options
% 7.69/1.51  
% 7.69/1.51  --instantiation_flag                    true
% 7.69/1.51  --inst_sos_flag                         false
% 7.69/1.51  --inst_sos_phase                        true
% 7.69/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.69/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.69/1.51  --inst_lit_sel_side                     num_symb
% 7.69/1.51  --inst_solver_per_active                1400
% 7.69/1.51  --inst_solver_calls_frac                1.
% 7.69/1.51  --inst_passive_queue_type               priority_queues
% 7.69/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.69/1.51  --inst_passive_queues_freq              [25;2]
% 7.69/1.51  --inst_dismatching                      true
% 7.69/1.51  --inst_eager_unprocessed_to_passive     true
% 7.69/1.51  --inst_prop_sim_given                   true
% 7.69/1.51  --inst_prop_sim_new                     false
% 7.69/1.51  --inst_subs_new                         false
% 7.69/1.51  --inst_eq_res_simp                      false
% 7.69/1.51  --inst_subs_given                       false
% 7.69/1.51  --inst_orphan_elimination               true
% 7.69/1.51  --inst_learning_loop_flag               true
% 7.69/1.51  --inst_learning_start                   3000
% 7.69/1.51  --inst_learning_factor                  2
% 7.69/1.51  --inst_start_prop_sim_after_learn       3
% 7.69/1.51  --inst_sel_renew                        solver
% 7.69/1.51  --inst_lit_activity_flag                true
% 7.69/1.51  --inst_restr_to_given                   false
% 7.69/1.51  --inst_activity_threshold               500
% 7.69/1.51  --inst_out_proof                        true
% 7.69/1.51  
% 7.69/1.51  ------ Resolution Options
% 7.69/1.51  
% 7.69/1.51  --resolution_flag                       true
% 7.69/1.51  --res_lit_sel                           adaptive
% 7.69/1.51  --res_lit_sel_side                      none
% 7.69/1.51  --res_ordering                          kbo
% 7.69/1.51  --res_to_prop_solver                    active
% 7.69/1.51  --res_prop_simpl_new                    false
% 7.69/1.51  --res_prop_simpl_given                  true
% 7.69/1.51  --res_passive_queue_type                priority_queues
% 7.69/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.69/1.51  --res_passive_queues_freq               [15;5]
% 7.69/1.51  --res_forward_subs                      full
% 7.69/1.51  --res_backward_subs                     full
% 7.69/1.51  --res_forward_subs_resolution           true
% 7.69/1.51  --res_backward_subs_resolution          true
% 7.69/1.51  --res_orphan_elimination                true
% 7.69/1.51  --res_time_limit                        2.
% 7.69/1.51  --res_out_proof                         true
% 7.69/1.51  
% 7.69/1.51  ------ Superposition Options
% 7.69/1.51  
% 7.69/1.51  --superposition_flag                    true
% 7.69/1.51  --sup_passive_queue_type                priority_queues
% 7.69/1.51  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.69/1.51  --sup_passive_queues_freq               [1;4]
% 7.69/1.51  --demod_completeness_check              fast
% 7.69/1.51  --demod_use_ground                      true
% 7.69/1.51  --sup_to_prop_solver                    passive
% 7.69/1.51  --sup_prop_simpl_new                    true
% 7.69/1.51  --sup_prop_simpl_given                  true
% 7.69/1.51  --sup_fun_splitting                     false
% 7.69/1.51  --sup_smt_interval                      50000
% 7.69/1.51  
% 7.69/1.51  ------ Superposition Simplification Setup
% 7.69/1.51  
% 7.69/1.51  --sup_indices_passive                   []
% 7.69/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.69/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.69/1.51  --sup_full_bw                           [BwDemod]
% 7.69/1.51  --sup_immed_triv                        [TrivRules]
% 7.69/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.69/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.69/1.51  --sup_immed_bw_main                     []
% 7.69/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.69/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.69/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.69/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.69/1.51  
% 7.69/1.51  ------ Combination Options
% 7.69/1.51  
% 7.69/1.51  --comb_res_mult                         3
% 7.69/1.51  --comb_sup_mult                         2
% 7.69/1.51  --comb_inst_mult                        10
% 7.69/1.51  
% 7.69/1.51  ------ Debug Options
% 7.69/1.51  
% 7.69/1.51  --dbg_backtrace                         false
% 7.69/1.51  --dbg_dump_prop_clauses                 false
% 7.69/1.51  --dbg_dump_prop_clauses_file            -
% 7.69/1.51  --dbg_out_stat                          false
% 7.69/1.51  ------ Parsing...
% 7.69/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.69/1.51  
% 7.69/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.69/1.51  
% 7.69/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.69/1.51  
% 7.69/1.51  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.69/1.51  ------ Proving...
% 7.69/1.51  ------ Problem Properties 
% 7.69/1.51  
% 7.69/1.51  
% 7.69/1.51  clauses                                 10
% 7.69/1.51  conjectures                             1
% 7.69/1.51  EPR                                     0
% 7.69/1.51  Horn                                    10
% 7.69/1.51  unary                                   10
% 7.69/1.51  binary                                  0
% 7.69/1.51  lits                                    10
% 7.69/1.51  lits eq                                 10
% 7.69/1.51  fd_pure                                 0
% 7.69/1.51  fd_pseudo                               0
% 7.69/1.51  fd_cond                                 0
% 7.69/1.51  fd_pseudo_cond                          0
% 7.69/1.51  AC symbols                              0
% 7.69/1.51  
% 7.69/1.51  ------ Input Options Time Limit: Unbounded
% 7.69/1.51  
% 7.69/1.51  
% 7.69/1.51  ------ 
% 7.69/1.51  Current options:
% 7.69/1.51  ------ 
% 7.69/1.51  
% 7.69/1.51  ------ Input Options
% 7.69/1.51  
% 7.69/1.51  --out_options                           all
% 7.69/1.51  --tptp_safe_out                         true
% 7.69/1.51  --problem_path                          ""
% 7.69/1.51  --include_path                          ""
% 7.69/1.51  --clausifier                            res/vclausify_rel
% 7.69/1.51  --clausifier_options                    --mode clausify
% 7.69/1.51  --stdin                                 false
% 7.69/1.51  --stats_out                             sel
% 7.69/1.51  
% 7.69/1.51  ------ General Options
% 7.69/1.51  
% 7.69/1.51  --fof                                   false
% 7.69/1.51  --time_out_real                         604.99
% 7.69/1.51  --time_out_virtual                      -1.
% 7.69/1.51  --symbol_type_check                     false
% 7.69/1.51  --clausify_out                          false
% 7.69/1.51  --sig_cnt_out                           false
% 7.69/1.51  --trig_cnt_out                          false
% 7.69/1.51  --trig_cnt_out_tolerance                1.
% 7.69/1.51  --trig_cnt_out_sk_spl                   false
% 7.69/1.51  --abstr_cl_out                          false
% 7.69/1.51  
% 7.69/1.51  ------ Global Options
% 7.69/1.51  
% 7.69/1.51  --schedule                              none
% 7.69/1.51  --add_important_lit                     false
% 7.69/1.51  --prop_solver_per_cl                    1000
% 7.69/1.51  --min_unsat_core                        false
% 7.69/1.51  --soft_assumptions                      false
% 7.69/1.51  --soft_lemma_size                       3
% 7.69/1.51  --prop_impl_unit_size                   0
% 7.69/1.51  --prop_impl_unit                        []
% 7.69/1.51  --share_sel_clauses                     true
% 7.69/1.51  --reset_solvers                         false
% 7.69/1.51  --bc_imp_inh                            [conj_cone]
% 7.69/1.51  --conj_cone_tolerance                   3.
% 7.69/1.51  --extra_neg_conj                        none
% 7.69/1.51  --large_theory_mode                     true
% 7.69/1.51  --prolific_symb_bound                   200
% 7.69/1.51  --lt_threshold                          2000
% 7.69/1.51  --clause_weak_htbl                      true
% 7.69/1.51  --gc_record_bc_elim                     false
% 7.69/1.51  
% 7.69/1.51  ------ Preprocessing Options
% 7.69/1.51  
% 7.69/1.51  --preprocessing_flag                    true
% 7.69/1.51  --time_out_prep_mult                    0.1
% 7.69/1.51  --splitting_mode                        input
% 7.69/1.51  --splitting_grd                         true
% 7.69/1.51  --splitting_cvd                         false
% 7.69/1.51  --splitting_cvd_svl                     false
% 7.69/1.51  --splitting_nvd                         32
% 7.69/1.51  --sub_typing                            true
% 7.69/1.51  --prep_gs_sim                           false
% 7.69/1.51  --prep_unflatten                        true
% 7.69/1.51  --prep_res_sim                          true
% 7.69/1.51  --prep_upred                            true
% 7.69/1.51  --prep_sem_filter                       exhaustive
% 7.69/1.51  --prep_sem_filter_out                   false
% 7.69/1.51  --pred_elim                             false
% 7.69/1.51  --res_sim_input                         true
% 7.69/1.51  --eq_ax_congr_red                       true
% 7.69/1.51  --pure_diseq_elim                       true
% 7.69/1.51  --brand_transform                       false
% 7.69/1.51  --non_eq_to_eq                          false
% 7.69/1.51  --prep_def_merge                        true
% 7.69/1.51  --prep_def_merge_prop_impl              false
% 7.69/1.51  --prep_def_merge_mbd                    true
% 7.69/1.51  --prep_def_merge_tr_red                 false
% 7.69/1.51  --prep_def_merge_tr_cl                  false
% 7.69/1.51  --smt_preprocessing                     true
% 7.69/1.51  --smt_ac_axioms                         fast
% 7.69/1.51  --preprocessed_out                      false
% 7.69/1.51  --preprocessed_stats                    false
% 7.69/1.51  
% 7.69/1.51  ------ Abstraction refinement Options
% 7.69/1.51  
% 7.69/1.51  --abstr_ref                             []
% 7.69/1.51  --abstr_ref_prep                        false
% 7.69/1.51  --abstr_ref_until_sat                   false
% 7.69/1.51  --abstr_ref_sig_restrict                funpre
% 7.69/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.69/1.51  --abstr_ref_under                       []
% 7.69/1.51  
% 7.69/1.51  ------ SAT Options
% 7.69/1.51  
% 7.69/1.51  --sat_mode                              false
% 7.69/1.51  --sat_fm_restart_options                ""
% 7.69/1.51  --sat_gr_def                            false
% 7.69/1.51  --sat_epr_types                         true
% 7.69/1.51  --sat_non_cyclic_types                  false
% 7.69/1.51  --sat_finite_models                     false
% 7.69/1.51  --sat_fm_lemmas                         false
% 7.69/1.51  --sat_fm_prep                           false
% 7.69/1.51  --sat_fm_uc_incr                        true
% 7.69/1.51  --sat_out_model                         small
% 7.69/1.51  --sat_out_clauses                       false
% 7.69/1.51  
% 7.69/1.51  ------ QBF Options
% 7.69/1.51  
% 7.69/1.51  --qbf_mode                              false
% 7.69/1.51  --qbf_elim_univ                         false
% 7.69/1.51  --qbf_dom_inst                          none
% 7.69/1.51  --qbf_dom_pre_inst                      false
% 7.69/1.51  --qbf_sk_in                             false
% 7.69/1.51  --qbf_pred_elim                         true
% 7.69/1.51  --qbf_split                             512
% 7.69/1.51  
% 7.69/1.51  ------ BMC1 Options
% 7.69/1.51  
% 7.69/1.51  --bmc1_incremental                      false
% 7.69/1.51  --bmc1_axioms                           reachable_all
% 7.69/1.51  --bmc1_min_bound                        0
% 7.69/1.51  --bmc1_max_bound                        -1
% 7.69/1.51  --bmc1_max_bound_default                -1
% 7.69/1.51  --bmc1_symbol_reachability              true
% 7.69/1.51  --bmc1_property_lemmas                  false
% 7.69/1.51  --bmc1_k_induction                      false
% 7.69/1.51  --bmc1_non_equiv_states                 false
% 7.69/1.51  --bmc1_deadlock                         false
% 7.69/1.51  --bmc1_ucm                              false
% 7.69/1.51  --bmc1_add_unsat_core                   none
% 7.69/1.51  --bmc1_unsat_core_children              false
% 7.69/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.69/1.51  --bmc1_out_stat                         full
% 7.69/1.51  --bmc1_ground_init                      false
% 7.69/1.51  --bmc1_pre_inst_next_state              false
% 7.69/1.51  --bmc1_pre_inst_state                   false
% 7.69/1.51  --bmc1_pre_inst_reach_state             false
% 7.69/1.51  --bmc1_out_unsat_core                   false
% 7.69/1.51  --bmc1_aig_witness_out                  false
% 7.69/1.51  --bmc1_verbose                          false
% 7.69/1.51  --bmc1_dump_clauses_tptp                false
% 7.69/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.69/1.51  --bmc1_dump_file                        -
% 7.69/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.69/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.69/1.51  --bmc1_ucm_extend_mode                  1
% 7.69/1.51  --bmc1_ucm_init_mode                    2
% 7.69/1.51  --bmc1_ucm_cone_mode                    none
% 7.69/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.69/1.51  --bmc1_ucm_relax_model                  4
% 7.69/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.69/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.69/1.51  --bmc1_ucm_layered_model                none
% 7.69/1.51  --bmc1_ucm_max_lemma_size               10
% 7.69/1.51  
% 7.69/1.51  ------ AIG Options
% 7.69/1.51  
% 7.69/1.51  --aig_mode                              false
% 7.69/1.51  
% 7.69/1.51  ------ Instantiation Options
% 7.69/1.51  
% 7.69/1.51  --instantiation_flag                    true
% 7.69/1.51  --inst_sos_flag                         false
% 7.69/1.51  --inst_sos_phase                        true
% 7.69/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.69/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.69/1.51  --inst_lit_sel_side                     num_symb
% 7.69/1.51  --inst_solver_per_active                1400
% 7.69/1.51  --inst_solver_calls_frac                1.
% 7.69/1.51  --inst_passive_queue_type               priority_queues
% 7.69/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.69/1.51  --inst_passive_queues_freq              [25;2]
% 7.69/1.51  --inst_dismatching                      true
% 7.69/1.51  --inst_eager_unprocessed_to_passive     true
% 7.69/1.51  --inst_prop_sim_given                   true
% 7.69/1.51  --inst_prop_sim_new                     false
% 7.69/1.51  --inst_subs_new                         false
% 7.69/1.51  --inst_eq_res_simp                      false
% 7.69/1.51  --inst_subs_given                       false
% 7.69/1.51  --inst_orphan_elimination               true
% 7.69/1.51  --inst_learning_loop_flag               true
% 7.69/1.51  --inst_learning_start                   3000
% 7.69/1.51  --inst_learning_factor                  2
% 7.69/1.51  --inst_start_prop_sim_after_learn       3
% 7.69/1.51  --inst_sel_renew                        solver
% 7.69/1.51  --inst_lit_activity_flag                true
% 7.69/1.51  --inst_restr_to_given                   false
% 7.69/1.51  --inst_activity_threshold               500
% 7.69/1.51  --inst_out_proof                        true
% 7.69/1.51  
% 7.69/1.51  ------ Resolution Options
% 7.69/1.51  
% 7.69/1.51  --resolution_flag                       true
% 7.69/1.51  --res_lit_sel                           adaptive
% 7.69/1.51  --res_lit_sel_side                      none
% 7.69/1.51  --res_ordering                          kbo
% 7.69/1.51  --res_to_prop_solver                    active
% 7.69/1.51  --res_prop_simpl_new                    false
% 7.69/1.51  --res_prop_simpl_given                  true
% 7.69/1.51  --res_passive_queue_type                priority_queues
% 7.69/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.69/1.51  --res_passive_queues_freq               [15;5]
% 7.69/1.51  --res_forward_subs                      full
% 7.69/1.51  --res_backward_subs                     full
% 7.69/1.51  --res_forward_subs_resolution           true
% 7.69/1.51  --res_backward_subs_resolution          true
% 7.69/1.51  --res_orphan_elimination                true
% 7.69/1.51  --res_time_limit                        2.
% 7.69/1.51  --res_out_proof                         true
% 7.69/1.51  
% 7.69/1.51  ------ Superposition Options
% 7.69/1.51  
% 7.69/1.51  --superposition_flag                    true
% 7.69/1.51  --sup_passive_queue_type                priority_queues
% 7.69/1.51  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.69/1.51  --sup_passive_queues_freq               [1;4]
% 7.69/1.51  --demod_completeness_check              fast
% 7.69/1.51  --demod_use_ground                      true
% 7.69/1.51  --sup_to_prop_solver                    passive
% 7.69/1.51  --sup_prop_simpl_new                    true
% 7.69/1.51  --sup_prop_simpl_given                  true
% 7.69/1.51  --sup_fun_splitting                     false
% 7.69/1.51  --sup_smt_interval                      50000
% 7.69/1.51  
% 7.69/1.51  ------ Superposition Simplification Setup
% 7.69/1.51  
% 7.69/1.51  --sup_indices_passive                   []
% 7.69/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.69/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.69/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.69/1.51  --sup_full_bw                           [BwDemod]
% 7.69/1.51  --sup_immed_triv                        [TrivRules]
% 7.69/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.69/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.69/1.51  --sup_immed_bw_main                     []
% 7.69/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.69/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.69/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.69/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.69/1.51  
% 7.69/1.51  ------ Combination Options
% 7.69/1.51  
% 7.69/1.51  --comb_res_mult                         3
% 7.69/1.51  --comb_sup_mult                         2
% 7.69/1.51  --comb_inst_mult                        10
% 7.69/1.51  
% 7.69/1.51  ------ Debug Options
% 7.69/1.51  
% 7.69/1.51  --dbg_backtrace                         false
% 7.69/1.51  --dbg_dump_prop_clauses                 false
% 7.69/1.51  --dbg_dump_prop_clauses_file            -
% 7.69/1.51  --dbg_out_stat                          false
% 7.69/1.51  
% 7.69/1.51  
% 7.69/1.51  
% 7.69/1.51  
% 7.69/1.51  ------ Proving...
% 7.69/1.51  
% 7.69/1.51  
% 7.69/1.51  % SZS status Theorem for theBenchmark.p
% 7.69/1.51  
% 7.69/1.51   Resolution empty clause
% 7.69/1.51  
% 7.69/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.69/1.51  
% 7.69/1.51  fof(f7,axiom,(
% 7.69/1.51    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0),
% 7.69/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f22,plain,(
% 7.69/1.51    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0) )),
% 7.69/1.51    inference(cnf_transformation,[],[f7])).
% 7.69/1.51  
% 7.69/1.51  fof(f6,axiom,(
% 7.69/1.51    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.69/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f21,plain,(
% 7.69/1.51    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.69/1.51    inference(cnf_transformation,[],[f6])).
% 7.69/1.51  
% 7.69/1.51  fof(f5,axiom,(
% 7.69/1.51    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 7.69/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f20,plain,(
% 7.69/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 7.69/1.51    inference(cnf_transformation,[],[f5])).
% 7.69/1.51  
% 7.69/1.51  fof(f10,axiom,(
% 7.69/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.69/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f25,plain,(
% 7.69/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 7.69/1.51    inference(cnf_transformation,[],[f10])).
% 7.69/1.51  
% 7.69/1.51  fof(f29,plain,(
% 7.69/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = k1_xboole_0) )),
% 7.69/1.51    inference(definition_unfolding,[],[f20,f25])).
% 7.69/1.51  
% 7.69/1.51  fof(f4,axiom,(
% 7.69/1.51    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.69/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f19,plain,(
% 7.69/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.69/1.51    inference(cnf_transformation,[],[f4])).
% 7.69/1.51  
% 7.69/1.51  fof(f28,plain,(
% 7.69/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2)))) )),
% 7.69/1.51    inference(definition_unfolding,[],[f19,f25])).
% 7.69/1.51  
% 7.69/1.51  fof(f9,axiom,(
% 7.69/1.51    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.69/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f24,plain,(
% 7.69/1.51    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.69/1.51    inference(cnf_transformation,[],[f9])).
% 7.69/1.51  
% 7.69/1.51  fof(f8,axiom,(
% 7.69/1.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.69/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f23,plain,(
% 7.69/1.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.69/1.51    inference(cnf_transformation,[],[f8])).
% 7.69/1.51  
% 7.69/1.51  fof(f1,axiom,(
% 7.69/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.69/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f16,plain,(
% 7.69/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.69/1.51    inference(cnf_transformation,[],[f1])).
% 7.69/1.51  
% 7.69/1.51  fof(f3,axiom,(
% 7.69/1.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.69/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f18,plain,(
% 7.69/1.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.69/1.51    inference(cnf_transformation,[],[f3])).
% 7.69/1.51  
% 7.69/1.51  fof(f2,axiom,(
% 7.69/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.69/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f17,plain,(
% 7.69/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 7.69/1.51    inference(cnf_transformation,[],[f2])).
% 7.69/1.51  
% 7.69/1.51  fof(f27,plain,(
% 7.69/1.51    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k3_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 7.69/1.51    inference(definition_unfolding,[],[f17,f25,f25])).
% 7.69/1.51  
% 7.69/1.51  fof(f11,conjecture,(
% 7.69/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.69/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.69/1.51  
% 7.69/1.51  fof(f12,negated_conjecture,(
% 7.69/1.51    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.69/1.51    inference(negated_conjecture,[],[f11])).
% 7.69/1.51  
% 7.69/1.51  fof(f13,plain,(
% 7.69/1.51    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 7.69/1.51    inference(ennf_transformation,[],[f12])).
% 7.69/1.51  
% 7.69/1.51  fof(f14,plain,(
% 7.69/1.51    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 7.69/1.51    introduced(choice_axiom,[])).
% 7.69/1.51  
% 7.69/1.51  fof(f15,plain,(
% 7.69/1.51    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 7.69/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 7.69/1.51  
% 7.69/1.51  fof(f26,plain,(
% 7.69/1.51    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 7.69/1.51    inference(cnf_transformation,[],[f15])).
% 7.69/1.51  
% 7.69/1.51  fof(f30,plain,(
% 7.69/1.51    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.69/1.51    inference(definition_unfolding,[],[f26,f25])).
% 7.69/1.51  
% 7.69/1.51  cnf(c_6,plain,
% 7.69/1.51      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.69/1.51      inference(cnf_transformation,[],[f22]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_5,plain,
% 7.69/1.51      ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 7.69/1.51      inference(cnf_transformation,[],[f21]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_4,plain,
% 7.69/1.51      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.69/1.51      inference(cnf_transformation,[],[f29]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_217,plain,
% 7.69/1.51      ( k3_xboole_0(X0,k4_xboole_0(X1,k5_xboole_0(k5_xboole_0(k3_xboole_0(X0,X1),X2),k3_xboole_0(k3_xboole_0(X0,X1),X2)))) = k1_xboole_0 ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_5,c_4]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_3,plain,
% 7.69/1.51      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k3_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.69/1.51      inference(cnf_transformation,[],[f28]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1157,plain,
% 7.69/1.51      ( k3_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k3_xboole_0(X0,X1)),X2)) = k1_xboole_0 ),
% 7.69/1.51      inference(demodulation,[status(thm)],[c_217,c_3]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1170,plain,
% 7.69/1.51      ( k3_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1)) = k1_xboole_0 ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_6,c_1157]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1215,plain,
% 7.69/1.51      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.69/1.51      inference(demodulation,[status(thm)],[c_1170,c_6]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_8,plain,
% 7.69/1.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.69/1.51      inference(cnf_transformation,[],[f24]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_7,plain,
% 7.69/1.51      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.69/1.51      inference(cnf_transformation,[],[f23]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_118,plain,
% 7.69/1.51      ( k4_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = k1_xboole_0 ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_7,c_4]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_235,plain,
% 7.69/1.51      ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(k5_xboole_0(X0,X1),k1_xboole_0)))) = k1_xboole_0 ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_8,c_118]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1898,plain,
% 7.69/1.51      ( k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k1_xboole_0 ),
% 7.69/1.51      inference(demodulation,[status(thm)],[c_235,c_7,c_1215]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1914,plain,
% 7.69/1.51      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)),X0),X1) = k1_xboole_0 ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_1898,c_3]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_7117,plain,
% 7.69/1.51      ( k4_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0),X0),k1_xboole_0) = k1_xboole_0 ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_1215,c_1914]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_7270,plain,
% 7.69/1.51      ( k4_xboole_0(k4_xboole_0(X0,X0),k1_xboole_0) = k1_xboole_0 ),
% 7.69/1.51      inference(light_normalisation,[status(thm)],[c_7117,c_7]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_0,plain,
% 7.69/1.51      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.69/1.51      inference(cnf_transformation,[],[f16]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_214,plain,
% 7.69/1.51      ( k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X1,k4_xboole_0(X0,X2)) ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_0,c_5]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_708,plain,
% 7.69/1.51      ( k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,k4_xboole_0(X0,X2)) ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_214,c_5]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_7356,plain,
% 7.69/1.51      ( k3_xboole_0(k4_xboole_0(X0,X0),k4_xboole_0(X1,k1_xboole_0)) = k3_xboole_0(X1,k1_xboole_0) ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_7270,c_708]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_2,plain,
% 7.69/1.51      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.69/1.51      inference(cnf_transformation,[],[f18]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_993,plain,
% 7.69/1.51      ( k3_xboole_0(k4_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X2,X1)) ),
% 7.69/1.51      inference(superposition,[status(thm)],[c_708,c_0]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_7364,plain,
% 7.69/1.51      ( k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k1_xboole_0 ),
% 7.69/1.51      inference(demodulation,[status(thm)],[c_7356,c_2,c_993,c_1215]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_1,plain,
% 7.69/1.51      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k3_xboole_0(X0,k4_xboole_0(X1,X0))) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
% 7.69/1.51      inference(cnf_transformation,[],[f27]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_7534,plain,
% 7.69/1.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 7.69/1.51      inference(demodulation,[status(thm)],[c_7364,c_1]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_7535,plain,
% 7.69/1.51      ( k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 7.69/1.51      inference(demodulation,[status(thm)],[c_7534,c_7]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_9,negated_conjecture,
% 7.69/1.51      ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
% 7.69/1.51      inference(cnf_transformation,[],[f30]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_24050,plain,
% 7.69/1.51      ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
% 7.69/1.51      inference(demodulation,[status(thm)],[c_7535,c_9]) ).
% 7.69/1.51  
% 7.69/1.51  cnf(c_24055,plain,
% 7.69/1.51      ( $false ),
% 7.69/1.51      inference(equality_resolution_simp,[status(thm)],[c_24050]) ).
% 7.69/1.51  
% 7.69/1.51  
% 7.69/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.69/1.51  
% 7.69/1.51  ------                               Statistics
% 7.69/1.51  
% 7.69/1.51  ------ Selected
% 7.69/1.51  
% 7.69/1.51  total_time:                             0.726
% 7.69/1.51  
%------------------------------------------------------------------------------
