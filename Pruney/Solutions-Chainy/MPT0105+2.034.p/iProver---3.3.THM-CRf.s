%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:16 EST 2020

% Result     : Theorem 3.05s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 136 expanded)
%              Number of clauses        :   20 (  30 expanded)
%              Number of leaves         :   12 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :   55 ( 137 expanded)
%              Number of equality atoms :   54 ( 136 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f18,f22])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f22])).

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))))) ),
    inference(definition_unfolding,[],[f23,f29,f22])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f24,f22,f29])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f21,f29])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) ),
    inference(definition_unfolding,[],[f17,f22,f29])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f19,f29,f29])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f12,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f12])).

fof(f14,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f13])).

fof(f15,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f28,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f36,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f28,f29])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_34,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1,c_3])).

cnf(c_5,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_43,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(light_normalisation,[status(thm)],[c_6,c_4])).

cnf(c_0,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_48,plain,
    ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(light_normalisation,[status(thm)],[c_0,c_43])).

cnf(c_51,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(demodulation,[status(thm)],[c_5,c_43,c_48])).

cnf(c_1001,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_34,c_51])).

cnf(c_1063,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_1001,c_3,c_34])).

cnf(c_2,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1182,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(demodulation,[status(thm)],[c_1063,c_2])).

cnf(c_1183,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_1182,c_34])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_1184,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_1183,c_7])).

cnf(c_9,negated_conjecture,
    ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_12537,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(demodulation,[status(thm)],[c_1184,c_9])).

cnf(c_12538,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_12537])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:05:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.05/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.03  
% 3.05/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.05/1.03  
% 3.05/1.03  ------  iProver source info
% 3.05/1.03  
% 3.05/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.05/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.05/1.03  git: non_committed_changes: false
% 3.05/1.03  git: last_make_outside_of_git: false
% 3.05/1.03  
% 3.05/1.03  ------ 
% 3.05/1.03  
% 3.05/1.03  ------ Input Options
% 3.05/1.03  
% 3.05/1.03  --out_options                           all
% 3.05/1.03  --tptp_safe_out                         true
% 3.05/1.03  --problem_path                          ""
% 3.05/1.03  --include_path                          ""
% 3.05/1.03  --clausifier                            res/vclausify_rel
% 3.05/1.03  --clausifier_options                    --mode clausify
% 3.05/1.03  --stdin                                 false
% 3.05/1.03  --stats_out                             sel
% 3.05/1.03  
% 3.05/1.03  ------ General Options
% 3.05/1.03  
% 3.05/1.03  --fof                                   false
% 3.05/1.03  --time_out_real                         604.97
% 3.05/1.03  --time_out_virtual                      -1.
% 3.05/1.03  --symbol_type_check                     false
% 3.05/1.03  --clausify_out                          false
% 3.05/1.03  --sig_cnt_out                           false
% 3.05/1.03  --trig_cnt_out                          false
% 3.05/1.03  --trig_cnt_out_tolerance                1.
% 3.05/1.03  --trig_cnt_out_sk_spl                   false
% 3.05/1.03  --abstr_cl_out                          false
% 3.05/1.03  
% 3.05/1.03  ------ Global Options
% 3.05/1.03  
% 3.05/1.03  --schedule                              none
% 3.05/1.03  --add_important_lit                     false
% 3.05/1.03  --prop_solver_per_cl                    1000
% 3.05/1.03  --min_unsat_core                        false
% 3.05/1.03  --soft_assumptions                      false
% 3.05/1.03  --soft_lemma_size                       3
% 3.05/1.03  --prop_impl_unit_size                   0
% 3.05/1.03  --prop_impl_unit                        []
% 3.05/1.03  --share_sel_clauses                     true
% 3.05/1.03  --reset_solvers                         false
% 3.05/1.03  --bc_imp_inh                            [conj_cone]
% 3.05/1.03  --conj_cone_tolerance                   3.
% 3.05/1.03  --extra_neg_conj                        none
% 3.05/1.03  --large_theory_mode                     true
% 3.05/1.03  --prolific_symb_bound                   200
% 3.05/1.03  --lt_threshold                          2000
% 3.05/1.03  --clause_weak_htbl                      true
% 3.05/1.03  --gc_record_bc_elim                     false
% 3.05/1.03  
% 3.05/1.03  ------ Preprocessing Options
% 3.05/1.03  
% 3.05/1.03  --preprocessing_flag                    true
% 3.05/1.03  --time_out_prep_mult                    0.1
% 3.05/1.03  --splitting_mode                        input
% 3.05/1.03  --splitting_grd                         true
% 3.05/1.03  --splitting_cvd                         false
% 3.05/1.03  --splitting_cvd_svl                     false
% 3.05/1.03  --splitting_nvd                         32
% 3.05/1.03  --sub_typing                            true
% 3.05/1.03  --prep_gs_sim                           false
% 3.05/1.03  --prep_unflatten                        true
% 3.05/1.03  --prep_res_sim                          true
% 3.05/1.03  --prep_upred                            true
% 3.05/1.03  --prep_sem_filter                       exhaustive
% 3.05/1.03  --prep_sem_filter_out                   false
% 3.05/1.03  --pred_elim                             false
% 3.05/1.03  --res_sim_input                         true
% 3.05/1.03  --eq_ax_congr_red                       true
% 3.05/1.03  --pure_diseq_elim                       true
% 3.05/1.03  --brand_transform                       false
% 3.05/1.03  --non_eq_to_eq                          false
% 3.05/1.03  --prep_def_merge                        true
% 3.05/1.03  --prep_def_merge_prop_impl              false
% 3.05/1.03  --prep_def_merge_mbd                    true
% 3.05/1.03  --prep_def_merge_tr_red                 false
% 3.05/1.03  --prep_def_merge_tr_cl                  false
% 3.05/1.03  --smt_preprocessing                     true
% 3.05/1.03  --smt_ac_axioms                         fast
% 3.05/1.03  --preprocessed_out                      false
% 3.05/1.03  --preprocessed_stats                    false
% 3.05/1.03  
% 3.05/1.03  ------ Abstraction refinement Options
% 3.05/1.03  
% 3.05/1.03  --abstr_ref                             []
% 3.05/1.03  --abstr_ref_prep                        false
% 3.05/1.03  --abstr_ref_until_sat                   false
% 3.05/1.03  --abstr_ref_sig_restrict                funpre
% 3.05/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/1.03  --abstr_ref_under                       []
% 3.05/1.03  
% 3.05/1.03  ------ SAT Options
% 3.05/1.03  
% 3.05/1.03  --sat_mode                              false
% 3.05/1.03  --sat_fm_restart_options                ""
% 3.05/1.03  --sat_gr_def                            false
% 3.05/1.03  --sat_epr_types                         true
% 3.05/1.03  --sat_non_cyclic_types                  false
% 3.05/1.03  --sat_finite_models                     false
% 3.05/1.03  --sat_fm_lemmas                         false
% 3.05/1.03  --sat_fm_prep                           false
% 3.05/1.03  --sat_fm_uc_incr                        true
% 3.05/1.03  --sat_out_model                         small
% 3.05/1.03  --sat_out_clauses                       false
% 3.05/1.03  
% 3.05/1.03  ------ QBF Options
% 3.05/1.03  
% 3.05/1.03  --qbf_mode                              false
% 3.05/1.03  --qbf_elim_univ                         false
% 3.05/1.03  --qbf_dom_inst                          none
% 3.05/1.03  --qbf_dom_pre_inst                      false
% 3.05/1.03  --qbf_sk_in                             false
% 3.05/1.03  --qbf_pred_elim                         true
% 3.05/1.03  --qbf_split                             512
% 3.05/1.03  
% 3.05/1.03  ------ BMC1 Options
% 3.05/1.03  
% 3.05/1.03  --bmc1_incremental                      false
% 3.05/1.03  --bmc1_axioms                           reachable_all
% 3.05/1.03  --bmc1_min_bound                        0
% 3.05/1.03  --bmc1_max_bound                        -1
% 3.05/1.03  --bmc1_max_bound_default                -1
% 3.05/1.03  --bmc1_symbol_reachability              true
% 3.05/1.03  --bmc1_property_lemmas                  false
% 3.05/1.03  --bmc1_k_induction                      false
% 3.05/1.03  --bmc1_non_equiv_states                 false
% 3.05/1.03  --bmc1_deadlock                         false
% 3.05/1.03  --bmc1_ucm                              false
% 3.05/1.03  --bmc1_add_unsat_core                   none
% 3.05/1.03  --bmc1_unsat_core_children              false
% 3.05/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/1.03  --bmc1_out_stat                         full
% 3.05/1.03  --bmc1_ground_init                      false
% 3.05/1.03  --bmc1_pre_inst_next_state              false
% 3.05/1.03  --bmc1_pre_inst_state                   false
% 3.05/1.03  --bmc1_pre_inst_reach_state             false
% 3.05/1.03  --bmc1_out_unsat_core                   false
% 3.05/1.03  --bmc1_aig_witness_out                  false
% 3.05/1.03  --bmc1_verbose                          false
% 3.05/1.03  --bmc1_dump_clauses_tptp                false
% 3.05/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.05/1.03  --bmc1_dump_file                        -
% 3.05/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.05/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.05/1.03  --bmc1_ucm_extend_mode                  1
% 3.05/1.03  --bmc1_ucm_init_mode                    2
% 3.05/1.03  --bmc1_ucm_cone_mode                    none
% 3.05/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.05/1.03  --bmc1_ucm_relax_model                  4
% 3.05/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.05/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/1.03  --bmc1_ucm_layered_model                none
% 3.05/1.03  --bmc1_ucm_max_lemma_size               10
% 3.05/1.03  
% 3.05/1.03  ------ AIG Options
% 3.05/1.03  
% 3.05/1.03  --aig_mode                              false
% 3.05/1.03  
% 3.05/1.03  ------ Instantiation Options
% 3.05/1.03  
% 3.05/1.03  --instantiation_flag                    true
% 3.05/1.03  --inst_sos_flag                         false
% 3.05/1.03  --inst_sos_phase                        true
% 3.05/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/1.03  --inst_lit_sel_side                     num_symb
% 3.05/1.03  --inst_solver_per_active                1400
% 3.05/1.03  --inst_solver_calls_frac                1.
% 3.05/1.03  --inst_passive_queue_type               priority_queues
% 3.05/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/1.03  --inst_passive_queues_freq              [25;2]
% 3.05/1.03  --inst_dismatching                      true
% 3.05/1.03  --inst_eager_unprocessed_to_passive     true
% 3.05/1.03  --inst_prop_sim_given                   true
% 3.05/1.03  --inst_prop_sim_new                     false
% 3.05/1.03  --inst_subs_new                         false
% 3.05/1.03  --inst_eq_res_simp                      false
% 3.05/1.03  --inst_subs_given                       false
% 3.05/1.03  --inst_orphan_elimination               true
% 3.05/1.03  --inst_learning_loop_flag               true
% 3.05/1.03  --inst_learning_start                   3000
% 3.05/1.03  --inst_learning_factor                  2
% 3.05/1.03  --inst_start_prop_sim_after_learn       3
% 3.05/1.03  --inst_sel_renew                        solver
% 3.05/1.03  --inst_lit_activity_flag                true
% 3.05/1.03  --inst_restr_to_given                   false
% 3.05/1.03  --inst_activity_threshold               500
% 3.05/1.03  --inst_out_proof                        true
% 3.05/1.03  
% 3.05/1.03  ------ Resolution Options
% 3.05/1.03  
% 3.05/1.03  --resolution_flag                       true
% 3.05/1.03  --res_lit_sel                           adaptive
% 3.05/1.03  --res_lit_sel_side                      none
% 3.05/1.03  --res_ordering                          kbo
% 3.05/1.03  --res_to_prop_solver                    active
% 3.05/1.03  --res_prop_simpl_new                    false
% 3.05/1.03  --res_prop_simpl_given                  true
% 3.05/1.03  --res_passive_queue_type                priority_queues
% 3.05/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/1.03  --res_passive_queues_freq               [15;5]
% 3.05/1.03  --res_forward_subs                      full
% 3.05/1.03  --res_backward_subs                     full
% 3.05/1.03  --res_forward_subs_resolution           true
% 3.05/1.03  --res_backward_subs_resolution          true
% 3.05/1.03  --res_orphan_elimination                true
% 3.05/1.03  --res_time_limit                        2.
% 3.05/1.03  --res_out_proof                         true
% 3.05/1.03  
% 3.05/1.03  ------ Superposition Options
% 3.05/1.03  
% 3.05/1.03  --superposition_flag                    true
% 3.05/1.03  --sup_passive_queue_type                priority_queues
% 3.05/1.03  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/1.03  --sup_passive_queues_freq               [1;4]
% 3.05/1.03  --demod_completeness_check              fast
% 3.05/1.03  --demod_use_ground                      true
% 3.05/1.03  --sup_to_prop_solver                    passive
% 3.05/1.03  --sup_prop_simpl_new                    true
% 3.05/1.03  --sup_prop_simpl_given                  true
% 3.05/1.03  --sup_fun_splitting                     false
% 3.05/1.03  --sup_smt_interval                      50000
% 3.05/1.03  
% 3.05/1.03  ------ Superposition Simplification Setup
% 3.05/1.03  
% 3.05/1.03  --sup_indices_passive                   []
% 3.05/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.03  --sup_full_bw                           [BwDemod]
% 3.05/1.03  --sup_immed_triv                        [TrivRules]
% 3.05/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.03  --sup_immed_bw_main                     []
% 3.05/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.03  
% 3.05/1.03  ------ Combination Options
% 3.05/1.03  
% 3.05/1.03  --comb_res_mult                         3
% 3.05/1.03  --comb_sup_mult                         2
% 3.05/1.03  --comb_inst_mult                        10
% 3.05/1.03  
% 3.05/1.03  ------ Debug Options
% 3.05/1.03  
% 3.05/1.03  --dbg_backtrace                         false
% 3.05/1.03  --dbg_dump_prop_clauses                 false
% 3.05/1.03  --dbg_dump_prop_clauses_file            -
% 3.05/1.03  --dbg_out_stat                          false
% 3.05/1.03  ------ Parsing...
% 3.05/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.05/1.03  
% 3.05/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.05/1.03  
% 3.05/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.05/1.03  
% 3.05/1.03  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.05/1.03  ------ Proving...
% 3.05/1.03  ------ Problem Properties 
% 3.05/1.03  
% 3.05/1.03  
% 3.05/1.03  clauses                                 10
% 3.05/1.03  conjectures                             1
% 3.05/1.03  EPR                                     0
% 3.05/1.03  Horn                                    10
% 3.05/1.03  unary                                   10
% 3.05/1.03  binary                                  0
% 3.05/1.03  lits                                    10
% 3.05/1.03  lits eq                                 10
% 3.05/1.03  fd_pure                                 0
% 3.05/1.03  fd_pseudo                               0
% 3.05/1.03  fd_cond                                 0
% 3.05/1.03  fd_pseudo_cond                          0
% 3.05/1.03  AC symbols                              0
% 3.05/1.03  
% 3.05/1.03  ------ Input Options Time Limit: Unbounded
% 3.05/1.03  
% 3.05/1.03  
% 3.05/1.03  ------ 
% 3.05/1.03  Current options:
% 3.05/1.03  ------ 
% 3.05/1.03  
% 3.05/1.03  ------ Input Options
% 3.05/1.03  
% 3.05/1.03  --out_options                           all
% 3.05/1.03  --tptp_safe_out                         true
% 3.05/1.03  --problem_path                          ""
% 3.05/1.03  --include_path                          ""
% 3.05/1.03  --clausifier                            res/vclausify_rel
% 3.05/1.03  --clausifier_options                    --mode clausify
% 3.05/1.03  --stdin                                 false
% 3.05/1.03  --stats_out                             sel
% 3.05/1.03  
% 3.05/1.03  ------ General Options
% 3.05/1.03  
% 3.05/1.03  --fof                                   false
% 3.05/1.03  --time_out_real                         604.97
% 3.05/1.03  --time_out_virtual                      -1.
% 3.05/1.03  --symbol_type_check                     false
% 3.05/1.03  --clausify_out                          false
% 3.05/1.03  --sig_cnt_out                           false
% 3.05/1.03  --trig_cnt_out                          false
% 3.05/1.03  --trig_cnt_out_tolerance                1.
% 3.05/1.03  --trig_cnt_out_sk_spl                   false
% 3.05/1.03  --abstr_cl_out                          false
% 3.05/1.03  
% 3.05/1.03  ------ Global Options
% 3.05/1.03  
% 3.05/1.03  --schedule                              none
% 3.05/1.03  --add_important_lit                     false
% 3.05/1.03  --prop_solver_per_cl                    1000
% 3.05/1.03  --min_unsat_core                        false
% 3.05/1.03  --soft_assumptions                      false
% 3.05/1.03  --soft_lemma_size                       3
% 3.05/1.03  --prop_impl_unit_size                   0
% 3.05/1.03  --prop_impl_unit                        []
% 3.05/1.03  --share_sel_clauses                     true
% 3.05/1.03  --reset_solvers                         false
% 3.05/1.03  --bc_imp_inh                            [conj_cone]
% 3.05/1.03  --conj_cone_tolerance                   3.
% 3.05/1.03  --extra_neg_conj                        none
% 3.05/1.03  --large_theory_mode                     true
% 3.05/1.03  --prolific_symb_bound                   200
% 3.05/1.03  --lt_threshold                          2000
% 3.05/1.03  --clause_weak_htbl                      true
% 3.05/1.03  --gc_record_bc_elim                     false
% 3.05/1.03  
% 3.05/1.03  ------ Preprocessing Options
% 3.05/1.03  
% 3.05/1.03  --preprocessing_flag                    true
% 3.05/1.03  --time_out_prep_mult                    0.1
% 3.05/1.03  --splitting_mode                        input
% 3.05/1.03  --splitting_grd                         true
% 3.05/1.03  --splitting_cvd                         false
% 3.05/1.03  --splitting_cvd_svl                     false
% 3.05/1.03  --splitting_nvd                         32
% 3.05/1.03  --sub_typing                            true
% 3.05/1.03  --prep_gs_sim                           false
% 3.05/1.03  --prep_unflatten                        true
% 3.05/1.03  --prep_res_sim                          true
% 3.05/1.03  --prep_upred                            true
% 3.05/1.03  --prep_sem_filter                       exhaustive
% 3.05/1.03  --prep_sem_filter_out                   false
% 3.05/1.03  --pred_elim                             false
% 3.05/1.03  --res_sim_input                         true
% 3.05/1.03  --eq_ax_congr_red                       true
% 3.05/1.03  --pure_diseq_elim                       true
% 3.05/1.03  --brand_transform                       false
% 3.05/1.03  --non_eq_to_eq                          false
% 3.05/1.03  --prep_def_merge                        true
% 3.05/1.03  --prep_def_merge_prop_impl              false
% 3.05/1.03  --prep_def_merge_mbd                    true
% 3.05/1.03  --prep_def_merge_tr_red                 false
% 3.05/1.03  --prep_def_merge_tr_cl                  false
% 3.05/1.03  --smt_preprocessing                     true
% 3.05/1.03  --smt_ac_axioms                         fast
% 3.05/1.03  --preprocessed_out                      false
% 3.05/1.03  --preprocessed_stats                    false
% 3.05/1.03  
% 3.05/1.03  ------ Abstraction refinement Options
% 3.05/1.03  
% 3.05/1.03  --abstr_ref                             []
% 3.05/1.03  --abstr_ref_prep                        false
% 3.05/1.03  --abstr_ref_until_sat                   false
% 3.05/1.03  --abstr_ref_sig_restrict                funpre
% 3.05/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.05/1.03  --abstr_ref_under                       []
% 3.05/1.03  
% 3.05/1.03  ------ SAT Options
% 3.05/1.03  
% 3.05/1.03  --sat_mode                              false
% 3.05/1.03  --sat_fm_restart_options                ""
% 3.05/1.03  --sat_gr_def                            false
% 3.05/1.03  --sat_epr_types                         true
% 3.05/1.03  --sat_non_cyclic_types                  false
% 3.05/1.03  --sat_finite_models                     false
% 3.05/1.03  --sat_fm_lemmas                         false
% 3.05/1.03  --sat_fm_prep                           false
% 3.05/1.03  --sat_fm_uc_incr                        true
% 3.05/1.03  --sat_out_model                         small
% 3.05/1.03  --sat_out_clauses                       false
% 3.05/1.03  
% 3.05/1.03  ------ QBF Options
% 3.05/1.03  
% 3.05/1.03  --qbf_mode                              false
% 3.05/1.03  --qbf_elim_univ                         false
% 3.05/1.03  --qbf_dom_inst                          none
% 3.05/1.03  --qbf_dom_pre_inst                      false
% 3.05/1.03  --qbf_sk_in                             false
% 3.05/1.03  --qbf_pred_elim                         true
% 3.05/1.03  --qbf_split                             512
% 3.05/1.03  
% 3.05/1.03  ------ BMC1 Options
% 3.05/1.03  
% 3.05/1.03  --bmc1_incremental                      false
% 3.05/1.03  --bmc1_axioms                           reachable_all
% 3.05/1.03  --bmc1_min_bound                        0
% 3.05/1.03  --bmc1_max_bound                        -1
% 3.05/1.03  --bmc1_max_bound_default                -1
% 3.05/1.03  --bmc1_symbol_reachability              true
% 3.05/1.03  --bmc1_property_lemmas                  false
% 3.05/1.03  --bmc1_k_induction                      false
% 3.05/1.03  --bmc1_non_equiv_states                 false
% 3.05/1.03  --bmc1_deadlock                         false
% 3.05/1.03  --bmc1_ucm                              false
% 3.05/1.03  --bmc1_add_unsat_core                   none
% 3.05/1.03  --bmc1_unsat_core_children              false
% 3.05/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.05/1.03  --bmc1_out_stat                         full
% 3.05/1.03  --bmc1_ground_init                      false
% 3.05/1.03  --bmc1_pre_inst_next_state              false
% 3.05/1.03  --bmc1_pre_inst_state                   false
% 3.05/1.03  --bmc1_pre_inst_reach_state             false
% 3.05/1.03  --bmc1_out_unsat_core                   false
% 3.05/1.03  --bmc1_aig_witness_out                  false
% 3.05/1.03  --bmc1_verbose                          false
% 3.05/1.03  --bmc1_dump_clauses_tptp                false
% 3.05/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.05/1.03  --bmc1_dump_file                        -
% 3.05/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.05/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.05/1.03  --bmc1_ucm_extend_mode                  1
% 3.05/1.03  --bmc1_ucm_init_mode                    2
% 3.05/1.03  --bmc1_ucm_cone_mode                    none
% 3.05/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.05/1.03  --bmc1_ucm_relax_model                  4
% 3.05/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.05/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.05/1.03  --bmc1_ucm_layered_model                none
% 3.05/1.03  --bmc1_ucm_max_lemma_size               10
% 3.05/1.03  
% 3.05/1.03  ------ AIG Options
% 3.05/1.03  
% 3.05/1.03  --aig_mode                              false
% 3.05/1.03  
% 3.05/1.03  ------ Instantiation Options
% 3.05/1.03  
% 3.05/1.03  --instantiation_flag                    true
% 3.05/1.03  --inst_sos_flag                         false
% 3.05/1.03  --inst_sos_phase                        true
% 3.05/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.05/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.05/1.03  --inst_lit_sel_side                     num_symb
% 3.05/1.03  --inst_solver_per_active                1400
% 3.05/1.03  --inst_solver_calls_frac                1.
% 3.05/1.03  --inst_passive_queue_type               priority_queues
% 3.05/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.05/1.03  --inst_passive_queues_freq              [25;2]
% 3.05/1.03  --inst_dismatching                      true
% 3.05/1.03  --inst_eager_unprocessed_to_passive     true
% 3.05/1.03  --inst_prop_sim_given                   true
% 3.05/1.03  --inst_prop_sim_new                     false
% 3.05/1.03  --inst_subs_new                         false
% 3.05/1.03  --inst_eq_res_simp                      false
% 3.05/1.03  --inst_subs_given                       false
% 3.05/1.03  --inst_orphan_elimination               true
% 3.05/1.03  --inst_learning_loop_flag               true
% 3.05/1.03  --inst_learning_start                   3000
% 3.05/1.03  --inst_learning_factor                  2
% 3.05/1.03  --inst_start_prop_sim_after_learn       3
% 3.05/1.03  --inst_sel_renew                        solver
% 3.05/1.03  --inst_lit_activity_flag                true
% 3.05/1.03  --inst_restr_to_given                   false
% 3.05/1.03  --inst_activity_threshold               500
% 3.05/1.03  --inst_out_proof                        true
% 3.05/1.03  
% 3.05/1.03  ------ Resolution Options
% 3.05/1.03  
% 3.05/1.03  --resolution_flag                       true
% 3.05/1.03  --res_lit_sel                           adaptive
% 3.05/1.03  --res_lit_sel_side                      none
% 3.05/1.03  --res_ordering                          kbo
% 3.05/1.03  --res_to_prop_solver                    active
% 3.05/1.03  --res_prop_simpl_new                    false
% 3.05/1.03  --res_prop_simpl_given                  true
% 3.05/1.03  --res_passive_queue_type                priority_queues
% 3.05/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.05/1.03  --res_passive_queues_freq               [15;5]
% 3.05/1.03  --res_forward_subs                      full
% 3.05/1.03  --res_backward_subs                     full
% 3.05/1.03  --res_forward_subs_resolution           true
% 3.05/1.03  --res_backward_subs_resolution          true
% 3.05/1.03  --res_orphan_elimination                true
% 3.05/1.03  --res_time_limit                        2.
% 3.05/1.03  --res_out_proof                         true
% 3.05/1.03  
% 3.05/1.03  ------ Superposition Options
% 3.05/1.03  
% 3.05/1.03  --superposition_flag                    true
% 3.05/1.03  --sup_passive_queue_type                priority_queues
% 3.05/1.03  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.05/1.03  --sup_passive_queues_freq               [1;4]
% 3.05/1.03  --demod_completeness_check              fast
% 3.05/1.03  --demod_use_ground                      true
% 3.05/1.03  --sup_to_prop_solver                    passive
% 3.05/1.03  --sup_prop_simpl_new                    true
% 3.05/1.03  --sup_prop_simpl_given                  true
% 3.05/1.03  --sup_fun_splitting                     false
% 3.05/1.03  --sup_smt_interval                      50000
% 3.05/1.03  
% 3.05/1.03  ------ Superposition Simplification Setup
% 3.05/1.03  
% 3.05/1.03  --sup_indices_passive                   []
% 3.05/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.05/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.05/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.03  --sup_full_bw                           [BwDemod]
% 3.05/1.03  --sup_immed_triv                        [TrivRules]
% 3.05/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.05/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.03  --sup_immed_bw_main                     []
% 3.05/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.05/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.05/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.05/1.03  
% 3.05/1.03  ------ Combination Options
% 3.05/1.03  
% 3.05/1.03  --comb_res_mult                         3
% 3.05/1.03  --comb_sup_mult                         2
% 3.05/1.03  --comb_inst_mult                        10
% 3.05/1.03  
% 3.05/1.03  ------ Debug Options
% 3.05/1.03  
% 3.05/1.03  --dbg_backtrace                         false
% 3.05/1.03  --dbg_dump_prop_clauses                 false
% 3.05/1.03  --dbg_dump_prop_clauses_file            -
% 3.05/1.03  --dbg_out_stat                          false
% 3.05/1.03  
% 3.05/1.03  
% 3.05/1.03  
% 3.05/1.03  
% 3.05/1.03  ------ Proving...
% 3.05/1.03  
% 3.05/1.03  
% 3.05/1.03  % SZS status Theorem for theBenchmark.p
% 3.05/1.03  
% 3.05/1.03   Resolution empty clause
% 3.05/1.03  
% 3.05/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.05/1.03  
% 3.05/1.03  fof(f2,axiom,(
% 3.05/1.03    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 3.05/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.03  
% 3.05/1.03  fof(f18,plain,(
% 3.05/1.03    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.05/1.03    inference(cnf_transformation,[],[f2])).
% 3.05/1.03  
% 3.05/1.03  fof(f6,axiom,(
% 3.05/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.05/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.03  
% 3.05/1.03  fof(f22,plain,(
% 3.05/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.05/1.03    inference(cnf_transformation,[],[f6])).
% 3.05/1.03  
% 3.05/1.03  fof(f31,plain,(
% 3.05/1.03    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 3.05/1.03    inference(definition_unfolding,[],[f18,f22])).
% 3.05/1.03  
% 3.05/1.03  fof(f4,axiom,(
% 3.05/1.03    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.05/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.03  
% 3.05/1.03  fof(f20,plain,(
% 3.05/1.03    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.05/1.03    inference(cnf_transformation,[],[f4])).
% 3.05/1.03  
% 3.05/1.03  fof(f7,axiom,(
% 3.05/1.03    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 3.05/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.03  
% 3.05/1.03  fof(f23,plain,(
% 3.05/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 3.05/1.03    inference(cnf_transformation,[],[f7])).
% 3.05/1.03  
% 3.05/1.03  fof(f11,axiom,(
% 3.05/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.05/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.03  
% 3.05/1.03  fof(f27,plain,(
% 3.05/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 3.05/1.03    inference(cnf_transformation,[],[f11])).
% 3.05/1.03  
% 3.05/1.03  fof(f29,plain,(
% 3.05/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.05/1.03    inference(definition_unfolding,[],[f27,f22])).
% 3.05/1.03  
% 3.05/1.03  fof(f34,plain,(
% 3.05/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))))) )),
% 3.05/1.03    inference(definition_unfolding,[],[f23,f29,f22])).
% 3.05/1.03  
% 3.05/1.03  fof(f8,axiom,(
% 3.05/1.03    ! [X0,X1,X2] : k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.05/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.03  
% 3.05/1.03  fof(f24,plain,(
% 3.05/1.03    ( ! [X2,X0,X1] : (k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.05/1.03    inference(cnf_transformation,[],[f8])).
% 3.05/1.03  
% 3.05/1.03  fof(f35,plain,(
% 3.05/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) )),
% 3.05/1.03    inference(definition_unfolding,[],[f24,f22,f29])).
% 3.05/1.03  
% 3.05/1.03  fof(f5,axiom,(
% 3.05/1.03    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 3.05/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.03  
% 3.05/1.03  fof(f21,plain,(
% 3.05/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 3.05/1.03    inference(cnf_transformation,[],[f5])).
% 3.05/1.03  
% 3.05/1.03  fof(f33,plain,(
% 3.05/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 3.05/1.03    inference(definition_unfolding,[],[f21,f29])).
% 3.05/1.03  
% 3.05/1.03  fof(f1,axiom,(
% 3.05/1.03    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 3.05/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.03  
% 3.05/1.03  fof(f17,plain,(
% 3.05/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 3.05/1.03    inference(cnf_transformation,[],[f1])).
% 3.05/1.03  
% 3.05/1.03  fof(f30,plain,(
% 3.05/1.03    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))))) )),
% 3.05/1.03    inference(definition_unfolding,[],[f17,f22,f29])).
% 3.05/1.03  
% 3.05/1.03  fof(f3,axiom,(
% 3.05/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.05/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.03  
% 3.05/1.03  fof(f19,plain,(
% 3.05/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.05/1.03    inference(cnf_transformation,[],[f3])).
% 3.05/1.03  
% 3.05/1.03  fof(f32,plain,(
% 3.05/1.03    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 3.05/1.03    inference(definition_unfolding,[],[f19,f29,f29])).
% 3.05/1.03  
% 3.05/1.03  fof(f9,axiom,(
% 3.05/1.03    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.05/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.03  
% 3.05/1.03  fof(f25,plain,(
% 3.05/1.03    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.05/1.03    inference(cnf_transformation,[],[f9])).
% 3.05/1.03  
% 3.05/1.03  fof(f12,conjecture,(
% 3.05/1.03    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.05/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.05/1.03  
% 3.05/1.03  fof(f13,negated_conjecture,(
% 3.05/1.03    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.05/1.03    inference(negated_conjecture,[],[f12])).
% 3.05/1.03  
% 3.05/1.03  fof(f14,plain,(
% 3.05/1.03    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.05/1.03    inference(ennf_transformation,[],[f13])).
% 3.05/1.03  
% 3.05/1.03  fof(f15,plain,(
% 3.05/1.03    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 3.05/1.03    introduced(choice_axiom,[])).
% 3.05/1.03  
% 3.05/1.03  fof(f16,plain,(
% 3.05/1.03    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 3.05/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 3.05/1.03  
% 3.05/1.03  fof(f28,plain,(
% 3.05/1.03    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 3.05/1.03    inference(cnf_transformation,[],[f16])).
% 3.05/1.03  
% 3.05/1.03  fof(f36,plain,(
% 3.05/1.03    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 3.05/1.03    inference(definition_unfolding,[],[f28,f29])).
% 3.05/1.03  
% 3.05/1.03  cnf(c_1,plain,
% 3.05/1.03      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 3.05/1.03      inference(cnf_transformation,[],[f31]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_3,plain,
% 3.05/1.03      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.05/1.03      inference(cnf_transformation,[],[f20]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_34,plain,
% 3.05/1.03      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.05/1.03      inference(light_normalisation,[status(thm)],[c_1,c_3]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_5,plain,
% 3.05/1.03      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 3.05/1.03      inference(cnf_transformation,[],[f34]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_6,plain,
% 3.05/1.03      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
% 3.05/1.03      inference(cnf_transformation,[],[f35]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_4,plain,
% 3.05/1.03      ( k4_xboole_0(X0,k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.05/1.03      inference(cnf_transformation,[],[f33]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_43,plain,
% 3.05/1.03      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 3.05/1.03      inference(light_normalisation,[status(thm)],[c_6,c_4]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_0,plain,
% 3.05/1.03      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 3.05/1.03      inference(cnf_transformation,[],[f30]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_48,plain,
% 3.05/1.03      ( k5_xboole_0(k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)),k4_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
% 3.05/1.03      inference(light_normalisation,[status(thm)],[c_0,c_43]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_51,plain,
% 3.05/1.03      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(X0,X2)))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 3.05/1.03      inference(demodulation,[status(thm)],[c_5,c_43,c_48]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_1001,plain,
% 3.05/1.03      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.05/1.03      inference(superposition,[status(thm)],[c_34,c_51]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_1063,plain,
% 3.05/1.03      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 3.05/1.03      inference(demodulation,[status(thm)],[c_1001,c_3,c_34]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_2,plain,
% 3.05/1.03      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 3.05/1.03      inference(cnf_transformation,[],[f32]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_1182,plain,
% 3.05/1.03      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X0)) = k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 3.05/1.03      inference(demodulation,[status(thm)],[c_1063,c_2]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_1183,plain,
% 3.05/1.03      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k1_xboole_0) ),
% 3.05/1.03      inference(light_normalisation,[status(thm)],[c_1182,c_34]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_7,plain,
% 3.05/1.03      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.05/1.03      inference(cnf_transformation,[],[f25]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_1184,plain,
% 3.05/1.03      ( k5_xboole_0(k5_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 3.05/1.03      inference(demodulation,[status(thm)],[c_1183,c_7]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_9,negated_conjecture,
% 3.05/1.03      ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 3.05/1.03      inference(cnf_transformation,[],[f36]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_12537,plain,
% 3.05/1.03      ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
% 3.05/1.03      inference(demodulation,[status(thm)],[c_1184,c_9]) ).
% 3.05/1.03  
% 3.05/1.03  cnf(c_12538,plain,
% 3.05/1.03      ( $false ),
% 3.05/1.03      inference(equality_resolution_simp,[status(thm)],[c_12537]) ).
% 3.05/1.03  
% 3.05/1.03  
% 3.05/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.05/1.03  
% 3.05/1.03  ------                               Statistics
% 3.05/1.03  
% 3.05/1.03  ------ Selected
% 3.05/1.03  
% 3.05/1.03  total_time:                             0.464
% 3.05/1.03  
%------------------------------------------------------------------------------
