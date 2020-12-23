%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:31 EST 2020

% Result     : Theorem 7.87s
% Output     : CNFRefutation 7.87s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 432 expanded)
%              Number of clauses        :   33 ( 152 expanded)
%              Number of leaves         :   12 ( 118 expanded)
%              Depth                    :   16
%              Number of atoms          :   66 ( 433 expanded)
%              Number of equality atoms :   65 ( 432 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f26,f20])).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f22,f20,f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f19,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f19,f28])).

fof(f11,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f15,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f27,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f27,f20,f28])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f23,f20,f20])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_34,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_6,c_1])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_3,plain,
    ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_23,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))) = k1_xboole_0 ),
    inference(theory_normalisation,[status(thm)],[c_4,c_6,c_1,c_3,c_0])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_42,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_6])).

cnf(c_49,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_42])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_57,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_42,c_2])).

cnf(c_78,plain,
    ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_57,c_42])).

cnf(c_81,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_78,c_57])).

cnf(c_83,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_49,c_81])).

cnf(c_87,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_83])).

cnf(c_266,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_23,c_87])).

cnf(c_91,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_83])).

cnf(c_273,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_266,c_91])).

cnf(c_3070,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_34,c_273])).

cnf(c_31588,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_3070])).

cnf(c_8,negated_conjecture,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_21,negated_conjecture,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) != k5_xboole_0(sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_8,c_6,c_1,c_3,c_0])).

cnf(c_5,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_22,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(theory_normalisation,[status(thm)],[c_5,c_6,c_1,c_3,c_0])).

cnf(c_30,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_21,c_22])).

cnf(c_34393,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)))) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_31588,c_30])).

cnf(c_129,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_81,c_57])).

cnf(c_139,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) ),
    inference(superposition,[status(thm)],[c_129,c_22])).

cnf(c_142,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,X1)) ),
    inference(demodulation,[status(thm)],[c_139,c_129])).

cnf(c_143,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_142,c_7])).

cnf(c_34394,plain,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_34393,c_7,c_91,c_143])).

cnf(c_34395,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_34394])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n002.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 19:45:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 7.87/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.87/1.48  
% 7.87/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.87/1.48  
% 7.87/1.48  ------  iProver source info
% 7.87/1.48  
% 7.87/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.87/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.87/1.48  git: non_committed_changes: false
% 7.87/1.48  git: last_make_outside_of_git: false
% 7.87/1.48  
% 7.87/1.48  ------ 
% 7.87/1.48  
% 7.87/1.48  ------ Input Options
% 7.87/1.48  
% 7.87/1.48  --out_options                           all
% 7.87/1.48  --tptp_safe_out                         true
% 7.87/1.48  --problem_path                          ""
% 7.87/1.48  --include_path                          ""
% 7.87/1.48  --clausifier                            res/vclausify_rel
% 7.87/1.48  --clausifier_options                    --mode clausify
% 7.87/1.48  --stdin                                 false
% 7.87/1.48  --stats_out                             all
% 7.87/1.48  
% 7.87/1.48  ------ General Options
% 7.87/1.48  
% 7.87/1.48  --fof                                   false
% 7.87/1.48  --time_out_real                         305.
% 7.87/1.48  --time_out_virtual                      -1.
% 7.87/1.48  --symbol_type_check                     false
% 7.87/1.48  --clausify_out                          false
% 7.87/1.48  --sig_cnt_out                           false
% 7.87/1.48  --trig_cnt_out                          false
% 7.87/1.48  --trig_cnt_out_tolerance                1.
% 7.87/1.48  --trig_cnt_out_sk_spl                   false
% 7.87/1.48  --abstr_cl_out                          false
% 7.87/1.48  
% 7.87/1.48  ------ Global Options
% 7.87/1.48  
% 7.87/1.48  --schedule                              default
% 7.87/1.48  --add_important_lit                     false
% 7.87/1.48  --prop_solver_per_cl                    1000
% 7.87/1.48  --min_unsat_core                        false
% 7.87/1.48  --soft_assumptions                      false
% 7.87/1.48  --soft_lemma_size                       3
% 7.87/1.48  --prop_impl_unit_size                   0
% 7.87/1.48  --prop_impl_unit                        []
% 7.87/1.48  --share_sel_clauses                     true
% 7.87/1.48  --reset_solvers                         false
% 7.87/1.48  --bc_imp_inh                            [conj_cone]
% 7.87/1.48  --conj_cone_tolerance                   3.
% 7.87/1.48  --extra_neg_conj                        none
% 7.87/1.48  --large_theory_mode                     true
% 7.87/1.48  --prolific_symb_bound                   200
% 7.87/1.48  --lt_threshold                          2000
% 7.87/1.48  --clause_weak_htbl                      true
% 7.87/1.48  --gc_record_bc_elim                     false
% 7.87/1.48  
% 7.87/1.48  ------ Preprocessing Options
% 7.87/1.48  
% 7.87/1.48  --preprocessing_flag                    true
% 7.87/1.48  --time_out_prep_mult                    0.1
% 7.87/1.48  --splitting_mode                        input
% 7.87/1.48  --splitting_grd                         true
% 7.87/1.48  --splitting_cvd                         false
% 7.87/1.48  --splitting_cvd_svl                     false
% 7.87/1.48  --splitting_nvd                         32
% 7.87/1.48  --sub_typing                            true
% 7.87/1.48  --prep_gs_sim                           true
% 7.87/1.48  --prep_unflatten                        true
% 7.87/1.48  --prep_res_sim                          true
% 7.87/1.48  --prep_upred                            true
% 7.87/1.48  --prep_sem_filter                       exhaustive
% 7.87/1.48  --prep_sem_filter_out                   false
% 7.87/1.48  --pred_elim                             true
% 7.87/1.48  --res_sim_input                         true
% 7.87/1.48  --eq_ax_congr_red                       true
% 7.87/1.48  --pure_diseq_elim                       true
% 7.87/1.48  --brand_transform                       false
% 7.87/1.48  --non_eq_to_eq                          false
% 7.87/1.48  --prep_def_merge                        true
% 7.87/1.48  --prep_def_merge_prop_impl              false
% 7.87/1.48  --prep_def_merge_mbd                    true
% 7.87/1.48  --prep_def_merge_tr_red                 false
% 7.87/1.48  --prep_def_merge_tr_cl                  false
% 7.87/1.48  --smt_preprocessing                     true
% 7.87/1.48  --smt_ac_axioms                         fast
% 7.87/1.48  --preprocessed_out                      false
% 7.87/1.48  --preprocessed_stats                    false
% 7.87/1.48  
% 7.87/1.48  ------ Abstraction refinement Options
% 7.87/1.48  
% 7.87/1.48  --abstr_ref                             []
% 7.87/1.48  --abstr_ref_prep                        false
% 7.87/1.48  --abstr_ref_until_sat                   false
% 7.87/1.48  --abstr_ref_sig_restrict                funpre
% 7.87/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.87/1.48  --abstr_ref_under                       []
% 7.87/1.48  
% 7.87/1.48  ------ SAT Options
% 7.87/1.48  
% 7.87/1.48  --sat_mode                              false
% 7.87/1.48  --sat_fm_restart_options                ""
% 7.87/1.48  --sat_gr_def                            false
% 7.87/1.48  --sat_epr_types                         true
% 7.87/1.48  --sat_non_cyclic_types                  false
% 7.87/1.48  --sat_finite_models                     false
% 7.87/1.48  --sat_fm_lemmas                         false
% 7.87/1.48  --sat_fm_prep                           false
% 7.87/1.48  --sat_fm_uc_incr                        true
% 7.87/1.48  --sat_out_model                         small
% 7.87/1.48  --sat_out_clauses                       false
% 7.87/1.48  
% 7.87/1.48  ------ QBF Options
% 7.87/1.48  
% 7.87/1.48  --qbf_mode                              false
% 7.87/1.48  --qbf_elim_univ                         false
% 7.87/1.48  --qbf_dom_inst                          none
% 7.87/1.48  --qbf_dom_pre_inst                      false
% 7.87/1.48  --qbf_sk_in                             false
% 7.87/1.48  --qbf_pred_elim                         true
% 7.87/1.48  --qbf_split                             512
% 7.87/1.48  
% 7.87/1.48  ------ BMC1 Options
% 7.87/1.48  
% 7.87/1.48  --bmc1_incremental                      false
% 7.87/1.48  --bmc1_axioms                           reachable_all
% 7.87/1.48  --bmc1_min_bound                        0
% 7.87/1.48  --bmc1_max_bound                        -1
% 7.87/1.48  --bmc1_max_bound_default                -1
% 7.87/1.48  --bmc1_symbol_reachability              true
% 7.87/1.48  --bmc1_property_lemmas                  false
% 7.87/1.48  --bmc1_k_induction                      false
% 7.87/1.48  --bmc1_non_equiv_states                 false
% 7.87/1.48  --bmc1_deadlock                         false
% 7.87/1.48  --bmc1_ucm                              false
% 7.87/1.48  --bmc1_add_unsat_core                   none
% 7.87/1.48  --bmc1_unsat_core_children              false
% 7.87/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.87/1.48  --bmc1_out_stat                         full
% 7.87/1.48  --bmc1_ground_init                      false
% 7.87/1.48  --bmc1_pre_inst_next_state              false
% 7.87/1.48  --bmc1_pre_inst_state                   false
% 7.87/1.48  --bmc1_pre_inst_reach_state             false
% 7.87/1.48  --bmc1_out_unsat_core                   false
% 7.87/1.48  --bmc1_aig_witness_out                  false
% 7.87/1.48  --bmc1_verbose                          false
% 7.87/1.48  --bmc1_dump_clauses_tptp                false
% 7.87/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.87/1.48  --bmc1_dump_file                        -
% 7.87/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.87/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.87/1.48  --bmc1_ucm_extend_mode                  1
% 7.87/1.48  --bmc1_ucm_init_mode                    2
% 7.87/1.48  --bmc1_ucm_cone_mode                    none
% 7.87/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.87/1.48  --bmc1_ucm_relax_model                  4
% 7.87/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.87/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.87/1.48  --bmc1_ucm_layered_model                none
% 7.87/1.48  --bmc1_ucm_max_lemma_size               10
% 7.87/1.48  
% 7.87/1.48  ------ AIG Options
% 7.87/1.48  
% 7.87/1.48  --aig_mode                              false
% 7.87/1.48  
% 7.87/1.48  ------ Instantiation Options
% 7.87/1.48  
% 7.87/1.48  --instantiation_flag                    true
% 7.87/1.48  --inst_sos_flag                         false
% 7.87/1.48  --inst_sos_phase                        true
% 7.87/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.87/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.87/1.48  --inst_lit_sel_side                     num_symb
% 7.87/1.48  --inst_solver_per_active                1400
% 7.87/1.48  --inst_solver_calls_frac                1.
% 7.87/1.48  --inst_passive_queue_type               priority_queues
% 7.87/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.87/1.48  --inst_passive_queues_freq              [25;2]
% 7.87/1.48  --inst_dismatching                      true
% 7.87/1.48  --inst_eager_unprocessed_to_passive     true
% 7.87/1.48  --inst_prop_sim_given                   true
% 7.87/1.48  --inst_prop_sim_new                     false
% 7.87/1.48  --inst_subs_new                         false
% 7.87/1.48  --inst_eq_res_simp                      false
% 7.87/1.48  --inst_subs_given                       false
% 7.87/1.48  --inst_orphan_elimination               true
% 7.87/1.48  --inst_learning_loop_flag               true
% 7.87/1.48  --inst_learning_start                   3000
% 7.87/1.48  --inst_learning_factor                  2
% 7.87/1.48  --inst_start_prop_sim_after_learn       3
% 7.87/1.48  --inst_sel_renew                        solver
% 7.87/1.48  --inst_lit_activity_flag                true
% 7.87/1.48  --inst_restr_to_given                   false
% 7.87/1.48  --inst_activity_threshold               500
% 7.87/1.48  --inst_out_proof                        true
% 7.87/1.48  
% 7.87/1.48  ------ Resolution Options
% 7.87/1.48  
% 7.87/1.48  --resolution_flag                       true
% 7.87/1.48  --res_lit_sel                           adaptive
% 7.87/1.48  --res_lit_sel_side                      none
% 7.87/1.48  --res_ordering                          kbo
% 7.87/1.48  --res_to_prop_solver                    active
% 7.87/1.48  --res_prop_simpl_new                    false
% 7.87/1.48  --res_prop_simpl_given                  true
% 7.87/1.48  --res_passive_queue_type                priority_queues
% 7.87/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.87/1.48  --res_passive_queues_freq               [15;5]
% 7.87/1.48  --res_forward_subs                      full
% 7.87/1.48  --res_backward_subs                     full
% 7.87/1.48  --res_forward_subs_resolution           true
% 7.87/1.48  --res_backward_subs_resolution          true
% 7.87/1.48  --res_orphan_elimination                true
% 7.87/1.48  --res_time_limit                        2.
% 7.87/1.48  --res_out_proof                         true
% 7.87/1.48  
% 7.87/1.48  ------ Superposition Options
% 7.87/1.48  
% 7.87/1.48  --superposition_flag                    true
% 7.87/1.48  --sup_passive_queue_type                priority_queues
% 7.87/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.87/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.87/1.48  --demod_completeness_check              fast
% 7.87/1.48  --demod_use_ground                      true
% 7.87/1.48  --sup_to_prop_solver                    passive
% 7.87/1.48  --sup_prop_simpl_new                    true
% 7.87/1.48  --sup_prop_simpl_given                  true
% 7.87/1.48  --sup_fun_splitting                     false
% 7.87/1.48  --sup_smt_interval                      50000
% 7.87/1.48  
% 7.87/1.48  ------ Superposition Simplification Setup
% 7.87/1.48  
% 7.87/1.48  --sup_indices_passive                   []
% 7.87/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.87/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.87/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.87/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.87/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.87/1.48  --sup_full_bw                           [BwDemod]
% 7.87/1.48  --sup_immed_triv                        [TrivRules]
% 7.87/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.87/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.87/1.48  --sup_immed_bw_main                     []
% 7.87/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.87/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.87/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.87/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.87/1.48  
% 7.87/1.48  ------ Combination Options
% 7.87/1.48  
% 7.87/1.48  --comb_res_mult                         3
% 7.87/1.48  --comb_sup_mult                         2
% 7.87/1.48  --comb_inst_mult                        10
% 7.87/1.48  
% 7.87/1.48  ------ Debug Options
% 7.87/1.48  
% 7.87/1.48  --dbg_backtrace                         false
% 7.87/1.48  --dbg_dump_prop_clauses                 false
% 7.87/1.48  --dbg_dump_prop_clauses_file            -
% 7.87/1.48  --dbg_out_stat                          false
% 7.87/1.48  ------ Parsing...
% 7.87/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.87/1.48  
% 7.87/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 7.87/1.48  
% 7.87/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.87/1.48  
% 7.87/1.48  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 7.87/1.48  ------ Proving...
% 7.87/1.48  ------ Problem Properties 
% 7.87/1.48  
% 7.87/1.48  
% 7.87/1.48  clauses                                 9
% 7.87/1.48  conjectures                             1
% 7.87/1.48  EPR                                     0
% 7.87/1.48  Horn                                    9
% 7.87/1.48  unary                                   9
% 7.87/1.48  binary                                  0
% 7.87/1.48  lits                                    9
% 7.87/1.48  lits eq                                 9
% 7.87/1.48  fd_pure                                 0
% 7.87/1.48  fd_pseudo                               0
% 7.87/1.48  fd_cond                                 0
% 7.87/1.48  fd_pseudo_cond                          0
% 7.87/1.48  AC symbols                              2
% 7.87/1.48  
% 7.87/1.48  ------ Schedule UEQ
% 7.87/1.48  
% 7.87/1.48  ------ pure equality problem: resolution off 
% 7.87/1.48  
% 7.87/1.48  ------ Option_UEQ Time Limit: Unbounded
% 7.87/1.48  
% 7.87/1.48  
% 7.87/1.48  ------ 
% 7.87/1.48  Current options:
% 7.87/1.48  ------ 
% 7.87/1.48  
% 7.87/1.48  ------ Input Options
% 7.87/1.48  
% 7.87/1.48  --out_options                           all
% 7.87/1.48  --tptp_safe_out                         true
% 7.87/1.48  --problem_path                          ""
% 7.87/1.48  --include_path                          ""
% 7.87/1.48  --clausifier                            res/vclausify_rel
% 7.87/1.48  --clausifier_options                    --mode clausify
% 7.87/1.48  --stdin                                 false
% 7.87/1.48  --stats_out                             all
% 7.87/1.48  
% 7.87/1.48  ------ General Options
% 7.87/1.48  
% 7.87/1.48  --fof                                   false
% 7.87/1.48  --time_out_real                         305.
% 7.87/1.48  --time_out_virtual                      -1.
% 7.87/1.48  --symbol_type_check                     false
% 7.87/1.48  --clausify_out                          false
% 7.87/1.48  --sig_cnt_out                           false
% 7.87/1.48  --trig_cnt_out                          false
% 7.87/1.48  --trig_cnt_out_tolerance                1.
% 7.87/1.48  --trig_cnt_out_sk_spl                   false
% 7.87/1.48  --abstr_cl_out                          false
% 7.87/1.48  
% 7.87/1.48  ------ Global Options
% 7.87/1.48  
% 7.87/1.48  --schedule                              default
% 7.87/1.48  --add_important_lit                     false
% 7.87/1.48  --prop_solver_per_cl                    1000
% 7.87/1.48  --min_unsat_core                        false
% 7.87/1.48  --soft_assumptions                      false
% 7.87/1.48  --soft_lemma_size                       3
% 7.87/1.48  --prop_impl_unit_size                   0
% 7.87/1.48  --prop_impl_unit                        []
% 7.87/1.48  --share_sel_clauses                     true
% 7.87/1.48  --reset_solvers                         false
% 7.87/1.48  --bc_imp_inh                            [conj_cone]
% 7.87/1.48  --conj_cone_tolerance                   3.
% 7.87/1.48  --extra_neg_conj                        none
% 7.87/1.48  --large_theory_mode                     true
% 7.87/1.48  --prolific_symb_bound                   200
% 7.87/1.48  --lt_threshold                          2000
% 7.87/1.48  --clause_weak_htbl                      true
% 7.87/1.48  --gc_record_bc_elim                     false
% 7.87/1.48  
% 7.87/1.48  ------ Preprocessing Options
% 7.87/1.48  
% 7.87/1.48  --preprocessing_flag                    true
% 7.87/1.48  --time_out_prep_mult                    0.1
% 7.87/1.48  --splitting_mode                        input
% 7.87/1.48  --splitting_grd                         true
% 7.87/1.48  --splitting_cvd                         false
% 7.87/1.48  --splitting_cvd_svl                     false
% 7.87/1.48  --splitting_nvd                         32
% 7.87/1.48  --sub_typing                            true
% 7.87/1.48  --prep_gs_sim                           true
% 7.87/1.48  --prep_unflatten                        true
% 7.87/1.48  --prep_res_sim                          true
% 7.87/1.48  --prep_upred                            true
% 7.87/1.48  --prep_sem_filter                       exhaustive
% 7.87/1.48  --prep_sem_filter_out                   false
% 7.87/1.48  --pred_elim                             true
% 7.87/1.48  --res_sim_input                         true
% 7.87/1.48  --eq_ax_congr_red                       true
% 7.87/1.48  --pure_diseq_elim                       true
% 7.87/1.48  --brand_transform                       false
% 7.87/1.48  --non_eq_to_eq                          false
% 7.87/1.48  --prep_def_merge                        true
% 7.87/1.48  --prep_def_merge_prop_impl              false
% 7.87/1.48  --prep_def_merge_mbd                    true
% 7.87/1.48  --prep_def_merge_tr_red                 false
% 7.87/1.48  --prep_def_merge_tr_cl                  false
% 7.87/1.48  --smt_preprocessing                     true
% 7.87/1.48  --smt_ac_axioms                         fast
% 7.87/1.48  --preprocessed_out                      false
% 7.87/1.48  --preprocessed_stats                    false
% 7.87/1.48  
% 7.87/1.48  ------ Abstraction refinement Options
% 7.87/1.48  
% 7.87/1.48  --abstr_ref                             []
% 7.87/1.48  --abstr_ref_prep                        false
% 7.87/1.48  --abstr_ref_until_sat                   false
% 7.87/1.48  --abstr_ref_sig_restrict                funpre
% 7.87/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.87/1.48  --abstr_ref_under                       []
% 7.87/1.48  
% 7.87/1.48  ------ SAT Options
% 7.87/1.48  
% 7.87/1.48  --sat_mode                              false
% 7.87/1.48  --sat_fm_restart_options                ""
% 7.87/1.48  --sat_gr_def                            false
% 7.87/1.48  --sat_epr_types                         true
% 7.87/1.48  --sat_non_cyclic_types                  false
% 7.87/1.48  --sat_finite_models                     false
% 7.87/1.48  --sat_fm_lemmas                         false
% 7.87/1.48  --sat_fm_prep                           false
% 7.87/1.48  --sat_fm_uc_incr                        true
% 7.87/1.48  --sat_out_model                         small
% 7.87/1.48  --sat_out_clauses                       false
% 7.87/1.48  
% 7.87/1.48  ------ QBF Options
% 7.87/1.48  
% 7.87/1.48  --qbf_mode                              false
% 7.87/1.48  --qbf_elim_univ                         false
% 7.87/1.48  --qbf_dom_inst                          none
% 7.87/1.48  --qbf_dom_pre_inst                      false
% 7.87/1.48  --qbf_sk_in                             false
% 7.87/1.48  --qbf_pred_elim                         true
% 7.87/1.48  --qbf_split                             512
% 7.87/1.48  
% 7.87/1.48  ------ BMC1 Options
% 7.87/1.48  
% 7.87/1.48  --bmc1_incremental                      false
% 7.87/1.48  --bmc1_axioms                           reachable_all
% 7.87/1.48  --bmc1_min_bound                        0
% 7.87/1.48  --bmc1_max_bound                        -1
% 7.87/1.48  --bmc1_max_bound_default                -1
% 7.87/1.48  --bmc1_symbol_reachability              true
% 7.87/1.48  --bmc1_property_lemmas                  false
% 7.87/1.48  --bmc1_k_induction                      false
% 7.87/1.48  --bmc1_non_equiv_states                 false
% 7.87/1.48  --bmc1_deadlock                         false
% 7.87/1.48  --bmc1_ucm                              false
% 7.87/1.48  --bmc1_add_unsat_core                   none
% 7.87/1.48  --bmc1_unsat_core_children              false
% 7.87/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.87/1.48  --bmc1_out_stat                         full
% 7.87/1.48  --bmc1_ground_init                      false
% 7.87/1.48  --bmc1_pre_inst_next_state              false
% 7.87/1.48  --bmc1_pre_inst_state                   false
% 7.87/1.48  --bmc1_pre_inst_reach_state             false
% 7.87/1.48  --bmc1_out_unsat_core                   false
% 7.87/1.48  --bmc1_aig_witness_out                  false
% 7.87/1.48  --bmc1_verbose                          false
% 7.87/1.48  --bmc1_dump_clauses_tptp                false
% 7.87/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.87/1.48  --bmc1_dump_file                        -
% 7.87/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.87/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.87/1.48  --bmc1_ucm_extend_mode                  1
% 7.87/1.48  --bmc1_ucm_init_mode                    2
% 7.87/1.48  --bmc1_ucm_cone_mode                    none
% 7.87/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.87/1.48  --bmc1_ucm_relax_model                  4
% 7.87/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.87/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.87/1.48  --bmc1_ucm_layered_model                none
% 7.87/1.48  --bmc1_ucm_max_lemma_size               10
% 7.87/1.48  
% 7.87/1.48  ------ AIG Options
% 7.87/1.48  
% 7.87/1.48  --aig_mode                              false
% 7.87/1.48  
% 7.87/1.48  ------ Instantiation Options
% 7.87/1.48  
% 7.87/1.48  --instantiation_flag                    false
% 7.87/1.48  --inst_sos_flag                         false
% 7.87/1.48  --inst_sos_phase                        true
% 7.87/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.87/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.87/1.48  --inst_lit_sel_side                     num_symb
% 7.87/1.48  --inst_solver_per_active                1400
% 7.87/1.48  --inst_solver_calls_frac                1.
% 7.87/1.48  --inst_passive_queue_type               priority_queues
% 7.87/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.87/1.48  --inst_passive_queues_freq              [25;2]
% 7.87/1.48  --inst_dismatching                      true
% 7.87/1.48  --inst_eager_unprocessed_to_passive     true
% 7.87/1.48  --inst_prop_sim_given                   true
% 7.87/1.48  --inst_prop_sim_new                     false
% 7.87/1.48  --inst_subs_new                         false
% 7.87/1.48  --inst_eq_res_simp                      false
% 7.87/1.48  --inst_subs_given                       false
% 7.87/1.48  --inst_orphan_elimination               true
% 7.87/1.48  --inst_learning_loop_flag               true
% 7.87/1.48  --inst_learning_start                   3000
% 7.87/1.48  --inst_learning_factor                  2
% 7.87/1.48  --inst_start_prop_sim_after_learn       3
% 7.87/1.48  --inst_sel_renew                        solver
% 7.87/1.48  --inst_lit_activity_flag                true
% 7.87/1.48  --inst_restr_to_given                   false
% 7.87/1.48  --inst_activity_threshold               500
% 7.87/1.48  --inst_out_proof                        true
% 7.87/1.48  
% 7.87/1.48  ------ Resolution Options
% 7.87/1.48  
% 7.87/1.48  --resolution_flag                       false
% 7.87/1.48  --res_lit_sel                           adaptive
% 7.87/1.48  --res_lit_sel_side                      none
% 7.87/1.48  --res_ordering                          kbo
% 7.87/1.48  --res_to_prop_solver                    active
% 7.87/1.48  --res_prop_simpl_new                    false
% 7.87/1.48  --res_prop_simpl_given                  true
% 7.87/1.48  --res_passive_queue_type                priority_queues
% 7.87/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.87/1.48  --res_passive_queues_freq               [15;5]
% 7.87/1.48  --res_forward_subs                      full
% 7.87/1.48  --res_backward_subs                     full
% 7.87/1.48  --res_forward_subs_resolution           true
% 7.87/1.48  --res_backward_subs_resolution          true
% 7.87/1.48  --res_orphan_elimination                true
% 7.87/1.48  --res_time_limit                        2.
% 7.87/1.48  --res_out_proof                         true
% 7.87/1.48  
% 7.87/1.48  ------ Superposition Options
% 7.87/1.48  
% 7.87/1.48  --superposition_flag                    true
% 7.87/1.48  --sup_passive_queue_type                priority_queues
% 7.87/1.48  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.87/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.87/1.48  --demod_completeness_check              fast
% 7.87/1.48  --demod_use_ground                      true
% 7.87/1.48  --sup_to_prop_solver                    active
% 7.87/1.48  --sup_prop_simpl_new                    false
% 7.87/1.48  --sup_prop_simpl_given                  false
% 7.87/1.48  --sup_fun_splitting                     true
% 7.87/1.48  --sup_smt_interval                      10000
% 7.87/1.48  
% 7.87/1.48  ------ Superposition Simplification Setup
% 7.87/1.48  
% 7.87/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.87/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.87/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.87/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.87/1.48  --sup_full_triv                         [TrivRules]
% 7.87/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.87/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.87/1.48  --sup_immed_triv                        [TrivRules]
% 7.87/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.87/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.87/1.48  --sup_immed_bw_main                     []
% 7.87/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.87/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.87/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.87/1.48  --sup_input_bw                          [BwDemod;BwSubsumption]
% 7.87/1.48  
% 7.87/1.48  ------ Combination Options
% 7.87/1.48  
% 7.87/1.48  --comb_res_mult                         1
% 7.87/1.48  --comb_sup_mult                         1
% 7.87/1.48  --comb_inst_mult                        1000000
% 7.87/1.48  
% 7.87/1.48  ------ Debug Options
% 7.87/1.48  
% 7.87/1.48  --dbg_backtrace                         false
% 7.87/1.48  --dbg_dump_prop_clauses                 false
% 7.87/1.48  --dbg_dump_prop_clauses_file            -
% 7.87/1.48  --dbg_out_stat                          false
% 7.87/1.48  
% 7.87/1.48  
% 7.87/1.48  
% 7.87/1.48  
% 7.87/1.48  ------ Proving...
% 7.87/1.48  
% 7.87/1.48  
% 7.87/1.48  % SZS status Theorem for theBenchmark.p
% 7.87/1.48  
% 7.87/1.48   Resolution empty clause
% 7.87/1.48  
% 7.87/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.87/1.48  
% 7.87/1.48  fof(f1,axiom,(
% 7.87/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.87/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f17,plain,(
% 7.87/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f1])).
% 7.87/1.48  
% 7.87/1.48  fof(f8,axiom,(
% 7.87/1.48    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.87/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f24,plain,(
% 7.87/1.48    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f8])).
% 7.87/1.48  
% 7.87/1.48  fof(f2,axiom,(
% 7.87/1.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.87/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f18,plain,(
% 7.87/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f2])).
% 7.87/1.48  
% 7.87/1.48  fof(f6,axiom,(
% 7.87/1.48    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 7.87/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f22,plain,(
% 7.87/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 7.87/1.48    inference(cnf_transformation,[],[f6])).
% 7.87/1.48  
% 7.87/1.48  fof(f10,axiom,(
% 7.87/1.48    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.87/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f26,plain,(
% 7.87/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f10])).
% 7.87/1.48  
% 7.87/1.48  fof(f4,axiom,(
% 7.87/1.48    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.87/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f20,plain,(
% 7.87/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f4])).
% 7.87/1.48  
% 7.87/1.48  fof(f28,plain,(
% 7.87/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 7.87/1.48    inference(definition_unfolding,[],[f26,f20])).
% 7.87/1.48  
% 7.87/1.48  fof(f30,plain,(
% 7.87/1.48    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0) )),
% 7.87/1.48    inference(definition_unfolding,[],[f22,f20,f28])).
% 7.87/1.48  
% 7.87/1.48  fof(f5,axiom,(
% 7.87/1.48    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.87/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f21,plain,(
% 7.87/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f5])).
% 7.87/1.48  
% 7.87/1.48  fof(f9,axiom,(
% 7.87/1.48    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.87/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f25,plain,(
% 7.87/1.48    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.87/1.48    inference(cnf_transformation,[],[f9])).
% 7.87/1.48  
% 7.87/1.48  fof(f3,axiom,(
% 7.87/1.48    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 7.87/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f13,plain,(
% 7.87/1.48    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 7.87/1.48    inference(rectify,[],[f3])).
% 7.87/1.48  
% 7.87/1.48  fof(f19,plain,(
% 7.87/1.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 7.87/1.48    inference(cnf_transformation,[],[f13])).
% 7.87/1.48  
% 7.87/1.48  fof(f29,plain,(
% 7.87/1.48    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 7.87/1.48    inference(definition_unfolding,[],[f19,f28])).
% 7.87/1.48  
% 7.87/1.48  fof(f11,conjecture,(
% 7.87/1.48    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.87/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f12,negated_conjecture,(
% 7.87/1.48    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.87/1.48    inference(negated_conjecture,[],[f11])).
% 7.87/1.48  
% 7.87/1.48  fof(f14,plain,(
% 7.87/1.48    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 7.87/1.48    inference(ennf_transformation,[],[f12])).
% 7.87/1.48  
% 7.87/1.48  fof(f15,plain,(
% 7.87/1.48    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.87/1.48    introduced(choice_axiom,[])).
% 7.87/1.48  
% 7.87/1.48  fof(f16,plain,(
% 7.87/1.48    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.87/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 7.87/1.48  
% 7.87/1.48  fof(f27,plain,(
% 7.87/1.48    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 7.87/1.48    inference(cnf_transformation,[],[f16])).
% 7.87/1.48  
% 7.87/1.48  fof(f32,plain,(
% 7.87/1.48    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 7.87/1.48    inference(definition_unfolding,[],[f27,f20,f28])).
% 7.87/1.48  
% 7.87/1.48  fof(f7,axiom,(
% 7.87/1.48    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 7.87/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.87/1.48  
% 7.87/1.48  fof(f23,plain,(
% 7.87/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 7.87/1.48    inference(cnf_transformation,[],[f7])).
% 7.87/1.48  
% 7.87/1.48  fof(f31,plain,(
% 7.87/1.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 7.87/1.48    inference(definition_unfolding,[],[f23,f20,f20])).
% 7.87/1.48  
% 7.87/1.48  cnf(c_0,plain,
% 7.87/1.48      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 7.87/1.48      inference(cnf_transformation,[],[f17]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_6,plain,
% 7.87/1.48      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.87/1.48      inference(cnf_transformation,[],[f24]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_1,plain,
% 7.87/1.48      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.87/1.48      inference(cnf_transformation,[],[f18]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_34,plain,
% 7.87/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X0,X2)) ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_6,c_1]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_4,plain,
% 7.87/1.48      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
% 7.87/1.48      inference(cnf_transformation,[],[f30]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_3,plain,
% 7.87/1.48      ( k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 7.87/1.48      inference(cnf_transformation,[],[f21]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_23,plain,
% 7.87/1.48      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))) = k1_xboole_0 ),
% 7.87/1.48      inference(theory_normalisation,[status(thm)],[c_4,c_6,c_1,c_3,c_0]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_7,plain,
% 7.87/1.48      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.87/1.48      inference(cnf_transformation,[],[f25]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_42,plain,
% 7.87/1.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_7,c_6]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_49,plain,
% 7.87/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_1,c_42]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_2,plain,
% 7.87/1.48      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
% 7.87/1.48      inference(cnf_transformation,[],[f29]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_57,plain,
% 7.87/1.48      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) = X0 ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_42,c_2]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_78,plain,
% 7.87/1.48      ( k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_57,c_42]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_81,plain,
% 7.87/1.48      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.87/1.48      inference(demodulation,[status(thm)],[c_78,c_57]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_83,plain,
% 7.87/1.48      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.87/1.48      inference(demodulation,[status(thm)],[c_49,c_81]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_87,plain,
% 7.87/1.48      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_1,c_83]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_266,plain,
% 7.87/1.48      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = k5_xboole_0(X0,k1_xboole_0) ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_23,c_87]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_91,plain,
% 7.87/1.48      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_7,c_83]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_273,plain,
% 7.87/1.48      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 7.87/1.48      inference(light_normalisation,[status(thm)],[c_266,c_91]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_3070,plain,
% 7.87/1.48      ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_34,c_273]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_31588,plain,
% 7.87/1.48      ( k3_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) = X0 ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_0,c_3070]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_8,negated_conjecture,
% 7.87/1.48      ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
% 7.87/1.48      inference(cnf_transformation,[],[f32]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_21,negated_conjecture,
% 7.87/1.48      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) != k5_xboole_0(sK0,sK1) ),
% 7.87/1.48      inference(theory_normalisation,[status(thm)],[c_8,c_6,c_1,c_3,c_0]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_5,plain,
% 7.87/1.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.87/1.48      inference(cnf_transformation,[],[f31]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_22,plain,
% 7.87/1.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,k3_xboole_0(X1,X2))) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 7.87/1.48      inference(theory_normalisation,[status(thm)],[c_5,c_6,c_1,c_3,c_0]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_30,plain,
% 7.87/1.48      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))))) != k5_xboole_0(sK0,sK1) ),
% 7.87/1.48      inference(demodulation,[status(thm)],[c_21,c_22]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_34393,plain,
% 7.87/1.48      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)))) != k5_xboole_0(sK0,sK1) ),
% 7.87/1.48      inference(demodulation,[status(thm)],[c_31588,c_30]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_129,plain,
% 7.87/1.48      ( k3_xboole_0(X0,X0) = X0 ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_81,c_57]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_139,plain,
% 7.87/1.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X1))) ),
% 7.87/1.48      inference(superposition,[status(thm)],[c_129,c_22]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_142,plain,
% 7.87/1.48      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_xboole_0(X0,k5_xboole_0(X1,X1)) ),
% 7.87/1.48      inference(demodulation,[status(thm)],[c_139,c_129]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_143,plain,
% 7.87/1.48      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 7.87/1.48      inference(demodulation,[status(thm)],[c_142,c_7]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_34394,plain,
% 7.87/1.48      ( k5_xboole_0(sK0,sK1) != k5_xboole_0(sK0,sK1) ),
% 7.87/1.48      inference(demodulation,[status(thm)],[c_34393,c_7,c_91,c_143]) ).
% 7.87/1.48  
% 7.87/1.48  cnf(c_34395,plain,
% 7.87/1.48      ( $false ),
% 7.87/1.48      inference(equality_resolution_simp,[status(thm)],[c_34394]) ).
% 7.87/1.48  
% 7.87/1.48  
% 7.87/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.87/1.48  
% 7.87/1.48  ------                               Statistics
% 7.87/1.48  
% 7.87/1.48  ------ General
% 7.87/1.48  
% 7.87/1.48  abstr_ref_over_cycles:                  0
% 7.87/1.48  abstr_ref_under_cycles:                 0
% 7.87/1.48  gc_basic_clause_elim:                   0
% 7.87/1.48  forced_gc_time:                         0
% 7.87/1.48  parsing_time:                           0.021
% 7.87/1.48  unif_index_cands_time:                  0.
% 7.87/1.48  unif_index_add_time:                    0.
% 7.87/1.48  orderings_time:                         0.
% 7.87/1.48  out_proof_time:                         0.005
% 7.87/1.48  total_time:                             0.964
% 7.87/1.48  num_of_symbols:                         36
% 7.87/1.48  num_of_terms:                           64598
% 7.87/1.48  
% 7.87/1.48  ------ Preprocessing
% 7.87/1.48  
% 7.87/1.48  num_of_splits:                          0
% 7.87/1.48  num_of_split_atoms:                     0
% 7.87/1.48  num_of_reused_defs:                     0
% 7.87/1.48  num_eq_ax_congr_red:                    0
% 7.87/1.48  num_of_sem_filtered_clauses:            0
% 7.87/1.48  num_of_subtypes:                        0
% 7.87/1.48  monotx_restored_types:                  0
% 7.87/1.48  sat_num_of_epr_types:                   0
% 7.87/1.48  sat_num_of_non_cyclic_types:            0
% 7.87/1.48  sat_guarded_non_collapsed_types:        0
% 7.87/1.48  num_pure_diseq_elim:                    0
% 7.87/1.48  simp_replaced_by:                       0
% 7.87/1.48  res_preprocessed:                       22
% 7.87/1.48  prep_upred:                             0
% 7.87/1.48  prep_unflattend:                        0
% 7.87/1.48  smt_new_axioms:                         0
% 7.87/1.48  pred_elim_cands:                        0
% 7.87/1.48  pred_elim:                              0
% 7.87/1.48  pred_elim_cl:                           0
% 7.87/1.48  pred_elim_cycles:                       0
% 7.87/1.48  merged_defs:                            0
% 7.87/1.48  merged_defs_ncl:                        0
% 7.87/1.48  bin_hyper_res:                          0
% 7.87/1.48  prep_cycles:                            2
% 7.87/1.48  pred_elim_time:                         0.
% 7.87/1.48  splitting_time:                         0.
% 7.87/1.48  sem_filter_time:                        0.
% 7.87/1.48  monotx_time:                            0.
% 7.87/1.48  subtype_inf_time:                       0.
% 7.87/1.48  
% 7.87/1.48  ------ Problem properties
% 7.87/1.48  
% 7.87/1.48  clauses:                                9
% 7.87/1.48  conjectures:                            1
% 7.87/1.48  epr:                                    0
% 7.87/1.48  horn:                                   9
% 7.87/1.48  ground:                                 1
% 7.87/1.48  unary:                                  9
% 7.87/1.48  binary:                                 0
% 7.87/1.48  lits:                                   9
% 7.87/1.48  lits_eq:                                9
% 7.87/1.48  fd_pure:                                0
% 7.87/1.48  fd_pseudo:                              0
% 7.87/1.48  fd_cond:                                0
% 7.87/1.48  fd_pseudo_cond:                         0
% 7.87/1.48  ac_symbols:                             2
% 7.87/1.48  
% 7.87/1.48  ------ Propositional Solver
% 7.87/1.48  
% 7.87/1.48  prop_solver_calls:                      13
% 7.87/1.48  prop_fast_solver_calls:                 56
% 7.87/1.48  smt_solver_calls:                       0
% 7.87/1.48  smt_fast_solver_calls:                  0
% 7.87/1.48  prop_num_of_clauses:                    233
% 7.87/1.48  prop_preprocess_simplified:             369
% 7.87/1.48  prop_fo_subsumed:                       0
% 7.87/1.48  prop_solver_time:                       0.
% 7.87/1.48  smt_solver_time:                        0.
% 7.87/1.48  smt_fast_solver_time:                   0.
% 7.87/1.48  prop_fast_solver_time:                  0.
% 7.87/1.48  prop_unsat_core_time:                   0.
% 7.87/1.48  
% 7.87/1.48  ------ QBF
% 7.87/1.48  
% 7.87/1.48  qbf_q_res:                              0
% 7.87/1.48  qbf_num_tautologies:                    0
% 7.87/1.48  qbf_prep_cycles:                        0
% 7.87/1.48  
% 7.87/1.48  ------ BMC1
% 7.87/1.48  
% 7.87/1.48  bmc1_current_bound:                     -1
% 7.87/1.48  bmc1_last_solved_bound:                 -1
% 7.87/1.48  bmc1_unsat_core_size:                   -1
% 7.87/1.48  bmc1_unsat_core_parents_size:           -1
% 7.87/1.48  bmc1_merge_next_fun:                    0
% 7.87/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.87/1.48  
% 7.87/1.48  ------ Instantiation
% 7.87/1.48  
% 7.87/1.48  inst_num_of_clauses:                    0
% 7.87/1.48  inst_num_in_passive:                    0
% 7.87/1.48  inst_num_in_active:                     0
% 7.87/1.48  inst_num_in_unprocessed:                0
% 7.87/1.48  inst_num_of_loops:                      0
% 7.87/1.48  inst_num_of_learning_restarts:          0
% 7.87/1.48  inst_num_moves_active_passive:          0
% 7.87/1.48  inst_lit_activity:                      0
% 7.87/1.48  inst_lit_activity_moves:                0
% 7.87/1.48  inst_num_tautologies:                   0
% 7.87/1.48  inst_num_prop_implied:                  0
% 7.87/1.48  inst_num_existing_simplified:           0
% 7.87/1.48  inst_num_eq_res_simplified:             0
% 7.87/1.48  inst_num_child_elim:                    0
% 7.87/1.48  inst_num_of_dismatching_blockings:      0
% 7.87/1.48  inst_num_of_non_proper_insts:           0
% 7.87/1.48  inst_num_of_duplicates:                 0
% 7.87/1.48  inst_inst_num_from_inst_to_res:         0
% 7.87/1.48  inst_dismatching_checking_time:         0.
% 7.87/1.48  
% 7.87/1.48  ------ Resolution
% 7.87/1.48  
% 7.87/1.48  res_num_of_clauses:                     0
% 7.87/1.48  res_num_in_passive:                     0
% 7.87/1.48  res_num_in_active:                      0
% 7.87/1.48  res_num_of_loops:                       24
% 7.87/1.48  res_forward_subset_subsumed:            0
% 7.87/1.48  res_backward_subset_subsumed:           0
% 7.87/1.48  res_forward_subsumed:                   0
% 7.87/1.48  res_backward_subsumed:                  0
% 7.87/1.48  res_forward_subsumption_resolution:     0
% 7.87/1.48  res_backward_subsumption_resolution:    0
% 7.87/1.48  res_clause_to_clause_subsumption:       72985
% 7.87/1.48  res_orphan_elimination:                 0
% 7.87/1.48  res_tautology_del:                      0
% 7.87/1.48  res_num_eq_res_simplified:              0
% 7.87/1.48  res_num_sel_changes:                    0
% 7.87/1.48  res_moves_from_active_to_pass:          0
% 7.87/1.48  
% 7.87/1.48  ------ Superposition
% 7.87/1.48  
% 7.87/1.48  sup_time_total:                         0.
% 7.87/1.48  sup_time_generating:                    0.
% 7.87/1.48  sup_time_sim_full:                      0.
% 7.87/1.48  sup_time_sim_immed:                     0.
% 7.87/1.48  
% 7.87/1.48  sup_num_of_clauses:                     2778
% 7.87/1.48  sup_num_in_active:                      138
% 7.87/1.48  sup_num_in_passive:                     2640
% 7.87/1.48  sup_num_of_loops:                       146
% 7.87/1.48  sup_fw_superposition:                   12335
% 7.87/1.48  sup_bw_superposition:                   8853
% 7.87/1.48  sup_immediate_simplified:               10806
% 7.87/1.48  sup_given_eliminated:                   1
% 7.87/1.48  comparisons_done:                       0
% 7.87/1.48  comparisons_avoided:                    0
% 7.87/1.48  
% 7.87/1.48  ------ Simplifications
% 7.87/1.48  
% 7.87/1.48  
% 7.87/1.48  sim_fw_subset_subsumed:                 0
% 7.87/1.48  sim_bw_subset_subsumed:                 0
% 7.87/1.48  sim_fw_subsumed:                        859
% 7.87/1.48  sim_bw_subsumed:                        10
% 7.87/1.48  sim_fw_subsumption_res:                 0
% 7.87/1.48  sim_bw_subsumption_res:                 0
% 7.87/1.48  sim_tautology_del:                      0
% 7.87/1.48  sim_eq_tautology_del:                   3904
% 7.87/1.48  sim_eq_res_simp:                        0
% 7.87/1.48  sim_fw_demodulated:                     8167
% 7.87/1.48  sim_bw_demodulated:                     61
% 7.87/1.48  sim_light_normalised:                   4454
% 7.87/1.48  sim_joinable_taut:                      234
% 7.87/1.48  sim_joinable_simp:                      0
% 7.87/1.48  sim_ac_normalised:                      0
% 7.87/1.48  sim_smt_subsumption:                    0
% 7.87/1.48  
%------------------------------------------------------------------------------
