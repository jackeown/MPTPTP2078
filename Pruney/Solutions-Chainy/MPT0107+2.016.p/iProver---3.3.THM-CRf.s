%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:20 EST 2020

% Result     : Theorem 7.71s
% Output     : CNFRefutation 7.71s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 264 expanded)
%              Number of clauses        :   33 (  81 expanded)
%              Number of leaves         :   15 (  77 expanded)
%              Depth                    :   17
%              Number of atoms          :   79 ( 271 expanded)
%              Number of equality atoms :   78 ( 270 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f28,f43,f43])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f4,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f36,f43])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f16,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(definition_unfolding,[],[f40,f48])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f15,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f15])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f17,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f17])).

fof(f20,plain,(
    ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f18])).

fof(f26,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1)
   => k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != k4_xboole_0(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != k4_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).

fof(f49,plain,(
    k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != k4_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK1,sK2) ),
    inference(definition_unfolding,[],[f49,f43])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_14,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_742,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_0,c_14])).

cnf(c_3160,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_0,c_742])).

cnf(c_3239,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(light_normalisation,[status(thm)],[c_3160,c_742])).

cnf(c_8,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_215,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8,c_10])).

cnf(c_3241,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3239,c_215])).

cnf(c_11,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_708,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_11,c_11])).

cnf(c_12,plain,
    ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_30560,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_708,c_12,c_3241])).

cnf(c_9,plain,
    ( X0 = X1
    | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_30693,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))
    | k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_30560,c_9])).

cnf(c_30728,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_30693,c_30560])).

cnf(c_30729,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_30728])).

cnf(c_1,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_18,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_17,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_924,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_18,c_17])).

cnf(c_16,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_354,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_16,c_1])).

cnf(c_940,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_924,c_354])).

cnf(c_1019,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_940])).

cnf(c_1052,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
    inference(superposition,[status(thm)],[c_1019,c_1019])).

cnf(c_32755,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_30729,c_1052])).

cnf(c_34265,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3241,c_32755])).

cnf(c_34713,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_34265,c_16])).

cnf(c_19,negated_conjecture,
    ( k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_43711,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_34713,c_19])).

cnf(c_43712,plain,
    ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_43711,c_14])).

cnf(c_43713,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_43712])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.71/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.71/1.51  
% 7.71/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.71/1.51  
% 7.71/1.51  ------  iProver source info
% 7.71/1.51  
% 7.71/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.71/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.71/1.51  git: non_committed_changes: false
% 7.71/1.51  git: last_make_outside_of_git: false
% 7.71/1.51  
% 7.71/1.51  ------ 
% 7.71/1.51  
% 7.71/1.51  ------ Input Options
% 7.71/1.51  
% 7.71/1.51  --out_options                           all
% 7.71/1.51  --tptp_safe_out                         true
% 7.71/1.51  --problem_path                          ""
% 7.71/1.51  --include_path                          ""
% 7.71/1.51  --clausifier                            res/vclausify_rel
% 7.71/1.51  --clausifier_options                    --mode clausify
% 7.71/1.51  --stdin                                 false
% 7.71/1.51  --stats_out                             all
% 7.71/1.51  
% 7.71/1.51  ------ General Options
% 7.71/1.51  
% 7.71/1.51  --fof                                   false
% 7.71/1.51  --time_out_real                         305.
% 7.71/1.51  --time_out_virtual                      -1.
% 7.71/1.51  --symbol_type_check                     false
% 7.71/1.51  --clausify_out                          false
% 7.71/1.51  --sig_cnt_out                           false
% 7.71/1.51  --trig_cnt_out                          false
% 7.71/1.51  --trig_cnt_out_tolerance                1.
% 7.71/1.51  --trig_cnt_out_sk_spl                   false
% 7.71/1.51  --abstr_cl_out                          false
% 7.71/1.51  
% 7.71/1.51  ------ Global Options
% 7.71/1.51  
% 7.71/1.51  --schedule                              default
% 7.71/1.51  --add_important_lit                     false
% 7.71/1.51  --prop_solver_per_cl                    1000
% 7.71/1.51  --min_unsat_core                        false
% 7.71/1.51  --soft_assumptions                      false
% 7.71/1.51  --soft_lemma_size                       3
% 7.71/1.51  --prop_impl_unit_size                   0
% 7.71/1.51  --prop_impl_unit                        []
% 7.71/1.51  --share_sel_clauses                     true
% 7.71/1.51  --reset_solvers                         false
% 7.71/1.51  --bc_imp_inh                            [conj_cone]
% 7.71/1.51  --conj_cone_tolerance                   3.
% 7.71/1.51  --extra_neg_conj                        none
% 7.71/1.51  --large_theory_mode                     true
% 7.71/1.51  --prolific_symb_bound                   200
% 7.71/1.51  --lt_threshold                          2000
% 7.71/1.51  --clause_weak_htbl                      true
% 7.71/1.51  --gc_record_bc_elim                     false
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing Options
% 7.71/1.51  
% 7.71/1.51  --preprocessing_flag                    true
% 7.71/1.51  --time_out_prep_mult                    0.1
% 7.71/1.51  --splitting_mode                        input
% 7.71/1.51  --splitting_grd                         true
% 7.71/1.51  --splitting_cvd                         false
% 7.71/1.51  --splitting_cvd_svl                     false
% 7.71/1.51  --splitting_nvd                         32
% 7.71/1.51  --sub_typing                            true
% 7.71/1.51  --prep_gs_sim                           true
% 7.71/1.51  --prep_unflatten                        true
% 7.71/1.51  --prep_res_sim                          true
% 7.71/1.51  --prep_upred                            true
% 7.71/1.51  --prep_sem_filter                       exhaustive
% 7.71/1.51  --prep_sem_filter_out                   false
% 7.71/1.51  --pred_elim                             true
% 7.71/1.51  --res_sim_input                         true
% 7.71/1.51  --eq_ax_congr_red                       true
% 7.71/1.51  --pure_diseq_elim                       true
% 7.71/1.51  --brand_transform                       false
% 7.71/1.51  --non_eq_to_eq                          false
% 7.71/1.51  --prep_def_merge                        true
% 7.71/1.51  --prep_def_merge_prop_impl              false
% 7.71/1.51  --prep_def_merge_mbd                    true
% 7.71/1.51  --prep_def_merge_tr_red                 false
% 7.71/1.51  --prep_def_merge_tr_cl                  false
% 7.71/1.51  --smt_preprocessing                     true
% 7.71/1.51  --smt_ac_axioms                         fast
% 7.71/1.51  --preprocessed_out                      false
% 7.71/1.51  --preprocessed_stats                    false
% 7.71/1.51  
% 7.71/1.51  ------ Abstraction refinement Options
% 7.71/1.51  
% 7.71/1.51  --abstr_ref                             []
% 7.71/1.51  --abstr_ref_prep                        false
% 7.71/1.51  --abstr_ref_until_sat                   false
% 7.71/1.51  --abstr_ref_sig_restrict                funpre
% 7.71/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.71/1.51  --abstr_ref_under                       []
% 7.71/1.51  
% 7.71/1.51  ------ SAT Options
% 7.71/1.51  
% 7.71/1.51  --sat_mode                              false
% 7.71/1.51  --sat_fm_restart_options                ""
% 7.71/1.51  --sat_gr_def                            false
% 7.71/1.51  --sat_epr_types                         true
% 7.71/1.51  --sat_non_cyclic_types                  false
% 7.71/1.51  --sat_finite_models                     false
% 7.71/1.51  --sat_fm_lemmas                         false
% 7.71/1.51  --sat_fm_prep                           false
% 7.71/1.51  --sat_fm_uc_incr                        true
% 7.71/1.51  --sat_out_model                         small
% 7.71/1.51  --sat_out_clauses                       false
% 7.71/1.51  
% 7.71/1.51  ------ QBF Options
% 7.71/1.51  
% 7.71/1.51  --qbf_mode                              false
% 7.71/1.51  --qbf_elim_univ                         false
% 7.71/1.51  --qbf_dom_inst                          none
% 7.71/1.51  --qbf_dom_pre_inst                      false
% 7.71/1.51  --qbf_sk_in                             false
% 7.71/1.51  --qbf_pred_elim                         true
% 7.71/1.51  --qbf_split                             512
% 7.71/1.51  
% 7.71/1.51  ------ BMC1 Options
% 7.71/1.51  
% 7.71/1.51  --bmc1_incremental                      false
% 7.71/1.51  --bmc1_axioms                           reachable_all
% 7.71/1.51  --bmc1_min_bound                        0
% 7.71/1.51  --bmc1_max_bound                        -1
% 7.71/1.51  --bmc1_max_bound_default                -1
% 7.71/1.51  --bmc1_symbol_reachability              true
% 7.71/1.51  --bmc1_property_lemmas                  false
% 7.71/1.51  --bmc1_k_induction                      false
% 7.71/1.51  --bmc1_non_equiv_states                 false
% 7.71/1.51  --bmc1_deadlock                         false
% 7.71/1.51  --bmc1_ucm                              false
% 7.71/1.51  --bmc1_add_unsat_core                   none
% 7.71/1.51  --bmc1_unsat_core_children              false
% 7.71/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.71/1.51  --bmc1_out_stat                         full
% 7.71/1.51  --bmc1_ground_init                      false
% 7.71/1.51  --bmc1_pre_inst_next_state              false
% 7.71/1.51  --bmc1_pre_inst_state                   false
% 7.71/1.51  --bmc1_pre_inst_reach_state             false
% 7.71/1.51  --bmc1_out_unsat_core                   false
% 7.71/1.51  --bmc1_aig_witness_out                  false
% 7.71/1.51  --bmc1_verbose                          false
% 7.71/1.51  --bmc1_dump_clauses_tptp                false
% 7.71/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.71/1.51  --bmc1_dump_file                        -
% 7.71/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.71/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.71/1.51  --bmc1_ucm_extend_mode                  1
% 7.71/1.51  --bmc1_ucm_init_mode                    2
% 7.71/1.51  --bmc1_ucm_cone_mode                    none
% 7.71/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.71/1.51  --bmc1_ucm_relax_model                  4
% 7.71/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.71/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.71/1.51  --bmc1_ucm_layered_model                none
% 7.71/1.51  --bmc1_ucm_max_lemma_size               10
% 7.71/1.51  
% 7.71/1.51  ------ AIG Options
% 7.71/1.51  
% 7.71/1.51  --aig_mode                              false
% 7.71/1.51  
% 7.71/1.51  ------ Instantiation Options
% 7.71/1.51  
% 7.71/1.51  --instantiation_flag                    true
% 7.71/1.51  --inst_sos_flag                         false
% 7.71/1.51  --inst_sos_phase                        true
% 7.71/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.71/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.71/1.51  --inst_lit_sel_side                     num_symb
% 7.71/1.51  --inst_solver_per_active                1400
% 7.71/1.51  --inst_solver_calls_frac                1.
% 7.71/1.51  --inst_passive_queue_type               priority_queues
% 7.71/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.71/1.51  --inst_passive_queues_freq              [25;2]
% 7.71/1.51  --inst_dismatching                      true
% 7.71/1.51  --inst_eager_unprocessed_to_passive     true
% 7.71/1.51  --inst_prop_sim_given                   true
% 7.71/1.51  --inst_prop_sim_new                     false
% 7.71/1.51  --inst_subs_new                         false
% 7.71/1.51  --inst_eq_res_simp                      false
% 7.71/1.51  --inst_subs_given                       false
% 7.71/1.51  --inst_orphan_elimination               true
% 7.71/1.51  --inst_learning_loop_flag               true
% 7.71/1.51  --inst_learning_start                   3000
% 7.71/1.51  --inst_learning_factor                  2
% 7.71/1.51  --inst_start_prop_sim_after_learn       3
% 7.71/1.51  --inst_sel_renew                        solver
% 7.71/1.51  --inst_lit_activity_flag                true
% 7.71/1.51  --inst_restr_to_given                   false
% 7.71/1.51  --inst_activity_threshold               500
% 7.71/1.51  --inst_out_proof                        true
% 7.71/1.51  
% 7.71/1.51  ------ Resolution Options
% 7.71/1.51  
% 7.71/1.51  --resolution_flag                       true
% 7.71/1.51  --res_lit_sel                           adaptive
% 7.71/1.51  --res_lit_sel_side                      none
% 7.71/1.51  --res_ordering                          kbo
% 7.71/1.51  --res_to_prop_solver                    active
% 7.71/1.51  --res_prop_simpl_new                    false
% 7.71/1.51  --res_prop_simpl_given                  true
% 7.71/1.51  --res_passive_queue_type                priority_queues
% 7.71/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.71/1.51  --res_passive_queues_freq               [15;5]
% 7.71/1.51  --res_forward_subs                      full
% 7.71/1.51  --res_backward_subs                     full
% 7.71/1.51  --res_forward_subs_resolution           true
% 7.71/1.51  --res_backward_subs_resolution          true
% 7.71/1.51  --res_orphan_elimination                true
% 7.71/1.51  --res_time_limit                        2.
% 7.71/1.51  --res_out_proof                         true
% 7.71/1.51  
% 7.71/1.51  ------ Superposition Options
% 7.71/1.51  
% 7.71/1.51  --superposition_flag                    true
% 7.71/1.51  --sup_passive_queue_type                priority_queues
% 7.71/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.71/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.71/1.51  --demod_completeness_check              fast
% 7.71/1.51  --demod_use_ground                      true
% 7.71/1.51  --sup_to_prop_solver                    passive
% 7.71/1.51  --sup_prop_simpl_new                    true
% 7.71/1.51  --sup_prop_simpl_given                  true
% 7.71/1.51  --sup_fun_splitting                     false
% 7.71/1.51  --sup_smt_interval                      50000
% 7.71/1.51  
% 7.71/1.51  ------ Superposition Simplification Setup
% 7.71/1.51  
% 7.71/1.51  --sup_indices_passive                   []
% 7.71/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.71/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.71/1.51  --sup_full_bw                           [BwDemod]
% 7.71/1.51  --sup_immed_triv                        [TrivRules]
% 7.71/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.71/1.51  --sup_immed_bw_main                     []
% 7.71/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.71/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.71/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.71/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.71/1.51  
% 7.71/1.51  ------ Combination Options
% 7.71/1.51  
% 7.71/1.51  --comb_res_mult                         3
% 7.71/1.51  --comb_sup_mult                         2
% 7.71/1.51  --comb_inst_mult                        10
% 7.71/1.51  
% 7.71/1.51  ------ Debug Options
% 7.71/1.51  
% 7.71/1.51  --dbg_backtrace                         false
% 7.71/1.51  --dbg_dump_prop_clauses                 false
% 7.71/1.51  --dbg_dump_prop_clauses_file            -
% 7.71/1.51  --dbg_out_stat                          false
% 7.71/1.51  ------ Parsing...
% 7.71/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.71/1.51  ------ Proving...
% 7.71/1.51  ------ Problem Properties 
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  clauses                                 20
% 7.71/1.51  conjectures                             1
% 7.71/1.51  EPR                                     0
% 7.71/1.51  Horn                                    16
% 7.71/1.51  unary                                   13
% 7.71/1.51  binary                                  3
% 7.71/1.51  lits                                    32
% 7.71/1.51  lits eq                                 18
% 7.71/1.51  fd_pure                                 0
% 7.71/1.51  fd_pseudo                               0
% 7.71/1.51  fd_cond                                 0
% 7.71/1.51  fd_pseudo_cond                          4
% 7.71/1.51  AC symbols                              1
% 7.71/1.51  
% 7.71/1.51  ------ Schedule dynamic 5 is on 
% 7.71/1.51  
% 7.71/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  ------ 
% 7.71/1.51  Current options:
% 7.71/1.51  ------ 
% 7.71/1.51  
% 7.71/1.51  ------ Input Options
% 7.71/1.51  
% 7.71/1.51  --out_options                           all
% 7.71/1.51  --tptp_safe_out                         true
% 7.71/1.51  --problem_path                          ""
% 7.71/1.51  --include_path                          ""
% 7.71/1.51  --clausifier                            res/vclausify_rel
% 7.71/1.51  --clausifier_options                    --mode clausify
% 7.71/1.51  --stdin                                 false
% 7.71/1.51  --stats_out                             all
% 7.71/1.51  
% 7.71/1.51  ------ General Options
% 7.71/1.51  
% 7.71/1.51  --fof                                   false
% 7.71/1.51  --time_out_real                         305.
% 7.71/1.51  --time_out_virtual                      -1.
% 7.71/1.51  --symbol_type_check                     false
% 7.71/1.51  --clausify_out                          false
% 7.71/1.51  --sig_cnt_out                           false
% 7.71/1.51  --trig_cnt_out                          false
% 7.71/1.51  --trig_cnt_out_tolerance                1.
% 7.71/1.51  --trig_cnt_out_sk_spl                   false
% 7.71/1.51  --abstr_cl_out                          false
% 7.71/1.51  
% 7.71/1.51  ------ Global Options
% 7.71/1.51  
% 7.71/1.51  --schedule                              default
% 7.71/1.51  --add_important_lit                     false
% 7.71/1.51  --prop_solver_per_cl                    1000
% 7.71/1.51  --min_unsat_core                        false
% 7.71/1.51  --soft_assumptions                      false
% 7.71/1.51  --soft_lemma_size                       3
% 7.71/1.51  --prop_impl_unit_size                   0
% 7.71/1.51  --prop_impl_unit                        []
% 7.71/1.51  --share_sel_clauses                     true
% 7.71/1.51  --reset_solvers                         false
% 7.71/1.51  --bc_imp_inh                            [conj_cone]
% 7.71/1.51  --conj_cone_tolerance                   3.
% 7.71/1.51  --extra_neg_conj                        none
% 7.71/1.51  --large_theory_mode                     true
% 7.71/1.51  --prolific_symb_bound                   200
% 7.71/1.51  --lt_threshold                          2000
% 7.71/1.51  --clause_weak_htbl                      true
% 7.71/1.51  --gc_record_bc_elim                     false
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing Options
% 7.71/1.51  
% 7.71/1.51  --preprocessing_flag                    true
% 7.71/1.51  --time_out_prep_mult                    0.1
% 7.71/1.51  --splitting_mode                        input
% 7.71/1.51  --splitting_grd                         true
% 7.71/1.51  --splitting_cvd                         false
% 7.71/1.51  --splitting_cvd_svl                     false
% 7.71/1.51  --splitting_nvd                         32
% 7.71/1.51  --sub_typing                            true
% 7.71/1.51  --prep_gs_sim                           true
% 7.71/1.51  --prep_unflatten                        true
% 7.71/1.51  --prep_res_sim                          true
% 7.71/1.51  --prep_upred                            true
% 7.71/1.51  --prep_sem_filter                       exhaustive
% 7.71/1.51  --prep_sem_filter_out                   false
% 7.71/1.51  --pred_elim                             true
% 7.71/1.51  --res_sim_input                         true
% 7.71/1.51  --eq_ax_congr_red                       true
% 7.71/1.51  --pure_diseq_elim                       true
% 7.71/1.51  --brand_transform                       false
% 7.71/1.51  --non_eq_to_eq                          false
% 7.71/1.51  --prep_def_merge                        true
% 7.71/1.51  --prep_def_merge_prop_impl              false
% 7.71/1.51  --prep_def_merge_mbd                    true
% 7.71/1.51  --prep_def_merge_tr_red                 false
% 7.71/1.51  --prep_def_merge_tr_cl                  false
% 7.71/1.51  --smt_preprocessing                     true
% 7.71/1.51  --smt_ac_axioms                         fast
% 7.71/1.51  --preprocessed_out                      false
% 7.71/1.51  --preprocessed_stats                    false
% 7.71/1.51  
% 7.71/1.51  ------ Abstraction refinement Options
% 7.71/1.51  
% 7.71/1.51  --abstr_ref                             []
% 7.71/1.51  --abstr_ref_prep                        false
% 7.71/1.51  --abstr_ref_until_sat                   false
% 7.71/1.51  --abstr_ref_sig_restrict                funpre
% 7.71/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.71/1.51  --abstr_ref_under                       []
% 7.71/1.51  
% 7.71/1.51  ------ SAT Options
% 7.71/1.51  
% 7.71/1.51  --sat_mode                              false
% 7.71/1.51  --sat_fm_restart_options                ""
% 7.71/1.51  --sat_gr_def                            false
% 7.71/1.51  --sat_epr_types                         true
% 7.71/1.51  --sat_non_cyclic_types                  false
% 7.71/1.51  --sat_finite_models                     false
% 7.71/1.51  --sat_fm_lemmas                         false
% 7.71/1.51  --sat_fm_prep                           false
% 7.71/1.51  --sat_fm_uc_incr                        true
% 7.71/1.51  --sat_out_model                         small
% 7.71/1.51  --sat_out_clauses                       false
% 7.71/1.51  
% 7.71/1.51  ------ QBF Options
% 7.71/1.51  
% 7.71/1.51  --qbf_mode                              false
% 7.71/1.51  --qbf_elim_univ                         false
% 7.71/1.51  --qbf_dom_inst                          none
% 7.71/1.51  --qbf_dom_pre_inst                      false
% 7.71/1.51  --qbf_sk_in                             false
% 7.71/1.51  --qbf_pred_elim                         true
% 7.71/1.51  --qbf_split                             512
% 7.71/1.51  
% 7.71/1.51  ------ BMC1 Options
% 7.71/1.51  
% 7.71/1.51  --bmc1_incremental                      false
% 7.71/1.51  --bmc1_axioms                           reachable_all
% 7.71/1.51  --bmc1_min_bound                        0
% 7.71/1.51  --bmc1_max_bound                        -1
% 7.71/1.51  --bmc1_max_bound_default                -1
% 7.71/1.51  --bmc1_symbol_reachability              true
% 7.71/1.51  --bmc1_property_lemmas                  false
% 7.71/1.51  --bmc1_k_induction                      false
% 7.71/1.51  --bmc1_non_equiv_states                 false
% 7.71/1.51  --bmc1_deadlock                         false
% 7.71/1.51  --bmc1_ucm                              false
% 7.71/1.51  --bmc1_add_unsat_core                   none
% 7.71/1.51  --bmc1_unsat_core_children              false
% 7.71/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.71/1.51  --bmc1_out_stat                         full
% 7.71/1.51  --bmc1_ground_init                      false
% 7.71/1.51  --bmc1_pre_inst_next_state              false
% 7.71/1.51  --bmc1_pre_inst_state                   false
% 7.71/1.51  --bmc1_pre_inst_reach_state             false
% 7.71/1.51  --bmc1_out_unsat_core                   false
% 7.71/1.51  --bmc1_aig_witness_out                  false
% 7.71/1.51  --bmc1_verbose                          false
% 7.71/1.51  --bmc1_dump_clauses_tptp                false
% 7.71/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.71/1.51  --bmc1_dump_file                        -
% 7.71/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.71/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.71/1.51  --bmc1_ucm_extend_mode                  1
% 7.71/1.51  --bmc1_ucm_init_mode                    2
% 7.71/1.51  --bmc1_ucm_cone_mode                    none
% 7.71/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.71/1.51  --bmc1_ucm_relax_model                  4
% 7.71/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.71/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.71/1.51  --bmc1_ucm_layered_model                none
% 7.71/1.51  --bmc1_ucm_max_lemma_size               10
% 7.71/1.51  
% 7.71/1.51  ------ AIG Options
% 7.71/1.51  
% 7.71/1.51  --aig_mode                              false
% 7.71/1.51  
% 7.71/1.51  ------ Instantiation Options
% 7.71/1.51  
% 7.71/1.51  --instantiation_flag                    true
% 7.71/1.51  --inst_sos_flag                         false
% 7.71/1.51  --inst_sos_phase                        true
% 7.71/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.71/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.71/1.51  --inst_lit_sel_side                     none
% 7.71/1.51  --inst_solver_per_active                1400
% 7.71/1.51  --inst_solver_calls_frac                1.
% 7.71/1.51  --inst_passive_queue_type               priority_queues
% 7.71/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.71/1.51  --inst_passive_queues_freq              [25;2]
% 7.71/1.51  --inst_dismatching                      true
% 7.71/1.51  --inst_eager_unprocessed_to_passive     true
% 7.71/1.51  --inst_prop_sim_given                   true
% 7.71/1.51  --inst_prop_sim_new                     false
% 7.71/1.51  --inst_subs_new                         false
% 7.71/1.51  --inst_eq_res_simp                      false
% 7.71/1.51  --inst_subs_given                       false
% 7.71/1.51  --inst_orphan_elimination               true
% 7.71/1.51  --inst_learning_loop_flag               true
% 7.71/1.51  --inst_learning_start                   3000
% 7.71/1.51  --inst_learning_factor                  2
% 7.71/1.51  --inst_start_prop_sim_after_learn       3
% 7.71/1.51  --inst_sel_renew                        solver
% 7.71/1.51  --inst_lit_activity_flag                true
% 7.71/1.51  --inst_restr_to_given                   false
% 7.71/1.51  --inst_activity_threshold               500
% 7.71/1.51  --inst_out_proof                        true
% 7.71/1.51  
% 7.71/1.51  ------ Resolution Options
% 7.71/1.51  
% 7.71/1.51  --resolution_flag                       false
% 7.71/1.51  --res_lit_sel                           adaptive
% 7.71/1.51  --res_lit_sel_side                      none
% 7.71/1.51  --res_ordering                          kbo
% 7.71/1.51  --res_to_prop_solver                    active
% 7.71/1.51  --res_prop_simpl_new                    false
% 7.71/1.51  --res_prop_simpl_given                  true
% 7.71/1.51  --res_passive_queue_type                priority_queues
% 7.71/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.71/1.51  --res_passive_queues_freq               [15;5]
% 7.71/1.51  --res_forward_subs                      full
% 7.71/1.51  --res_backward_subs                     full
% 7.71/1.51  --res_forward_subs_resolution           true
% 7.71/1.51  --res_backward_subs_resolution          true
% 7.71/1.51  --res_orphan_elimination                true
% 7.71/1.51  --res_time_limit                        2.
% 7.71/1.51  --res_out_proof                         true
% 7.71/1.51  
% 7.71/1.51  ------ Superposition Options
% 7.71/1.51  
% 7.71/1.51  --superposition_flag                    true
% 7.71/1.51  --sup_passive_queue_type                priority_queues
% 7.71/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.71/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.71/1.51  --demod_completeness_check              fast
% 7.71/1.51  --demod_use_ground                      true
% 7.71/1.51  --sup_to_prop_solver                    passive
% 7.71/1.51  --sup_prop_simpl_new                    true
% 7.71/1.51  --sup_prop_simpl_given                  true
% 7.71/1.51  --sup_fun_splitting                     false
% 7.71/1.51  --sup_smt_interval                      50000
% 7.71/1.51  
% 7.71/1.51  ------ Superposition Simplification Setup
% 7.71/1.51  
% 7.71/1.51  --sup_indices_passive                   []
% 7.71/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.71/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.71/1.51  --sup_full_bw                           [BwDemod]
% 7.71/1.51  --sup_immed_triv                        [TrivRules]
% 7.71/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.71/1.51  --sup_immed_bw_main                     []
% 7.71/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.71/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.71/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.71/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.71/1.51  
% 7.71/1.51  ------ Combination Options
% 7.71/1.51  
% 7.71/1.51  --comb_res_mult                         3
% 7.71/1.51  --comb_sup_mult                         2
% 7.71/1.51  --comb_inst_mult                        10
% 7.71/1.51  
% 7.71/1.51  ------ Debug Options
% 7.71/1.51  
% 7.71/1.51  --dbg_backtrace                         false
% 7.71/1.51  --dbg_dump_prop_clauses                 false
% 7.71/1.51  --dbg_dump_prop_clauses_file            -
% 7.71/1.51  --dbg_out_stat                          false
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  ------ Proving...
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  % SZS status Theorem for theBenchmark.p
% 7.71/1.51  
% 7.71/1.51   Resolution empty clause
% 7.71/1.51  
% 7.71/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.71/1.51  
% 7.71/1.51  fof(f1,axiom,(
% 7.71/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f28,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f1])).
% 7.71/1.51  
% 7.71/1.51  fof(f11,axiom,(
% 7.71/1.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f43,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.71/1.51    inference(cnf_transformation,[],[f11])).
% 7.71/1.51  
% 7.71/1.51  fof(f50,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.71/1.51    inference(definition_unfolding,[],[f28,f43,f43])).
% 7.71/1.51  
% 7.71/1.51  fof(f10,axiom,(
% 7.71/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f42,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 7.71/1.51    inference(cnf_transformation,[],[f10])).
% 7.71/1.51  
% 7.71/1.51  fof(f55,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 7.71/1.51    inference(definition_unfolding,[],[f42,f43])).
% 7.71/1.51  
% 7.71/1.51  fof(f4,axiom,(
% 7.71/1.51    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f36,plain,(
% 7.71/1.51    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 7.71/1.51    inference(cnf_transformation,[],[f4])).
% 7.71/1.51  
% 7.71/1.51  fof(f51,plain,(
% 7.71/1.51    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 7.71/1.51    inference(definition_unfolding,[],[f36,f43])).
% 7.71/1.51  
% 7.71/1.51  fof(f6,axiom,(
% 7.71/1.51    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f38,plain,(
% 7.71/1.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.71/1.51    inference(cnf_transformation,[],[f6])).
% 7.71/1.51  
% 7.71/1.51  fof(f7,axiom,(
% 7.71/1.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f39,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f7])).
% 7.71/1.51  
% 7.71/1.51  fof(f16,axiom,(
% 7.71/1.51    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f48,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f16])).
% 7.71/1.51  
% 7.71/1.51  fof(f52,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) )),
% 7.71/1.51    inference(definition_unfolding,[],[f39,f48])).
% 7.71/1.51  
% 7.71/1.51  fof(f8,axiom,(
% 7.71/1.51    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f40,plain,(
% 7.71/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f8])).
% 7.71/1.51  
% 7.71/1.51  fof(f53,plain,(
% 7.71/1.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 7.71/1.51    inference(definition_unfolding,[],[f40,f48])).
% 7.71/1.51  
% 7.71/1.51  fof(f5,axiom,(
% 7.71/1.51    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f19,plain,(
% 7.71/1.51    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 7.71/1.51    inference(ennf_transformation,[],[f5])).
% 7.71/1.51  
% 7.71/1.51  fof(f37,plain,(
% 7.71/1.51    ( ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f19])).
% 7.71/1.51  
% 7.71/1.51  fof(f2,axiom,(
% 7.71/1.51    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f29,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f2])).
% 7.71/1.51  
% 7.71/1.51  fof(f15,axiom,(
% 7.71/1.51    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f47,plain,(
% 7.71/1.51    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 7.71/1.51    inference(cnf_transformation,[],[f15])).
% 7.71/1.51  
% 7.71/1.51  fof(f14,axiom,(
% 7.71/1.51    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f46,plain,(
% 7.71/1.51    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f14])).
% 7.71/1.51  
% 7.71/1.51  fof(f13,axiom,(
% 7.71/1.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f45,plain,(
% 7.71/1.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.71/1.51    inference(cnf_transformation,[],[f13])).
% 7.71/1.51  
% 7.71/1.51  fof(f17,conjecture,(
% 7.71/1.51    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f18,negated_conjecture,(
% 7.71/1.51    ~! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 7.71/1.51    inference(negated_conjecture,[],[f17])).
% 7.71/1.51  
% 7.71/1.51  fof(f20,plain,(
% 7.71/1.51    ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1)),
% 7.71/1.51    inference(ennf_transformation,[],[f18])).
% 7.71/1.51  
% 7.71/1.51  fof(f26,plain,(
% 7.71/1.51    ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1) => k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != k4_xboole_0(sK1,sK2)),
% 7.71/1.51    introduced(choice_axiom,[])).
% 7.71/1.51  
% 7.71/1.51  fof(f27,plain,(
% 7.71/1.51    k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != k4_xboole_0(sK1,sK2)),
% 7.71/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).
% 7.71/1.51  
% 7.71/1.51  fof(f49,plain,(
% 7.71/1.51    k5_xboole_0(sK1,k3_xboole_0(sK1,sK2)) != k4_xboole_0(sK1,sK2)),
% 7.71/1.51    inference(cnf_transformation,[],[f27])).
% 7.71/1.51  
% 7.71/1.51  fof(f57,plain,(
% 7.71/1.51    k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK1,sK2)),
% 7.71/1.51    inference(definition_unfolding,[],[f49,f43])).
% 7.71/1.51  
% 7.71/1.51  cnf(c_0,plain,
% 7.71/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.71/1.51      inference(cnf_transformation,[],[f50]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_14,plain,
% 7.71/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 7.71/1.51      inference(cnf_transformation,[],[f55]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_742,plain,
% 7.71/1.51      ( k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_0,c_14]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3160,plain,
% 7.71/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_0,c_742]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3239,plain,
% 7.71/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 7.71/1.51      inference(light_normalisation,[status(thm)],[c_3160,c_742]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8,plain,
% 7.71/1.51      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.71/1.51      inference(cnf_transformation,[],[f51]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_10,plain,
% 7.71/1.51      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.71/1.51      inference(cnf_transformation,[],[f38]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_215,plain,
% 7.71/1.51      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.71/1.51      inference(light_normalisation,[status(thm)],[c_8,c_10]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3241,plain,
% 7.71/1.51      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
% 7.71/1.51      inference(demodulation,[status(thm)],[c_3239,c_215]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_11,plain,
% 7.71/1.51      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
% 7.71/1.51      inference(cnf_transformation,[],[f52]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_708,plain,
% 7.71/1.51      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))) ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_11,c_11]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_12,plain,
% 7.71/1.51      ( k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
% 7.71/1.51      inference(cnf_transformation,[],[f53]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_30560,plain,
% 7.71/1.51      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 7.71/1.51      inference(demodulation,[status(thm)],[c_708,c_12,c_3241]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_9,plain,
% 7.71/1.51      ( X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f37]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_30693,plain,
% 7.71/1.51      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))
% 7.71/1.51      | k4_xboole_0(k5_xboole_0(X1,k4_xboole_0(X0,X1)),k5_xboole_0(X0,k4_xboole_0(X1,X0))) != k1_xboole_0 ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_30560,c_9]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_30728,plain,
% 7.71/1.51      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1))
% 7.71/1.51      | k1_xboole_0 != k1_xboole_0 ),
% 7.71/1.51      inference(demodulation,[status(thm)],[c_30693,c_30560]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_30729,plain,
% 7.71/1.51      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 7.71/1.51      inference(equality_resolution_simp,[status(thm)],[c_30728]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1,plain,
% 7.71/1.51      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f29]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_18,plain,
% 7.71/1.51      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.71/1.51      inference(cnf_transformation,[],[f47]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_17,plain,
% 7.71/1.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 7.71/1.51      inference(cnf_transformation,[],[f46]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_924,plain,
% 7.71/1.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_18,c_17]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_16,plain,
% 7.71/1.51      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.71/1.51      inference(cnf_transformation,[],[f45]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_354,plain,
% 7.71/1.51      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_16,c_1]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_940,plain,
% 7.71/1.51      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 7.71/1.51      inference(demodulation,[status(thm)],[c_924,c_354]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1019,plain,
% 7.71/1.51      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1,c_940]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1052,plain,
% 7.71/1.51      ( k5_xboole_0(k5_xboole_0(X0,X1),X0) = X1 ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1019,c_1019]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_32755,plain,
% 7.71/1.51      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_30729,c_1052]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_34265,plain,
% 7.71/1.51      ( k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_3241,c_32755]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_34713,plain,
% 7.71/1.51      ( k5_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 7.71/1.51      inference(light_normalisation,[status(thm)],[c_34265,c_16]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_19,negated_conjecture,
% 7.71/1.51      ( k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK1,sK2) ),
% 7.71/1.51      inference(cnf_transformation,[],[f57]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_43711,plain,
% 7.71/1.51      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK1,sK2) ),
% 7.71/1.51      inference(demodulation,[status(thm)],[c_34713,c_19]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_43712,plain,
% 7.71/1.51      ( k4_xboole_0(sK1,sK2) != k4_xboole_0(sK1,sK2) ),
% 7.71/1.51      inference(demodulation,[status(thm)],[c_43711,c_14]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_43713,plain,
% 7.71/1.51      ( $false ),
% 7.71/1.51      inference(equality_resolution_simp,[status(thm)],[c_43712]) ).
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.71/1.51  
% 7.71/1.51  ------                               Statistics
% 7.71/1.51  
% 7.71/1.51  ------ General
% 7.71/1.51  
% 7.71/1.51  abstr_ref_over_cycles:                  0
% 7.71/1.51  abstr_ref_under_cycles:                 0
% 7.71/1.51  gc_basic_clause_elim:                   0
% 7.71/1.51  forced_gc_time:                         0
% 7.71/1.51  parsing_time:                           0.01
% 7.71/1.51  unif_index_cands_time:                  0.
% 7.71/1.51  unif_index_add_time:                    0.
% 7.71/1.51  orderings_time:                         0.
% 7.71/1.51  out_proof_time:                         0.007
% 7.71/1.51  total_time:                             0.945
% 7.71/1.51  num_of_symbols:                         38
% 7.71/1.51  num_of_terms:                           43276
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing
% 7.71/1.51  
% 7.71/1.51  num_of_splits:                          0
% 7.71/1.51  num_of_split_atoms:                     0
% 7.71/1.51  num_of_reused_defs:                     0
% 7.71/1.51  num_eq_ax_congr_red:                    6
% 7.71/1.51  num_of_sem_filtered_clauses:            1
% 7.71/1.51  num_of_subtypes:                        0
% 7.71/1.51  monotx_restored_types:                  0
% 7.71/1.51  sat_num_of_epr_types:                   0
% 7.71/1.51  sat_num_of_non_cyclic_types:            0
% 7.71/1.51  sat_guarded_non_collapsed_types:        0
% 7.71/1.51  num_pure_diseq_elim:                    0
% 7.71/1.51  simp_replaced_by:                       0
% 7.71/1.51  res_preprocessed:                       71
% 7.71/1.51  prep_upred:                             0
% 7.71/1.51  prep_unflattend:                        0
% 7.71/1.51  smt_new_axioms:                         0
% 7.71/1.51  pred_elim_cands:                        1
% 7.71/1.51  pred_elim:                              0
% 7.71/1.51  pred_elim_cl:                           0
% 7.71/1.51  pred_elim_cycles:                       1
% 7.71/1.51  merged_defs:                            0
% 7.71/1.51  merged_defs_ncl:                        0
% 7.71/1.51  bin_hyper_res:                          0
% 7.71/1.51  prep_cycles:                            3
% 7.71/1.51  pred_elim_time:                         0.
% 7.71/1.51  splitting_time:                         0.
% 7.71/1.51  sem_filter_time:                        0.
% 7.71/1.51  monotx_time:                            0.001
% 7.71/1.51  subtype_inf_time:                       0.
% 7.71/1.51  
% 7.71/1.51  ------ Problem properties
% 7.71/1.51  
% 7.71/1.51  clauses:                                20
% 7.71/1.51  conjectures:                            1
% 7.71/1.51  epr:                                    0
% 7.71/1.51  horn:                                   16
% 7.71/1.51  ground:                                 1
% 7.71/1.51  unary:                                  13
% 7.71/1.51  binary:                                 3
% 7.71/1.51  lits:                                   32
% 7.71/1.51  lits_eq:                                18
% 7.71/1.51  fd_pure:                                0
% 7.71/1.51  fd_pseudo:                              0
% 7.71/1.51  fd_cond:                                0
% 7.71/1.51  fd_pseudo_cond:                         4
% 7.71/1.51  ac_symbols:                             1
% 7.71/1.51  
% 7.71/1.51  ------ Propositional Solver
% 7.71/1.51  
% 7.71/1.51  prop_solver_calls:                      25
% 7.71/1.51  prop_fast_solver_calls:                 422
% 7.71/1.51  smt_solver_calls:                       0
% 7.71/1.51  smt_fast_solver_calls:                  0
% 7.71/1.51  prop_num_of_clauses:                    7639
% 7.71/1.51  prop_preprocess_simplified:             9080
% 7.71/1.51  prop_fo_subsumed:                       1
% 7.71/1.51  prop_solver_time:                       0.
% 7.71/1.51  smt_solver_time:                        0.
% 7.71/1.51  smt_fast_solver_time:                   0.
% 7.71/1.51  prop_fast_solver_time:                  0.
% 7.71/1.51  prop_unsat_core_time:                   0.
% 7.71/1.51  
% 7.71/1.51  ------ QBF
% 7.71/1.51  
% 7.71/1.51  qbf_q_res:                              0
% 7.71/1.51  qbf_num_tautologies:                    0
% 7.71/1.51  qbf_prep_cycles:                        0
% 7.71/1.51  
% 7.71/1.51  ------ BMC1
% 7.71/1.51  
% 7.71/1.51  bmc1_current_bound:                     -1
% 7.71/1.51  bmc1_last_solved_bound:                 -1
% 7.71/1.51  bmc1_unsat_core_size:                   -1
% 7.71/1.51  bmc1_unsat_core_parents_size:           -1
% 7.71/1.51  bmc1_merge_next_fun:                    0
% 7.71/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.71/1.51  
% 7.71/1.51  ------ Instantiation
% 7.71/1.51  
% 7.71/1.51  inst_num_of_clauses:                    1331
% 7.71/1.51  inst_num_in_passive:                    537
% 7.71/1.51  inst_num_in_active:                     456
% 7.71/1.51  inst_num_in_unprocessed:                339
% 7.71/1.51  inst_num_of_loops:                      690
% 7.71/1.51  inst_num_of_learning_restarts:          0
% 7.71/1.51  inst_num_moves_active_passive:          229
% 7.71/1.51  inst_lit_activity:                      0
% 7.71/1.51  inst_lit_activity_moves:                0
% 7.71/1.51  inst_num_tautologies:                   0
% 7.71/1.51  inst_num_prop_implied:                  0
% 7.71/1.51  inst_num_existing_simplified:           0
% 7.71/1.51  inst_num_eq_res_simplified:             0
% 7.71/1.51  inst_num_child_elim:                    0
% 7.71/1.51  inst_num_of_dismatching_blockings:      1101
% 7.71/1.51  inst_num_of_non_proper_insts:           1564
% 7.71/1.51  inst_num_of_duplicates:                 0
% 7.71/1.51  inst_inst_num_from_inst_to_res:         0
% 7.71/1.51  inst_dismatching_checking_time:         0.
% 7.71/1.51  
% 7.71/1.51  ------ Resolution
% 7.71/1.51  
% 7.71/1.51  res_num_of_clauses:                     0
% 7.71/1.51  res_num_in_passive:                     0
% 7.71/1.51  res_num_in_active:                      0
% 7.71/1.51  res_num_of_loops:                       74
% 7.71/1.51  res_forward_subset_subsumed:            189
% 7.71/1.51  res_backward_subset_subsumed:           12
% 7.71/1.51  res_forward_subsumed:                   0
% 7.71/1.51  res_backward_subsumed:                  0
% 7.71/1.51  res_forward_subsumption_resolution:     0
% 7.71/1.51  res_backward_subsumption_resolution:    0
% 7.71/1.51  res_clause_to_clause_subsumption:       77441
% 7.71/1.51  res_orphan_elimination:                 0
% 7.71/1.51  res_tautology_del:                      150
% 7.71/1.51  res_num_eq_res_simplified:              0
% 7.71/1.51  res_num_sel_changes:                    0
% 7.71/1.51  res_moves_from_active_to_pass:          0
% 7.71/1.51  
% 7.71/1.51  ------ Superposition
% 7.71/1.51  
% 7.71/1.51  sup_time_total:                         0.
% 7.71/1.51  sup_time_generating:                    0.
% 7.71/1.51  sup_time_sim_full:                      0.
% 7.71/1.51  sup_time_sim_immed:                     0.
% 7.71/1.51  
% 7.71/1.51  sup_num_of_clauses:                     3099
% 7.71/1.51  sup_num_in_active:                      128
% 7.71/1.51  sup_num_in_passive:                     2971
% 7.71/1.51  sup_num_of_loops:                       136
% 7.71/1.51  sup_fw_superposition:                   9297
% 7.71/1.51  sup_bw_superposition:                   8035
% 7.71/1.51  sup_immediate_simplified:               5208
% 7.71/1.51  sup_given_eliminated:                   2
% 7.71/1.51  comparisons_done:                       0
% 7.71/1.51  comparisons_avoided:                    0
% 7.71/1.51  
% 7.71/1.51  ------ Simplifications
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  sim_fw_subset_subsumed:                 20
% 7.71/1.51  sim_bw_subset_subsumed:                 8
% 7.71/1.51  sim_fw_subsumed:                        692
% 7.71/1.51  sim_bw_subsumed:                        4
% 7.71/1.51  sim_fw_subsumption_res:                 0
% 7.71/1.51  sim_bw_subsumption_res:                 0
% 7.71/1.51  sim_tautology_del:                      47
% 7.71/1.51  sim_eq_tautology_del:                   1378
% 7.71/1.51  sim_eq_res_simp:                        2
% 7.71/1.51  sim_fw_demodulated:                     2405
% 7.71/1.51  sim_bw_demodulated:                     159
% 7.71/1.51  sim_light_normalised:                   2498
% 7.71/1.51  sim_joinable_taut:                      229
% 7.71/1.51  sim_joinable_simp:                      0
% 7.71/1.51  sim_ac_normalised:                      0
% 7.71/1.51  sim_smt_subsumption:                    0
% 7.71/1.51  
%------------------------------------------------------------------------------
