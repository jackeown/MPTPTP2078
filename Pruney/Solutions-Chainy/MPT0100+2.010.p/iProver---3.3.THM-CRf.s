%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:56 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 619 expanded)
%              Number of clauses        :   40 ( 254 expanded)
%              Number of leaves         :   10 ( 160 expanded)
%              Depth                    :   18
%              Number of atoms          :   73 ( 704 expanded)
%              Number of equality atoms :   64 ( 591 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f13,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f14,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f25,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f28,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f25,f17,f23])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f19,f23])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_6,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_60,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_97,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_3,c_60])).

cnf(c_7,negated_conjecture,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_52,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
    inference(theory_normalisation,[status(thm)],[c_7,c_6,c_0])).

cnf(c_3783,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_97,c_52])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_2,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_40,plain,
    ( X0 != X1
    | k4_xboole_0(X0,k4_xboole_0(X0,X2)) != X3
    | k2_xboole_0(X3,X1) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_41,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0 ),
    inference(unflattening,[status(thm)],[c_40])).

cnf(c_51,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(theory_normalisation,[status(thm)],[c_41,c_6,c_0])).

cnf(c_76,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_51])).

cnf(c_89,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_76,c_3])).

cnf(c_61,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_122,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_89,c_61])).

cnf(c_287,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(superposition,[status(thm)],[c_3,c_122])).

cnf(c_334,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_287,c_122])).

cnf(c_478,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_334,c_60])).

cnf(c_99,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_89,c_60])).

cnf(c_180,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3,c_99])).

cnf(c_120,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_3,c_61])).

cnf(c_211,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
    inference(demodulation,[status(thm)],[c_180,c_3,c_120])).

cnf(c_746,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_211,c_0])).

cnf(c_121,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
    inference(superposition,[status(thm)],[c_76,c_61])).

cnf(c_1540,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_746,c_121])).

cnf(c_110,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_6,c_89])).

cnf(c_111,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_110,c_99])).

cnf(c_62,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_262,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_111,c_62])).

cnf(c_357,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_111,c_262])).

cnf(c_372,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_262,c_62])).

cnf(c_388,plain,
    ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_357,c_262,c_372])).

cnf(c_1145,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_388,c_121])).

cnf(c_1207,plain,
    ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_1145,c_122])).

cnf(c_1547,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_1540,c_1207])).

cnf(c_3784,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3783,c_478,c_1547])).

cnf(c_3785,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3784])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:16:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.52/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/0.98  
% 2.52/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.52/0.98  
% 2.52/0.98  ------  iProver source info
% 2.52/0.98  
% 2.52/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.52/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.52/0.98  git: non_committed_changes: false
% 2.52/0.98  git: last_make_outside_of_git: false
% 2.52/0.98  
% 2.52/0.98  ------ 
% 2.52/0.98  
% 2.52/0.98  ------ Input Options
% 2.52/0.98  
% 2.52/0.98  --out_options                           all
% 2.52/0.98  --tptp_safe_out                         true
% 2.52/0.98  --problem_path                          ""
% 2.52/0.98  --include_path                          ""
% 2.52/0.98  --clausifier                            res/vclausify_rel
% 2.52/0.98  --clausifier_options                    --mode clausify
% 2.52/0.98  --stdin                                 false
% 2.52/0.98  --stats_out                             all
% 2.52/0.98  
% 2.52/0.98  ------ General Options
% 2.52/0.98  
% 2.52/0.98  --fof                                   false
% 2.52/0.98  --time_out_real                         305.
% 2.52/0.98  --time_out_virtual                      -1.
% 2.52/0.98  --symbol_type_check                     false
% 2.52/0.98  --clausify_out                          false
% 2.52/0.98  --sig_cnt_out                           false
% 2.52/0.98  --trig_cnt_out                          false
% 2.52/0.98  --trig_cnt_out_tolerance                1.
% 2.52/0.98  --trig_cnt_out_sk_spl                   false
% 2.52/0.98  --abstr_cl_out                          false
% 2.52/0.98  
% 2.52/0.98  ------ Global Options
% 2.52/0.98  
% 2.52/0.98  --schedule                              default
% 2.52/0.98  --add_important_lit                     false
% 2.52/0.98  --prop_solver_per_cl                    1000
% 2.52/0.98  --min_unsat_core                        false
% 2.52/0.98  --soft_assumptions                      false
% 2.52/0.98  --soft_lemma_size                       3
% 2.52/0.98  --prop_impl_unit_size                   0
% 2.52/0.98  --prop_impl_unit                        []
% 2.52/0.98  --share_sel_clauses                     true
% 2.52/0.98  --reset_solvers                         false
% 2.52/0.98  --bc_imp_inh                            [conj_cone]
% 2.52/0.98  --conj_cone_tolerance                   3.
% 2.52/0.98  --extra_neg_conj                        none
% 2.52/0.98  --large_theory_mode                     true
% 2.52/0.98  --prolific_symb_bound                   200
% 2.52/0.98  --lt_threshold                          2000
% 2.52/0.98  --clause_weak_htbl                      true
% 2.52/0.98  --gc_record_bc_elim                     false
% 2.52/0.98  
% 2.52/0.98  ------ Preprocessing Options
% 2.52/0.98  
% 2.52/0.98  --preprocessing_flag                    true
% 2.52/0.98  --time_out_prep_mult                    0.1
% 2.52/0.98  --splitting_mode                        input
% 2.52/0.98  --splitting_grd                         true
% 2.52/0.98  --splitting_cvd                         false
% 2.52/0.98  --splitting_cvd_svl                     false
% 2.52/0.98  --splitting_nvd                         32
% 2.52/0.98  --sub_typing                            true
% 2.52/0.98  --prep_gs_sim                           true
% 2.52/0.98  --prep_unflatten                        true
% 2.52/0.98  --prep_res_sim                          true
% 2.52/0.98  --prep_upred                            true
% 2.52/0.98  --prep_sem_filter                       exhaustive
% 2.52/0.98  --prep_sem_filter_out                   false
% 2.52/0.98  --pred_elim                             true
% 2.52/0.98  --res_sim_input                         true
% 2.52/0.98  --eq_ax_congr_red                       true
% 2.52/0.98  --pure_diseq_elim                       true
% 2.52/0.98  --brand_transform                       false
% 2.52/0.98  --non_eq_to_eq                          false
% 2.52/0.98  --prep_def_merge                        true
% 2.52/0.98  --prep_def_merge_prop_impl              false
% 2.52/0.98  --prep_def_merge_mbd                    true
% 2.52/0.98  --prep_def_merge_tr_red                 false
% 2.52/0.98  --prep_def_merge_tr_cl                  false
% 2.52/0.98  --smt_preprocessing                     true
% 2.52/0.98  --smt_ac_axioms                         fast
% 2.52/0.98  --preprocessed_out                      false
% 2.52/0.98  --preprocessed_stats                    false
% 2.52/0.98  
% 2.52/0.98  ------ Abstraction refinement Options
% 2.52/0.98  
% 2.52/0.98  --abstr_ref                             []
% 2.52/0.98  --abstr_ref_prep                        false
% 2.52/0.98  --abstr_ref_until_sat                   false
% 2.52/0.98  --abstr_ref_sig_restrict                funpre
% 2.52/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/0.98  --abstr_ref_under                       []
% 2.52/0.98  
% 2.52/0.98  ------ SAT Options
% 2.52/0.98  
% 2.52/0.98  --sat_mode                              false
% 2.52/0.98  --sat_fm_restart_options                ""
% 2.52/0.98  --sat_gr_def                            false
% 2.52/0.98  --sat_epr_types                         true
% 2.52/0.98  --sat_non_cyclic_types                  false
% 2.52/0.98  --sat_finite_models                     false
% 2.52/0.98  --sat_fm_lemmas                         false
% 2.52/0.98  --sat_fm_prep                           false
% 2.52/0.98  --sat_fm_uc_incr                        true
% 2.52/0.98  --sat_out_model                         small
% 2.52/0.98  --sat_out_clauses                       false
% 2.52/0.98  
% 2.52/0.98  ------ QBF Options
% 2.52/0.98  
% 2.52/0.98  --qbf_mode                              false
% 2.52/0.98  --qbf_elim_univ                         false
% 2.52/0.98  --qbf_dom_inst                          none
% 2.52/0.98  --qbf_dom_pre_inst                      false
% 2.52/0.98  --qbf_sk_in                             false
% 2.52/0.98  --qbf_pred_elim                         true
% 2.52/0.98  --qbf_split                             512
% 2.52/0.98  
% 2.52/0.98  ------ BMC1 Options
% 2.52/0.98  
% 2.52/0.98  --bmc1_incremental                      false
% 2.52/0.98  --bmc1_axioms                           reachable_all
% 2.52/0.98  --bmc1_min_bound                        0
% 2.52/0.98  --bmc1_max_bound                        -1
% 2.52/0.98  --bmc1_max_bound_default                -1
% 2.52/0.98  --bmc1_symbol_reachability              true
% 2.52/0.98  --bmc1_property_lemmas                  false
% 2.52/0.98  --bmc1_k_induction                      false
% 2.52/0.98  --bmc1_non_equiv_states                 false
% 2.52/0.98  --bmc1_deadlock                         false
% 2.52/0.98  --bmc1_ucm                              false
% 2.52/0.98  --bmc1_add_unsat_core                   none
% 2.52/0.98  --bmc1_unsat_core_children              false
% 2.52/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/0.98  --bmc1_out_stat                         full
% 2.52/0.98  --bmc1_ground_init                      false
% 2.52/0.98  --bmc1_pre_inst_next_state              false
% 2.52/0.98  --bmc1_pre_inst_state                   false
% 2.52/0.98  --bmc1_pre_inst_reach_state             false
% 2.52/0.98  --bmc1_out_unsat_core                   false
% 2.52/0.98  --bmc1_aig_witness_out                  false
% 2.52/0.98  --bmc1_verbose                          false
% 2.52/0.98  --bmc1_dump_clauses_tptp                false
% 2.52/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.52/0.98  --bmc1_dump_file                        -
% 2.52/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.52/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.52/0.98  --bmc1_ucm_extend_mode                  1
% 2.52/0.98  --bmc1_ucm_init_mode                    2
% 2.52/0.98  --bmc1_ucm_cone_mode                    none
% 2.52/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.52/0.98  --bmc1_ucm_relax_model                  4
% 2.52/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.52/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/0.98  --bmc1_ucm_layered_model                none
% 2.52/0.98  --bmc1_ucm_max_lemma_size               10
% 2.52/0.98  
% 2.52/0.98  ------ AIG Options
% 2.52/0.98  
% 2.52/0.98  --aig_mode                              false
% 2.52/0.98  
% 2.52/0.98  ------ Instantiation Options
% 2.52/0.98  
% 2.52/0.98  --instantiation_flag                    true
% 2.52/0.98  --inst_sos_flag                         false
% 2.52/0.98  --inst_sos_phase                        true
% 2.52/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/0.98  --inst_lit_sel_side                     num_symb
% 2.52/0.98  --inst_solver_per_active                1400
% 2.52/0.98  --inst_solver_calls_frac                1.
% 2.52/0.98  --inst_passive_queue_type               priority_queues
% 2.52/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/0.98  --inst_passive_queues_freq              [25;2]
% 2.52/0.98  --inst_dismatching                      true
% 2.52/0.98  --inst_eager_unprocessed_to_passive     true
% 2.52/0.98  --inst_prop_sim_given                   true
% 2.52/0.98  --inst_prop_sim_new                     false
% 2.52/0.98  --inst_subs_new                         false
% 2.52/0.98  --inst_eq_res_simp                      false
% 2.52/0.98  --inst_subs_given                       false
% 2.52/0.98  --inst_orphan_elimination               true
% 2.52/0.98  --inst_learning_loop_flag               true
% 2.52/0.98  --inst_learning_start                   3000
% 2.52/0.98  --inst_learning_factor                  2
% 2.52/0.98  --inst_start_prop_sim_after_learn       3
% 2.52/0.98  --inst_sel_renew                        solver
% 2.52/0.98  --inst_lit_activity_flag                true
% 2.52/0.98  --inst_restr_to_given                   false
% 2.52/0.98  --inst_activity_threshold               500
% 2.52/0.98  --inst_out_proof                        true
% 2.52/0.98  
% 2.52/0.98  ------ Resolution Options
% 2.52/0.98  
% 2.52/0.98  --resolution_flag                       true
% 2.52/0.98  --res_lit_sel                           adaptive
% 2.52/0.98  --res_lit_sel_side                      none
% 2.52/0.98  --res_ordering                          kbo
% 2.52/0.98  --res_to_prop_solver                    active
% 2.52/0.98  --res_prop_simpl_new                    false
% 2.52/0.98  --res_prop_simpl_given                  true
% 2.52/0.98  --res_passive_queue_type                priority_queues
% 2.52/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/0.98  --res_passive_queues_freq               [15;5]
% 2.52/0.98  --res_forward_subs                      full
% 2.52/0.98  --res_backward_subs                     full
% 2.52/0.98  --res_forward_subs_resolution           true
% 2.52/0.98  --res_backward_subs_resolution          true
% 2.52/0.98  --res_orphan_elimination                true
% 2.52/0.98  --res_time_limit                        2.
% 2.52/0.98  --res_out_proof                         true
% 2.52/0.98  
% 2.52/0.98  ------ Superposition Options
% 2.52/0.98  
% 2.52/0.98  --superposition_flag                    true
% 2.52/0.98  --sup_passive_queue_type                priority_queues
% 2.52/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.52/0.98  --demod_completeness_check              fast
% 2.52/0.98  --demod_use_ground                      true
% 2.52/0.98  --sup_to_prop_solver                    passive
% 2.52/0.98  --sup_prop_simpl_new                    true
% 2.52/0.98  --sup_prop_simpl_given                  true
% 2.52/0.98  --sup_fun_splitting                     false
% 2.52/0.98  --sup_smt_interval                      50000
% 2.52/0.99  
% 2.52/0.99  ------ Superposition Simplification Setup
% 2.52/0.99  
% 2.52/0.99  --sup_indices_passive                   []
% 2.52/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.52/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.99  --sup_full_bw                           [BwDemod]
% 2.52/0.99  --sup_immed_triv                        [TrivRules]
% 2.52/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.99  --sup_immed_bw_main                     []
% 2.52/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.52/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.52/0.99  
% 2.52/0.99  ------ Combination Options
% 2.52/0.99  
% 2.52/0.99  --comb_res_mult                         3
% 2.52/0.99  --comb_sup_mult                         2
% 2.52/0.99  --comb_inst_mult                        10
% 2.52/0.99  
% 2.52/0.99  ------ Debug Options
% 2.52/0.99  
% 2.52/0.99  --dbg_backtrace                         false
% 2.52/0.99  --dbg_dump_prop_clauses                 false
% 2.52/0.99  --dbg_dump_prop_clauses_file            -
% 2.52/0.99  --dbg_out_stat                          false
% 2.52/0.99  ------ Parsing...
% 2.52/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.52/0.99  ------ Proving...
% 2.52/0.99  ------ Problem Properties 
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  clauses                                 7
% 2.52/0.99  conjectures                             1
% 2.52/0.99  EPR                                     0
% 2.52/0.99  Horn                                    7
% 2.52/0.99  unary                                   7
% 2.52/0.99  binary                                  0
% 2.52/0.99  lits                                    7
% 2.52/0.99  lits eq                                 7
% 2.52/0.99  fd_pure                                 0
% 2.52/0.99  fd_pseudo                               0
% 2.52/0.99  fd_cond                                 0
% 2.52/0.99  fd_pseudo_cond                          0
% 2.52/0.99  AC symbols                              1
% 2.52/0.99  
% 2.52/0.99  ------ Schedule UEQ
% 2.52/0.99  
% 2.52/0.99  ------ pure equality problem: resolution off 
% 2.52/0.99  
% 2.52/0.99  ------ Option_UEQ Time Limit: Unbounded
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  ------ 
% 2.52/0.99  Current options:
% 2.52/0.99  ------ 
% 2.52/0.99  
% 2.52/0.99  ------ Input Options
% 2.52/0.99  
% 2.52/0.99  --out_options                           all
% 2.52/0.99  --tptp_safe_out                         true
% 2.52/0.99  --problem_path                          ""
% 2.52/0.99  --include_path                          ""
% 2.52/0.99  --clausifier                            res/vclausify_rel
% 2.52/0.99  --clausifier_options                    --mode clausify
% 2.52/0.99  --stdin                                 false
% 2.52/0.99  --stats_out                             all
% 2.52/0.99  
% 2.52/0.99  ------ General Options
% 2.52/0.99  
% 2.52/0.99  --fof                                   false
% 2.52/0.99  --time_out_real                         305.
% 2.52/0.99  --time_out_virtual                      -1.
% 2.52/0.99  --symbol_type_check                     false
% 2.52/0.99  --clausify_out                          false
% 2.52/0.99  --sig_cnt_out                           false
% 2.52/0.99  --trig_cnt_out                          false
% 2.52/0.99  --trig_cnt_out_tolerance                1.
% 2.52/0.99  --trig_cnt_out_sk_spl                   false
% 2.52/0.99  --abstr_cl_out                          false
% 2.52/0.99  
% 2.52/0.99  ------ Global Options
% 2.52/0.99  
% 2.52/0.99  --schedule                              default
% 2.52/0.99  --add_important_lit                     false
% 2.52/0.99  --prop_solver_per_cl                    1000
% 2.52/0.99  --min_unsat_core                        false
% 2.52/0.99  --soft_assumptions                      false
% 2.52/0.99  --soft_lemma_size                       3
% 2.52/0.99  --prop_impl_unit_size                   0
% 2.52/0.99  --prop_impl_unit                        []
% 2.52/0.99  --share_sel_clauses                     true
% 2.52/0.99  --reset_solvers                         false
% 2.52/0.99  --bc_imp_inh                            [conj_cone]
% 2.52/0.99  --conj_cone_tolerance                   3.
% 2.52/0.99  --extra_neg_conj                        none
% 2.52/0.99  --large_theory_mode                     true
% 2.52/0.99  --prolific_symb_bound                   200
% 2.52/0.99  --lt_threshold                          2000
% 2.52/0.99  --clause_weak_htbl                      true
% 2.52/0.99  --gc_record_bc_elim                     false
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing Options
% 2.52/0.99  
% 2.52/0.99  --preprocessing_flag                    true
% 2.52/0.99  --time_out_prep_mult                    0.1
% 2.52/0.99  --splitting_mode                        input
% 2.52/0.99  --splitting_grd                         true
% 2.52/0.99  --splitting_cvd                         false
% 2.52/0.99  --splitting_cvd_svl                     false
% 2.52/0.99  --splitting_nvd                         32
% 2.52/0.99  --sub_typing                            true
% 2.52/0.99  --prep_gs_sim                           true
% 2.52/0.99  --prep_unflatten                        true
% 2.52/0.99  --prep_res_sim                          true
% 2.52/0.99  --prep_upred                            true
% 2.52/0.99  --prep_sem_filter                       exhaustive
% 2.52/0.99  --prep_sem_filter_out                   false
% 2.52/0.99  --pred_elim                             true
% 2.52/0.99  --res_sim_input                         true
% 2.52/0.99  --eq_ax_congr_red                       true
% 2.52/0.99  --pure_diseq_elim                       true
% 2.52/0.99  --brand_transform                       false
% 2.52/0.99  --non_eq_to_eq                          false
% 2.52/0.99  --prep_def_merge                        true
% 2.52/0.99  --prep_def_merge_prop_impl              false
% 2.52/0.99  --prep_def_merge_mbd                    true
% 2.52/0.99  --prep_def_merge_tr_red                 false
% 2.52/0.99  --prep_def_merge_tr_cl                  false
% 2.52/0.99  --smt_preprocessing                     true
% 2.52/0.99  --smt_ac_axioms                         fast
% 2.52/0.99  --preprocessed_out                      false
% 2.52/0.99  --preprocessed_stats                    false
% 2.52/0.99  
% 2.52/0.99  ------ Abstraction refinement Options
% 2.52/0.99  
% 2.52/0.99  --abstr_ref                             []
% 2.52/0.99  --abstr_ref_prep                        false
% 2.52/0.99  --abstr_ref_until_sat                   false
% 2.52/0.99  --abstr_ref_sig_restrict                funpre
% 2.52/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.52/0.99  --abstr_ref_under                       []
% 2.52/0.99  
% 2.52/0.99  ------ SAT Options
% 2.52/0.99  
% 2.52/0.99  --sat_mode                              false
% 2.52/0.99  --sat_fm_restart_options                ""
% 2.52/0.99  --sat_gr_def                            false
% 2.52/0.99  --sat_epr_types                         true
% 2.52/0.99  --sat_non_cyclic_types                  false
% 2.52/0.99  --sat_finite_models                     false
% 2.52/0.99  --sat_fm_lemmas                         false
% 2.52/0.99  --sat_fm_prep                           false
% 2.52/0.99  --sat_fm_uc_incr                        true
% 2.52/0.99  --sat_out_model                         small
% 2.52/0.99  --sat_out_clauses                       false
% 2.52/0.99  
% 2.52/0.99  ------ QBF Options
% 2.52/0.99  
% 2.52/0.99  --qbf_mode                              false
% 2.52/0.99  --qbf_elim_univ                         false
% 2.52/0.99  --qbf_dom_inst                          none
% 2.52/0.99  --qbf_dom_pre_inst                      false
% 2.52/0.99  --qbf_sk_in                             false
% 2.52/0.99  --qbf_pred_elim                         true
% 2.52/0.99  --qbf_split                             512
% 2.52/0.99  
% 2.52/0.99  ------ BMC1 Options
% 2.52/0.99  
% 2.52/0.99  --bmc1_incremental                      false
% 2.52/0.99  --bmc1_axioms                           reachable_all
% 2.52/0.99  --bmc1_min_bound                        0
% 2.52/0.99  --bmc1_max_bound                        -1
% 2.52/0.99  --bmc1_max_bound_default                -1
% 2.52/0.99  --bmc1_symbol_reachability              true
% 2.52/0.99  --bmc1_property_lemmas                  false
% 2.52/0.99  --bmc1_k_induction                      false
% 2.52/0.99  --bmc1_non_equiv_states                 false
% 2.52/0.99  --bmc1_deadlock                         false
% 2.52/0.99  --bmc1_ucm                              false
% 2.52/0.99  --bmc1_add_unsat_core                   none
% 2.52/0.99  --bmc1_unsat_core_children              false
% 2.52/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.52/0.99  --bmc1_out_stat                         full
% 2.52/0.99  --bmc1_ground_init                      false
% 2.52/0.99  --bmc1_pre_inst_next_state              false
% 2.52/0.99  --bmc1_pre_inst_state                   false
% 2.52/0.99  --bmc1_pre_inst_reach_state             false
% 2.52/0.99  --bmc1_out_unsat_core                   false
% 2.52/0.99  --bmc1_aig_witness_out                  false
% 2.52/0.99  --bmc1_verbose                          false
% 2.52/0.99  --bmc1_dump_clauses_tptp                false
% 2.52/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.52/0.99  --bmc1_dump_file                        -
% 2.52/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.52/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.52/0.99  --bmc1_ucm_extend_mode                  1
% 2.52/0.99  --bmc1_ucm_init_mode                    2
% 2.52/0.99  --bmc1_ucm_cone_mode                    none
% 2.52/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.52/0.99  --bmc1_ucm_relax_model                  4
% 2.52/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.52/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.52/0.99  --bmc1_ucm_layered_model                none
% 2.52/0.99  --bmc1_ucm_max_lemma_size               10
% 2.52/0.99  
% 2.52/0.99  ------ AIG Options
% 2.52/0.99  
% 2.52/0.99  --aig_mode                              false
% 2.52/0.99  
% 2.52/0.99  ------ Instantiation Options
% 2.52/0.99  
% 2.52/0.99  --instantiation_flag                    false
% 2.52/0.99  --inst_sos_flag                         false
% 2.52/0.99  --inst_sos_phase                        true
% 2.52/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.52/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.52/0.99  --inst_lit_sel_side                     num_symb
% 2.52/0.99  --inst_solver_per_active                1400
% 2.52/0.99  --inst_solver_calls_frac                1.
% 2.52/0.99  --inst_passive_queue_type               priority_queues
% 2.52/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.52/0.99  --inst_passive_queues_freq              [25;2]
% 2.52/0.99  --inst_dismatching                      true
% 2.52/0.99  --inst_eager_unprocessed_to_passive     true
% 2.52/0.99  --inst_prop_sim_given                   true
% 2.52/0.99  --inst_prop_sim_new                     false
% 2.52/0.99  --inst_subs_new                         false
% 2.52/0.99  --inst_eq_res_simp                      false
% 2.52/0.99  --inst_subs_given                       false
% 2.52/0.99  --inst_orphan_elimination               true
% 2.52/0.99  --inst_learning_loop_flag               true
% 2.52/0.99  --inst_learning_start                   3000
% 2.52/0.99  --inst_learning_factor                  2
% 2.52/0.99  --inst_start_prop_sim_after_learn       3
% 2.52/0.99  --inst_sel_renew                        solver
% 2.52/0.99  --inst_lit_activity_flag                true
% 2.52/0.99  --inst_restr_to_given                   false
% 2.52/0.99  --inst_activity_threshold               500
% 2.52/0.99  --inst_out_proof                        true
% 2.52/0.99  
% 2.52/0.99  ------ Resolution Options
% 2.52/0.99  
% 2.52/0.99  --resolution_flag                       false
% 2.52/0.99  --res_lit_sel                           adaptive
% 2.52/0.99  --res_lit_sel_side                      none
% 2.52/0.99  --res_ordering                          kbo
% 2.52/0.99  --res_to_prop_solver                    active
% 2.52/0.99  --res_prop_simpl_new                    false
% 2.52/0.99  --res_prop_simpl_given                  true
% 2.52/0.99  --res_passive_queue_type                priority_queues
% 2.52/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.52/0.99  --res_passive_queues_freq               [15;5]
% 2.52/0.99  --res_forward_subs                      full
% 2.52/0.99  --res_backward_subs                     full
% 2.52/0.99  --res_forward_subs_resolution           true
% 2.52/0.99  --res_backward_subs_resolution          true
% 2.52/0.99  --res_orphan_elimination                true
% 2.52/0.99  --res_time_limit                        2.
% 2.52/0.99  --res_out_proof                         true
% 2.52/0.99  
% 2.52/0.99  ------ Superposition Options
% 2.52/0.99  
% 2.52/0.99  --superposition_flag                    true
% 2.52/0.99  --sup_passive_queue_type                priority_queues
% 2.52/0.99  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.52/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.52/0.99  --demod_completeness_check              fast
% 2.52/0.99  --demod_use_ground                      true
% 2.52/0.99  --sup_to_prop_solver                    active
% 2.52/0.99  --sup_prop_simpl_new                    false
% 2.52/0.99  --sup_prop_simpl_given                  false
% 2.52/0.99  --sup_fun_splitting                     true
% 2.52/0.99  --sup_smt_interval                      10000
% 2.52/0.99  
% 2.52/0.99  ------ Superposition Simplification Setup
% 2.52/0.99  
% 2.52/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.52/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.52/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.52/0.99  --sup_full_triv                         [TrivRules]
% 2.52/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.52/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.52/0.99  --sup_immed_triv                        [TrivRules]
% 2.52/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/0.99  --sup_immed_bw_main                     []
% 2.52/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.52/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.52/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.52/0.99  --sup_input_bw                          [BwDemod;BwSubsumption]
% 2.52/0.99  
% 2.52/0.99  ------ Combination Options
% 2.52/0.99  
% 2.52/0.99  --comb_res_mult                         1
% 2.52/0.99  --comb_sup_mult                         1
% 2.52/0.99  --comb_inst_mult                        1000000
% 2.52/0.99  
% 2.52/0.99  ------ Debug Options
% 2.52/0.99  
% 2.52/0.99  --dbg_backtrace                         false
% 2.52/0.99  --dbg_dump_prop_clauses                 false
% 2.52/0.99  --dbg_dump_prop_clauses_file            -
% 2.52/0.99  --dbg_out_stat                          false
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  ------ Proving...
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  % SZS status Theorem for theBenchmark.p
% 2.52/0.99  
% 2.52/0.99   Resolution empty clause
% 2.52/0.99  
% 2.52/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.52/0.99  
% 2.52/0.99  fof(f5,axiom,(
% 2.52/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f20,plain,(
% 2.52/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.52/0.99    inference(cnf_transformation,[],[f5])).
% 2.52/0.99  
% 2.52/0.99  fof(f9,axiom,(
% 2.52/0.99    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)),
% 2.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f24,plain,(
% 2.52/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f9])).
% 2.52/0.99  
% 2.52/0.99  fof(f1,axiom,(
% 2.52/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f16,plain,(
% 2.52/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f1])).
% 2.52/0.99  
% 2.52/0.99  fof(f10,conjecture,(
% 2.52/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f11,negated_conjecture,(
% 2.52/0.99    ~! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.52/0.99    inference(negated_conjecture,[],[f10])).
% 2.52/0.99  
% 2.52/0.99  fof(f13,plain,(
% 2.52/0.99    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.52/0.99    inference(ennf_transformation,[],[f11])).
% 2.52/0.99  
% 2.52/0.99  fof(f14,plain,(
% 2.52/0.99    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.52/0.99    introduced(choice_axiom,[])).
% 2.52/0.99  
% 2.52/0.99  fof(f15,plain,(
% 2.52/0.99    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.52/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 2.52/0.99  
% 2.52/0.99  fof(f25,plain,(
% 2.52/0.99    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.52/0.99    inference(cnf_transformation,[],[f15])).
% 2.52/0.99  
% 2.52/0.99  fof(f2,axiom,(
% 2.52/0.99    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)),
% 2.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f17,plain,(
% 2.52/0.99    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k5_xboole_0(X0,X1)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f2])).
% 2.52/0.99  
% 2.52/0.99  fof(f8,axiom,(
% 2.52/0.99    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f23,plain,(
% 2.52/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f8])).
% 2.52/0.99  
% 2.52/0.99  fof(f28,plain,(
% 2.52/0.99    k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.52/0.99    inference(definition_unfolding,[],[f25,f17,f23])).
% 2.52/0.99  
% 2.52/0.99  fof(f7,axiom,(
% 2.52/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f22,plain,(
% 2.52/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.52/0.99    inference(cnf_transformation,[],[f7])).
% 2.52/0.99  
% 2.52/0.99  fof(f27,plain,(
% 2.52/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.52/0.99    inference(definition_unfolding,[],[f22,f23])).
% 2.52/0.99  
% 2.52/0.99  fof(f3,axiom,(
% 2.52/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f12,plain,(
% 2.52/0.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.52/0.99    inference(ennf_transformation,[],[f3])).
% 2.52/0.99  
% 2.52/0.99  fof(f18,plain,(
% 2.52/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f12])).
% 2.52/0.99  
% 2.52/0.99  fof(f4,axiom,(
% 2.52/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.52/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.52/0.99  
% 2.52/0.99  fof(f19,plain,(
% 2.52/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.52/0.99    inference(cnf_transformation,[],[f4])).
% 2.52/0.99  
% 2.52/0.99  fof(f26,plain,(
% 2.52/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 2.52/0.99    inference(definition_unfolding,[],[f19,f23])).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3,plain,
% 2.52/0.99      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 2.52/0.99      inference(cnf_transformation,[],[f20]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_6,plain,
% 2.52/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 2.52/0.99      inference(cnf_transformation,[],[f24]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_0,plain,
% 2.52/0.99      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 2.52/0.99      inference(cnf_transformation,[],[f16]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_60,plain,
% 2.52/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_97,plain,
% 2.52/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X2,X0))) = k2_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_3,c_60]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_7,negated_conjecture,
% 2.52/0.99      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
% 2.52/0.99      inference(cnf_transformation,[],[f28]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_52,negated_conjecture,
% 2.52/0.99      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) != k2_xboole_0(sK0,sK1) ),
% 2.52/0.99      inference(theory_normalisation,[status(thm)],[c_7,c_6,c_0]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3783,plain,
% 2.52/0.99      ( k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)) != k2_xboole_0(sK0,sK1) ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_97,c_52]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_5,plain,
% 2.52/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 2.52/0.99      inference(cnf_transformation,[],[f27]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1,plain,
% 2.52/0.99      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 2.52/0.99      inference(cnf_transformation,[],[f18]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_2,plain,
% 2.52/0.99      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 2.52/0.99      inference(cnf_transformation,[],[f26]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_40,plain,
% 2.52/0.99      ( X0 != X1
% 2.52/0.99      | k4_xboole_0(X0,k4_xboole_0(X0,X2)) != X3
% 2.52/0.99      | k2_xboole_0(X3,X1) = X1 ),
% 2.52/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_41,plain,
% 2.52/0.99      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = X0 ),
% 2.52/0.99      inference(unflattening,[status(thm)],[c_40]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_51,plain,
% 2.52/0.99      ( k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 2.52/0.99      inference(theory_normalisation,[status(thm)],[c_41,c_6,c_0]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_76,plain,
% 2.52/0.99      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_5,c_51]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_89,plain,
% 2.52/0.99      ( k2_xboole_0(X0,X0) = X0 ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_76,c_3]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_61,plain,
% 2.52/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_122,plain,
% 2.52/0.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_89,c_61]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_287,plain,
% 2.52/0.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),X0) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_3,c_122]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_334,plain,
% 2.52/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),X1) = k2_xboole_0(X0,X1) ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_287,c_122]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_478,plain,
% 2.52/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,k2_xboole_0(X0,X1)) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_334,c_60]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_99,plain,
% 2.52/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_89,c_60]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_180,plain,
% 2.52/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,k4_xboole_0(X0,X1)) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_3,c_99]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_120,plain,
% 2.52/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_3,c_61]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_211,plain,
% 2.52/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X1,X0) ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_180,c_3,c_120]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_746,plain,
% 2.52/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_211,c_0]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_121,plain,
% 2.52/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(X2,X0) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_76,c_61]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1540,plain,
% 2.52/0.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X1)) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_746,c_121]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_110,plain,
% 2.52/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X1))) = k2_xboole_0(X0,X1) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_6,c_89]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_111,plain,
% 2.52/0.99      ( k2_xboole_0(X0,k2_xboole_0(X0,X1)) = k2_xboole_0(X0,X1) ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_110,c_99]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_62,plain,
% 2.52/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k2_xboole_0(X2,X0)) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_262,plain,
% 2.52/0.99      ( k2_xboole_0(X0,k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_111,c_62]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_357,plain,
% 2.52/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_111,c_262]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_372,plain,
% 2.52/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X2,X1)) = k2_xboole_0(X2,k2_xboole_0(X1,X0)) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_262,c_62]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_388,plain,
% 2.52/0.99      ( k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(X0,X1) ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_357,c_262,c_372]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1145,plain,
% 2.52/0.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X0,X1)) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 2.52/0.99      inference(superposition,[status(thm)],[c_388,c_121]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1207,plain,
% 2.52/0.99      ( k2_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X2),k2_xboole_0(X0,X1)) = k2_xboole_0(X1,X0) ),
% 2.52/0.99      inference(light_normalisation,[status(thm)],[c_1145,c_122]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_1547,plain,
% 2.52/0.99      ( k2_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 2.52/0.99      inference(light_normalisation,[status(thm)],[c_1540,c_1207]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3784,plain,
% 2.52/0.99      ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) ),
% 2.52/0.99      inference(demodulation,[status(thm)],[c_3783,c_478,c_1547]) ).
% 2.52/0.99  
% 2.52/0.99  cnf(c_3785,plain,
% 2.52/0.99      ( $false ),
% 2.52/0.99      inference(equality_resolution_simp,[status(thm)],[c_3784]) ).
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.52/0.99  
% 2.52/0.99  ------                               Statistics
% 2.52/0.99  
% 2.52/0.99  ------ General
% 2.52/0.99  
% 2.52/0.99  abstr_ref_over_cycles:                  0
% 2.52/0.99  abstr_ref_under_cycles:                 0
% 2.52/0.99  gc_basic_clause_elim:                   0
% 2.52/0.99  forced_gc_time:                         0
% 2.52/0.99  parsing_time:                           0.007
% 2.52/0.99  unif_index_cands_time:                  0.
% 2.52/0.99  unif_index_add_time:                    0.
% 2.52/0.99  orderings_time:                         0.
% 2.52/0.99  out_proof_time:                         0.007
% 2.52/0.99  total_time:                             0.154
% 2.52/0.99  num_of_symbols:                         36
% 2.52/0.99  num_of_terms:                           4430
% 2.52/0.99  
% 2.52/0.99  ------ Preprocessing
% 2.52/0.99  
% 2.52/0.99  num_of_splits:                          0
% 2.52/0.99  num_of_split_atoms:                     0
% 2.52/0.99  num_of_reused_defs:                     0
% 2.52/0.99  num_eq_ax_congr_red:                    1
% 2.52/0.99  num_of_sem_filtered_clauses:            0
% 2.52/0.99  num_of_subtypes:                        0
% 2.52/0.99  monotx_restored_types:                  0
% 2.52/0.99  sat_num_of_epr_types:                   0
% 2.52/0.99  sat_num_of_non_cyclic_types:            0
% 2.52/0.99  sat_guarded_non_collapsed_types:        0
% 2.52/0.99  num_pure_diseq_elim:                    0
% 2.52/0.99  simp_replaced_by:                       0
% 2.52/0.99  res_preprocessed:                       26
% 2.52/0.99  prep_upred:                             0
% 2.52/0.99  prep_unflattend:                        2
% 2.52/0.99  smt_new_axioms:                         0
% 2.52/0.99  pred_elim_cands:                        0
% 2.52/0.99  pred_elim:                              1
% 2.52/0.99  pred_elim_cl:                           1
% 2.52/0.99  pred_elim_cycles:                       2
% 2.52/0.99  merged_defs:                            0
% 2.52/0.99  merged_defs_ncl:                        0
% 2.52/0.99  bin_hyper_res:                          0
% 2.52/0.99  prep_cycles:                            3
% 2.52/0.99  pred_elim_time:                         0.
% 2.52/0.99  splitting_time:                         0.
% 2.52/0.99  sem_filter_time:                        0.
% 2.52/0.99  monotx_time:                            0.
% 2.52/0.99  subtype_inf_time:                       0.
% 2.52/0.99  
% 2.52/0.99  ------ Problem properties
% 2.52/0.99  
% 2.52/0.99  clauses:                                7
% 2.52/0.99  conjectures:                            1
% 2.52/0.99  epr:                                    0
% 2.52/0.99  horn:                                   7
% 2.52/0.99  ground:                                 1
% 2.52/0.99  unary:                                  7
% 2.52/0.99  binary:                                 0
% 2.52/0.99  lits:                                   7
% 2.52/0.99  lits_eq:                                7
% 2.52/0.99  fd_pure:                                0
% 2.52/0.99  fd_pseudo:                              0
% 2.52/0.99  fd_cond:                                0
% 2.52/0.99  fd_pseudo_cond:                         0
% 2.52/0.99  ac_symbols:                             1
% 2.52/0.99  
% 2.52/0.99  ------ Propositional Solver
% 2.52/0.99  
% 2.52/0.99  prop_solver_calls:                      17
% 2.52/0.99  prop_fast_solver_calls:                 67
% 2.52/0.99  smt_solver_calls:                       0
% 2.52/0.99  smt_fast_solver_calls:                  0
% 2.52/0.99  prop_num_of_clauses:                    96
% 2.52/0.99  prop_preprocess_simplified:             394
% 2.52/0.99  prop_fo_subsumed:                       0
% 2.52/0.99  prop_solver_time:                       0.
% 2.52/0.99  smt_solver_time:                        0.
% 2.52/0.99  smt_fast_solver_time:                   0.
% 2.52/0.99  prop_fast_solver_time:                  0.
% 2.52/0.99  prop_unsat_core_time:                   0.
% 2.52/0.99  
% 2.52/0.99  ------ QBF
% 2.52/0.99  
% 2.52/0.99  qbf_q_res:                              0
% 2.52/0.99  qbf_num_tautologies:                    0
% 2.52/0.99  qbf_prep_cycles:                        0
% 2.52/0.99  
% 2.52/0.99  ------ BMC1
% 2.52/0.99  
% 2.52/0.99  bmc1_current_bound:                     -1
% 2.52/0.99  bmc1_last_solved_bound:                 -1
% 2.52/0.99  bmc1_unsat_core_size:                   -1
% 2.52/0.99  bmc1_unsat_core_parents_size:           -1
% 2.52/0.99  bmc1_merge_next_fun:                    0
% 2.52/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.52/0.99  
% 2.52/0.99  ------ Instantiation
% 2.52/0.99  
% 2.52/0.99  inst_num_of_clauses:                    0
% 2.52/0.99  inst_num_in_passive:                    0
% 2.52/0.99  inst_num_in_active:                     0
% 2.52/0.99  inst_num_in_unprocessed:                0
% 2.52/0.99  inst_num_of_loops:                      0
% 2.52/0.99  inst_num_of_learning_restarts:          0
% 2.52/0.99  inst_num_moves_active_passive:          0
% 2.52/0.99  inst_lit_activity:                      0
% 2.52/0.99  inst_lit_activity_moves:                0
% 2.52/0.99  inst_num_tautologies:                   0
% 2.52/0.99  inst_num_prop_implied:                  0
% 2.52/0.99  inst_num_existing_simplified:           0
% 2.52/0.99  inst_num_eq_res_simplified:             0
% 2.52/0.99  inst_num_child_elim:                    0
% 2.52/0.99  inst_num_of_dismatching_blockings:      0
% 2.52/0.99  inst_num_of_non_proper_insts:           0
% 2.52/0.99  inst_num_of_duplicates:                 0
% 2.52/0.99  inst_inst_num_from_inst_to_res:         0
% 2.52/0.99  inst_dismatching_checking_time:         0.
% 2.52/0.99  
% 2.52/0.99  ------ Resolution
% 2.52/0.99  
% 2.52/0.99  res_num_of_clauses:                     0
% 2.52/0.99  res_num_in_passive:                     0
% 2.52/0.99  res_num_in_active:                      0
% 2.52/0.99  res_num_of_loops:                       29
% 2.52/0.99  res_forward_subset_subsumed:            0
% 2.52/0.99  res_backward_subset_subsumed:           0
% 2.52/0.99  res_forward_subsumed:                   0
% 2.52/0.99  res_backward_subsumed:                  0
% 2.52/0.99  res_forward_subsumption_resolution:     0
% 2.52/0.99  res_backward_subsumption_resolution:    0
% 2.52/0.99  res_clause_to_clause_subsumption:       13167
% 2.52/0.99  res_orphan_elimination:                 0
% 2.52/0.99  res_tautology_del:                      0
% 2.52/0.99  res_num_eq_res_simplified:              0
% 2.52/0.99  res_num_sel_changes:                    0
% 2.52/0.99  res_moves_from_active_to_pass:          0
% 2.52/0.99  
% 2.52/0.99  ------ Superposition
% 2.52/0.99  
% 2.52/0.99  sup_time_total:                         0.
% 2.52/0.99  sup_time_generating:                    0.
% 2.52/0.99  sup_time_sim_full:                      0.
% 2.52/0.99  sup_time_sim_immed:                     0.
% 2.52/0.99  
% 2.52/0.99  sup_num_of_clauses:                     452
% 2.52/0.99  sup_num_in_active:                      47
% 2.52/0.99  sup_num_in_passive:                     405
% 2.52/0.99  sup_num_of_loops:                       52
% 2.52/0.99  sup_fw_superposition:                   1414
% 2.52/0.99  sup_bw_superposition:                   1160
% 2.52/0.99  sup_immediate_simplified:               1127
% 2.52/0.99  sup_given_eliminated:                   0
% 2.52/0.99  comparisons_done:                       0
% 2.52/0.99  comparisons_avoided:                    0
% 2.52/0.99  
% 2.52/0.99  ------ Simplifications
% 2.52/0.99  
% 2.52/0.99  
% 2.52/0.99  sim_fw_subset_subsumed:                 0
% 2.52/0.99  sim_bw_subset_subsumed:                 0
% 2.52/0.99  sim_fw_subsumed:                        189
% 2.52/0.99  sim_bw_subsumed:                        8
% 2.52/0.99  sim_fw_subsumption_res:                 0
% 2.52/0.99  sim_bw_subsumption_res:                 0
% 2.52/0.99  sim_tautology_del:                      0
% 2.52/0.99  sim_eq_tautology_del:                   156
% 2.52/0.99  sim_eq_res_simp:                        0
% 2.52/0.99  sim_fw_demodulated:                     655
% 2.52/0.99  sim_bw_demodulated:                     9
% 2.52/0.99  sim_light_normalised:                   367
% 2.52/0.99  sim_joinable_taut:                      27
% 2.52/0.99  sim_joinable_simp:                      0
% 2.52/0.99  sim_ac_normalised:                      0
% 2.52/0.99  sim_smt_subsumption:                    0
% 2.52/0.99  
%------------------------------------------------------------------------------
