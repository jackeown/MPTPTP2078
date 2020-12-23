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
% DateTime   : Thu Dec  3 11:26:52 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   54 (  84 expanded)
%              Number of clauses        :   20 (  24 expanded)
%              Number of leaves         :   13 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :   61 (  91 expanded)
%              Number of equality atoms :   52 (  82 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :   10 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f13])).

fof(f16,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f14])).

fof(f17,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f31,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f27,f21])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f28,f32])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f29,f32,f33])).

fof(f37,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0)))) ),
    inference(definition_unfolding,[],[f31,f33,f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f24,f32])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_89,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_7,c_6])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_2,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_69,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_2])).

cnf(c_96,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_89,c_69])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_8,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0)))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_55,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0)))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) ),
    inference(theory_normalisation,[status(thm)],[c_8,c_6,c_2])).

cnf(c_66,plain,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k1_tarski(sK0)))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(demodulation,[status(thm)],[c_1,c_55])).

cnf(c_67,plain,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(superposition,[status(thm)],[c_1,c_66])).

cnf(c_130,plain,
    ( k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(demodulation,[status(thm)],[c_96,c_67])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_5,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_43,plain,
    ( X0 != X1
    | k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))) != X3
    | k3_xboole_0(X1,X3) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_5])).

cnf(c_44,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
    inference(unflattening,[status(thm)],[c_43])).

cnf(c_80,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_44])).

cnf(c_131,plain,
    ( k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(demodulation,[status(thm)],[c_130,c_80])).

cnf(c_155,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_131])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:26:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.79/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/0.98  
% 2.79/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.79/0.98  
% 2.79/0.98  ------  iProver source info
% 2.79/0.98  
% 2.79/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.79/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.79/0.98  git: non_committed_changes: false
% 2.79/0.98  git: last_make_outside_of_git: false
% 2.79/0.98  
% 2.79/0.98  ------ 
% 2.79/0.98  
% 2.79/0.98  ------ Input Options
% 2.79/0.98  
% 2.79/0.98  --out_options                           all
% 2.79/0.98  --tptp_safe_out                         true
% 2.79/0.98  --problem_path                          ""
% 2.79/0.98  --include_path                          ""
% 2.79/0.98  --clausifier                            res/vclausify_rel
% 2.79/0.98  --clausifier_options                    --mode clausify
% 2.79/0.98  --stdin                                 false
% 2.79/0.98  --stats_out                             all
% 2.79/0.98  
% 2.79/0.98  ------ General Options
% 2.79/0.98  
% 2.79/0.98  --fof                                   false
% 2.79/0.98  --time_out_real                         305.
% 2.79/0.98  --time_out_virtual                      -1.
% 2.79/0.98  --symbol_type_check                     false
% 2.79/0.98  --clausify_out                          false
% 2.79/0.98  --sig_cnt_out                           false
% 2.79/0.98  --trig_cnt_out                          false
% 2.79/0.98  --trig_cnt_out_tolerance                1.
% 2.79/0.98  --trig_cnt_out_sk_spl                   false
% 2.79/0.98  --abstr_cl_out                          false
% 2.79/0.98  
% 2.79/0.98  ------ Global Options
% 2.79/0.98  
% 2.79/0.98  --schedule                              default
% 2.79/0.98  --add_important_lit                     false
% 2.79/0.98  --prop_solver_per_cl                    1000
% 2.79/0.98  --min_unsat_core                        false
% 2.79/0.98  --soft_assumptions                      false
% 2.79/0.98  --soft_lemma_size                       3
% 2.79/0.98  --prop_impl_unit_size                   0
% 2.79/0.98  --prop_impl_unit                        []
% 2.79/0.98  --share_sel_clauses                     true
% 2.79/0.98  --reset_solvers                         false
% 2.79/0.98  --bc_imp_inh                            [conj_cone]
% 2.79/0.98  --conj_cone_tolerance                   3.
% 2.79/0.98  --extra_neg_conj                        none
% 2.79/0.98  --large_theory_mode                     true
% 2.79/0.98  --prolific_symb_bound                   200
% 2.79/0.98  --lt_threshold                          2000
% 2.79/0.98  --clause_weak_htbl                      true
% 2.79/0.98  --gc_record_bc_elim                     false
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing Options
% 2.79/0.98  
% 2.79/0.98  --preprocessing_flag                    true
% 2.79/0.98  --time_out_prep_mult                    0.1
% 2.79/0.98  --splitting_mode                        input
% 2.79/0.98  --splitting_grd                         true
% 2.79/0.98  --splitting_cvd                         false
% 2.79/0.98  --splitting_cvd_svl                     false
% 2.79/0.98  --splitting_nvd                         32
% 2.79/0.98  --sub_typing                            true
% 2.79/0.98  --prep_gs_sim                           true
% 2.79/0.98  --prep_unflatten                        true
% 2.79/0.98  --prep_res_sim                          true
% 2.79/0.98  --prep_upred                            true
% 2.79/0.98  --prep_sem_filter                       exhaustive
% 2.79/0.98  --prep_sem_filter_out                   false
% 2.79/0.98  --pred_elim                             true
% 2.79/0.98  --res_sim_input                         true
% 2.79/0.98  --eq_ax_congr_red                       true
% 2.79/0.98  --pure_diseq_elim                       true
% 2.79/0.98  --brand_transform                       false
% 2.79/0.98  --non_eq_to_eq                          false
% 2.79/0.98  --prep_def_merge                        true
% 2.79/0.98  --prep_def_merge_prop_impl              false
% 2.79/0.98  --prep_def_merge_mbd                    true
% 2.79/0.98  --prep_def_merge_tr_red                 false
% 2.79/0.98  --prep_def_merge_tr_cl                  false
% 2.79/0.98  --smt_preprocessing                     true
% 2.79/0.98  --smt_ac_axioms                         fast
% 2.79/0.98  --preprocessed_out                      false
% 2.79/0.98  --preprocessed_stats                    false
% 2.79/0.98  
% 2.79/0.98  ------ Abstraction refinement Options
% 2.79/0.98  
% 2.79/0.98  --abstr_ref                             []
% 2.79/0.98  --abstr_ref_prep                        false
% 2.79/0.98  --abstr_ref_until_sat                   false
% 2.79/0.98  --abstr_ref_sig_restrict                funpre
% 2.79/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/0.98  --abstr_ref_under                       []
% 2.79/0.98  
% 2.79/0.98  ------ SAT Options
% 2.79/0.98  
% 2.79/0.98  --sat_mode                              false
% 2.79/0.98  --sat_fm_restart_options                ""
% 2.79/0.98  --sat_gr_def                            false
% 2.79/0.98  --sat_epr_types                         true
% 2.79/0.98  --sat_non_cyclic_types                  false
% 2.79/0.98  --sat_finite_models                     false
% 2.79/0.98  --sat_fm_lemmas                         false
% 2.79/0.98  --sat_fm_prep                           false
% 2.79/0.98  --sat_fm_uc_incr                        true
% 2.79/0.98  --sat_out_model                         small
% 2.79/0.98  --sat_out_clauses                       false
% 2.79/0.98  
% 2.79/0.98  ------ QBF Options
% 2.79/0.98  
% 2.79/0.98  --qbf_mode                              false
% 2.79/0.98  --qbf_elim_univ                         false
% 2.79/0.98  --qbf_dom_inst                          none
% 2.79/0.98  --qbf_dom_pre_inst                      false
% 2.79/0.98  --qbf_sk_in                             false
% 2.79/0.98  --qbf_pred_elim                         true
% 2.79/0.98  --qbf_split                             512
% 2.79/0.98  
% 2.79/0.98  ------ BMC1 Options
% 2.79/0.98  
% 2.79/0.98  --bmc1_incremental                      false
% 2.79/0.98  --bmc1_axioms                           reachable_all
% 2.79/0.98  --bmc1_min_bound                        0
% 2.79/0.98  --bmc1_max_bound                        -1
% 2.79/0.98  --bmc1_max_bound_default                -1
% 2.79/0.98  --bmc1_symbol_reachability              true
% 2.79/0.98  --bmc1_property_lemmas                  false
% 2.79/0.98  --bmc1_k_induction                      false
% 2.79/0.98  --bmc1_non_equiv_states                 false
% 2.79/0.98  --bmc1_deadlock                         false
% 2.79/0.98  --bmc1_ucm                              false
% 2.79/0.98  --bmc1_add_unsat_core                   none
% 2.79/0.98  --bmc1_unsat_core_children              false
% 2.79/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/0.98  --bmc1_out_stat                         full
% 2.79/0.98  --bmc1_ground_init                      false
% 2.79/0.98  --bmc1_pre_inst_next_state              false
% 2.79/0.98  --bmc1_pre_inst_state                   false
% 2.79/0.98  --bmc1_pre_inst_reach_state             false
% 2.79/0.98  --bmc1_out_unsat_core                   false
% 2.79/0.98  --bmc1_aig_witness_out                  false
% 2.79/0.98  --bmc1_verbose                          false
% 2.79/0.98  --bmc1_dump_clauses_tptp                false
% 2.79/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.79/0.98  --bmc1_dump_file                        -
% 2.79/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.79/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.79/0.98  --bmc1_ucm_extend_mode                  1
% 2.79/0.98  --bmc1_ucm_init_mode                    2
% 2.79/0.98  --bmc1_ucm_cone_mode                    none
% 2.79/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.79/0.98  --bmc1_ucm_relax_model                  4
% 2.79/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.79/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/0.98  --bmc1_ucm_layered_model                none
% 2.79/0.98  --bmc1_ucm_max_lemma_size               10
% 2.79/0.98  
% 2.79/0.98  ------ AIG Options
% 2.79/0.98  
% 2.79/0.98  --aig_mode                              false
% 2.79/0.98  
% 2.79/0.98  ------ Instantiation Options
% 2.79/0.98  
% 2.79/0.98  --instantiation_flag                    true
% 2.79/0.98  --inst_sos_flag                         false
% 2.79/0.98  --inst_sos_phase                        true
% 2.79/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/0.98  --inst_lit_sel_side                     num_symb
% 2.79/0.98  --inst_solver_per_active                1400
% 2.79/0.98  --inst_solver_calls_frac                1.
% 2.79/0.98  --inst_passive_queue_type               priority_queues
% 2.79/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/0.98  --inst_passive_queues_freq              [25;2]
% 2.79/0.98  --inst_dismatching                      true
% 2.79/0.98  --inst_eager_unprocessed_to_passive     true
% 2.79/0.98  --inst_prop_sim_given                   true
% 2.79/0.98  --inst_prop_sim_new                     false
% 2.79/0.98  --inst_subs_new                         false
% 2.79/0.98  --inst_eq_res_simp                      false
% 2.79/0.98  --inst_subs_given                       false
% 2.79/0.98  --inst_orphan_elimination               true
% 2.79/0.98  --inst_learning_loop_flag               true
% 2.79/0.98  --inst_learning_start                   3000
% 2.79/0.98  --inst_learning_factor                  2
% 2.79/0.98  --inst_start_prop_sim_after_learn       3
% 2.79/0.98  --inst_sel_renew                        solver
% 2.79/0.98  --inst_lit_activity_flag                true
% 2.79/0.98  --inst_restr_to_given                   false
% 2.79/0.98  --inst_activity_threshold               500
% 2.79/0.98  --inst_out_proof                        true
% 2.79/0.98  
% 2.79/0.98  ------ Resolution Options
% 2.79/0.98  
% 2.79/0.98  --resolution_flag                       true
% 2.79/0.98  --res_lit_sel                           adaptive
% 2.79/0.98  --res_lit_sel_side                      none
% 2.79/0.98  --res_ordering                          kbo
% 2.79/0.98  --res_to_prop_solver                    active
% 2.79/0.98  --res_prop_simpl_new                    false
% 2.79/0.98  --res_prop_simpl_given                  true
% 2.79/0.98  --res_passive_queue_type                priority_queues
% 2.79/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/0.98  --res_passive_queues_freq               [15;5]
% 2.79/0.98  --res_forward_subs                      full
% 2.79/0.98  --res_backward_subs                     full
% 2.79/0.98  --res_forward_subs_resolution           true
% 2.79/0.98  --res_backward_subs_resolution          true
% 2.79/0.98  --res_orphan_elimination                true
% 2.79/0.98  --res_time_limit                        2.
% 2.79/0.98  --res_out_proof                         true
% 2.79/0.98  
% 2.79/0.98  ------ Superposition Options
% 2.79/0.98  
% 2.79/0.98  --superposition_flag                    true
% 2.79/0.98  --sup_passive_queue_type                priority_queues
% 2.79/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.79/0.98  --demod_completeness_check              fast
% 2.79/0.98  --demod_use_ground                      true
% 2.79/0.98  --sup_to_prop_solver                    passive
% 2.79/0.98  --sup_prop_simpl_new                    true
% 2.79/0.98  --sup_prop_simpl_given                  true
% 2.79/0.98  --sup_fun_splitting                     false
% 2.79/0.98  --sup_smt_interval                      50000
% 2.79/0.98  
% 2.79/0.98  ------ Superposition Simplification Setup
% 2.79/0.98  
% 2.79/0.98  --sup_indices_passive                   []
% 2.79/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.79/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.98  --sup_full_bw                           [BwDemod]
% 2.79/0.98  --sup_immed_triv                        [TrivRules]
% 2.79/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.98  --sup_immed_bw_main                     []
% 2.79/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.79/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.79/0.98  
% 2.79/0.98  ------ Combination Options
% 2.79/0.98  
% 2.79/0.98  --comb_res_mult                         3
% 2.79/0.98  --comb_sup_mult                         2
% 2.79/0.98  --comb_inst_mult                        10
% 2.79/0.98  
% 2.79/0.98  ------ Debug Options
% 2.79/0.98  
% 2.79/0.98  --dbg_backtrace                         false
% 2.79/0.98  --dbg_dump_prop_clauses                 false
% 2.79/0.98  --dbg_dump_prop_clauses_file            -
% 2.79/0.98  --dbg_out_stat                          false
% 2.79/0.98  ------ Parsing...
% 2.79/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.79/0.98  ------ Proving...
% 2.79/0.98  ------ Problem Properties 
% 2.79/0.98  
% 2.79/0.98  
% 2.79/0.98  clauses                                 8
% 2.79/0.98  conjectures                             1
% 2.79/0.98  EPR                                     0
% 2.79/0.98  Horn                                    8
% 2.79/0.98  unary                                   8
% 2.79/0.98  binary                                  0
% 2.79/0.98  lits                                    8
% 2.79/0.98  lits eq                                 8
% 2.79/0.98  fd_pure                                 0
% 2.79/0.98  fd_pseudo                               0
% 2.79/0.98  fd_cond                                 0
% 2.79/0.98  fd_pseudo_cond                          0
% 2.79/0.98  AC symbols                              1
% 2.79/0.98  
% 2.79/0.98  ------ Schedule UEQ
% 2.79/0.98  
% 2.79/0.98  ------ pure equality problem: resolution off 
% 2.79/0.98  
% 2.79/0.98  ------ Option_UEQ Time Limit: Unbounded
% 2.79/0.98  
% 2.79/0.98  
% 2.79/0.98  ------ 
% 2.79/0.98  Current options:
% 2.79/0.98  ------ 
% 2.79/0.98  
% 2.79/0.98  ------ Input Options
% 2.79/0.98  
% 2.79/0.98  --out_options                           all
% 2.79/0.98  --tptp_safe_out                         true
% 2.79/0.98  --problem_path                          ""
% 2.79/0.98  --include_path                          ""
% 2.79/0.98  --clausifier                            res/vclausify_rel
% 2.79/0.98  --clausifier_options                    --mode clausify
% 2.79/0.98  --stdin                                 false
% 2.79/0.98  --stats_out                             all
% 2.79/0.98  
% 2.79/0.98  ------ General Options
% 2.79/0.98  
% 2.79/0.98  --fof                                   false
% 2.79/0.98  --time_out_real                         305.
% 2.79/0.98  --time_out_virtual                      -1.
% 2.79/0.98  --symbol_type_check                     false
% 2.79/0.98  --clausify_out                          false
% 2.79/0.98  --sig_cnt_out                           false
% 2.79/0.98  --trig_cnt_out                          false
% 2.79/0.98  --trig_cnt_out_tolerance                1.
% 2.79/0.98  --trig_cnt_out_sk_spl                   false
% 2.79/0.98  --abstr_cl_out                          false
% 2.79/0.98  
% 2.79/0.98  ------ Global Options
% 2.79/0.98  
% 2.79/0.98  --schedule                              default
% 2.79/0.98  --add_important_lit                     false
% 2.79/0.98  --prop_solver_per_cl                    1000
% 2.79/0.98  --min_unsat_core                        false
% 2.79/0.98  --soft_assumptions                      false
% 2.79/0.98  --soft_lemma_size                       3
% 2.79/0.98  --prop_impl_unit_size                   0
% 2.79/0.98  --prop_impl_unit                        []
% 2.79/0.98  --share_sel_clauses                     true
% 2.79/0.98  --reset_solvers                         false
% 2.79/0.98  --bc_imp_inh                            [conj_cone]
% 2.79/0.98  --conj_cone_tolerance                   3.
% 2.79/0.98  --extra_neg_conj                        none
% 2.79/0.98  --large_theory_mode                     true
% 2.79/0.98  --prolific_symb_bound                   200
% 2.79/0.98  --lt_threshold                          2000
% 2.79/0.98  --clause_weak_htbl                      true
% 2.79/0.98  --gc_record_bc_elim                     false
% 2.79/0.98  
% 2.79/0.98  ------ Preprocessing Options
% 2.79/0.98  
% 2.79/0.98  --preprocessing_flag                    true
% 2.79/0.98  --time_out_prep_mult                    0.1
% 2.79/0.98  --splitting_mode                        input
% 2.79/0.98  --splitting_grd                         true
% 2.79/0.98  --splitting_cvd                         false
% 2.79/0.98  --splitting_cvd_svl                     false
% 2.79/0.98  --splitting_nvd                         32
% 2.79/0.98  --sub_typing                            true
% 2.79/0.98  --prep_gs_sim                           true
% 2.79/0.98  --prep_unflatten                        true
% 2.79/0.98  --prep_res_sim                          true
% 2.79/0.98  --prep_upred                            true
% 2.79/0.98  --prep_sem_filter                       exhaustive
% 2.79/0.98  --prep_sem_filter_out                   false
% 2.79/0.98  --pred_elim                             true
% 2.79/0.98  --res_sim_input                         true
% 2.79/0.98  --eq_ax_congr_red                       true
% 2.79/0.98  --pure_diseq_elim                       true
% 2.79/0.98  --brand_transform                       false
% 2.79/0.98  --non_eq_to_eq                          false
% 2.79/0.98  --prep_def_merge                        true
% 2.79/0.98  --prep_def_merge_prop_impl              false
% 2.79/0.98  --prep_def_merge_mbd                    true
% 2.79/0.98  --prep_def_merge_tr_red                 false
% 2.79/0.98  --prep_def_merge_tr_cl                  false
% 2.79/0.98  --smt_preprocessing                     true
% 2.79/0.98  --smt_ac_axioms                         fast
% 2.79/0.98  --preprocessed_out                      false
% 2.79/0.98  --preprocessed_stats                    false
% 2.79/0.98  
% 2.79/0.98  ------ Abstraction refinement Options
% 2.79/0.98  
% 2.79/0.98  --abstr_ref                             []
% 2.79/0.98  --abstr_ref_prep                        false
% 2.79/0.98  --abstr_ref_until_sat                   false
% 2.79/0.98  --abstr_ref_sig_restrict                funpre
% 2.79/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.79/0.98  --abstr_ref_under                       []
% 2.79/0.98  
% 2.79/0.98  ------ SAT Options
% 2.79/0.98  
% 2.79/0.98  --sat_mode                              false
% 2.79/0.98  --sat_fm_restart_options                ""
% 2.79/0.98  --sat_gr_def                            false
% 2.79/0.98  --sat_epr_types                         true
% 2.79/0.98  --sat_non_cyclic_types                  false
% 2.79/0.98  --sat_finite_models                     false
% 2.79/0.98  --sat_fm_lemmas                         false
% 2.79/0.98  --sat_fm_prep                           false
% 2.79/0.98  --sat_fm_uc_incr                        true
% 2.79/0.98  --sat_out_model                         small
% 2.79/0.98  --sat_out_clauses                       false
% 2.79/0.98  
% 2.79/0.98  ------ QBF Options
% 2.79/0.98  
% 2.79/0.98  --qbf_mode                              false
% 2.79/0.98  --qbf_elim_univ                         false
% 2.79/0.98  --qbf_dom_inst                          none
% 2.79/0.98  --qbf_dom_pre_inst                      false
% 2.79/0.98  --qbf_sk_in                             false
% 2.79/0.98  --qbf_pred_elim                         true
% 2.79/0.98  --qbf_split                             512
% 2.79/0.98  
% 2.79/0.98  ------ BMC1 Options
% 2.79/0.98  
% 2.79/0.98  --bmc1_incremental                      false
% 2.79/0.98  --bmc1_axioms                           reachable_all
% 2.79/0.98  --bmc1_min_bound                        0
% 2.79/0.98  --bmc1_max_bound                        -1
% 2.79/0.98  --bmc1_max_bound_default                -1
% 2.79/0.98  --bmc1_symbol_reachability              true
% 2.79/0.98  --bmc1_property_lemmas                  false
% 2.79/0.99  --bmc1_k_induction                      false
% 2.79/0.99  --bmc1_non_equiv_states                 false
% 2.79/0.99  --bmc1_deadlock                         false
% 2.79/0.99  --bmc1_ucm                              false
% 2.79/0.99  --bmc1_add_unsat_core                   none
% 2.79/0.99  --bmc1_unsat_core_children              false
% 2.79/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.79/0.99  --bmc1_out_stat                         full
% 2.79/0.99  --bmc1_ground_init                      false
% 2.79/0.99  --bmc1_pre_inst_next_state              false
% 2.79/0.99  --bmc1_pre_inst_state                   false
% 2.79/0.99  --bmc1_pre_inst_reach_state             false
% 2.79/0.99  --bmc1_out_unsat_core                   false
% 2.79/0.99  --bmc1_aig_witness_out                  false
% 2.79/0.99  --bmc1_verbose                          false
% 2.79/0.99  --bmc1_dump_clauses_tptp                false
% 2.79/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.79/0.99  --bmc1_dump_file                        -
% 2.79/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.79/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.79/0.99  --bmc1_ucm_extend_mode                  1
% 2.79/0.99  --bmc1_ucm_init_mode                    2
% 2.79/0.99  --bmc1_ucm_cone_mode                    none
% 2.79/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.79/0.99  --bmc1_ucm_relax_model                  4
% 2.79/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.79/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.79/0.99  --bmc1_ucm_layered_model                none
% 2.79/0.99  --bmc1_ucm_max_lemma_size               10
% 2.79/0.99  
% 2.79/0.99  ------ AIG Options
% 2.79/0.99  
% 2.79/0.99  --aig_mode                              false
% 2.79/0.99  
% 2.79/0.99  ------ Instantiation Options
% 2.79/0.99  
% 2.79/0.99  --instantiation_flag                    false
% 2.79/0.99  --inst_sos_flag                         false
% 2.79/0.99  --inst_sos_phase                        true
% 2.79/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.79/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.79/0.99  --inst_lit_sel_side                     num_symb
% 2.79/0.99  --inst_solver_per_active                1400
% 2.79/0.99  --inst_solver_calls_frac                1.
% 2.79/0.99  --inst_passive_queue_type               priority_queues
% 2.79/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.79/0.99  --inst_passive_queues_freq              [25;2]
% 2.79/0.99  --inst_dismatching                      true
% 2.79/0.99  --inst_eager_unprocessed_to_passive     true
% 2.79/0.99  --inst_prop_sim_given                   true
% 2.79/0.99  --inst_prop_sim_new                     false
% 2.79/0.99  --inst_subs_new                         false
% 2.79/0.99  --inst_eq_res_simp                      false
% 2.79/0.99  --inst_subs_given                       false
% 2.79/0.99  --inst_orphan_elimination               true
% 2.79/0.99  --inst_learning_loop_flag               true
% 2.79/0.99  --inst_learning_start                   3000
% 2.79/0.99  --inst_learning_factor                  2
% 2.79/0.99  --inst_start_prop_sim_after_learn       3
% 2.79/0.99  --inst_sel_renew                        solver
% 2.79/0.99  --inst_lit_activity_flag                true
% 2.79/0.99  --inst_restr_to_given                   false
% 2.79/0.99  --inst_activity_threshold               500
% 2.79/0.99  --inst_out_proof                        true
% 2.79/0.99  
% 2.79/0.99  ------ Resolution Options
% 2.79/0.99  
% 2.79/0.99  --resolution_flag                       false
% 2.79/0.99  --res_lit_sel                           adaptive
% 2.79/0.99  --res_lit_sel_side                      none
% 2.79/0.99  --res_ordering                          kbo
% 2.79/0.99  --res_to_prop_solver                    active
% 2.79/0.99  --res_prop_simpl_new                    false
% 2.79/0.99  --res_prop_simpl_given                  true
% 2.79/0.99  --res_passive_queue_type                priority_queues
% 2.79/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.79/0.99  --res_passive_queues_freq               [15;5]
% 2.79/0.99  --res_forward_subs                      full
% 2.79/0.99  --res_backward_subs                     full
% 2.79/0.99  --res_forward_subs_resolution           true
% 2.79/0.99  --res_backward_subs_resolution          true
% 2.79/0.99  --res_orphan_elimination                true
% 2.79/0.99  --res_time_limit                        2.
% 2.79/0.99  --res_out_proof                         true
% 2.79/0.99  
% 2.79/0.99  ------ Superposition Options
% 2.79/0.99  
% 2.79/0.99  --superposition_flag                    true
% 2.79/0.99  --sup_passive_queue_type                priority_queues
% 2.79/0.99  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.79/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.79/0.99  --demod_completeness_check              fast
% 2.79/0.99  --demod_use_ground                      true
% 2.79/0.99  --sup_to_prop_solver                    active
% 2.79/0.99  --sup_prop_simpl_new                    false
% 2.79/0.99  --sup_prop_simpl_given                  false
% 2.79/0.99  --sup_fun_splitting                     true
% 2.79/0.99  --sup_smt_interval                      10000
% 2.79/0.99  
% 2.79/0.99  ------ Superposition Simplification Setup
% 2.79/0.99  
% 2.79/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.79/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.79/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.79/0.99  --sup_full_triv                         [TrivRules]
% 2.79/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.79/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.79/0.99  --sup_immed_triv                        [TrivRules]
% 2.79/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/0.99  --sup_immed_bw_main                     []
% 2.79/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.79/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.79/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.79/0.99  --sup_input_bw                          [BwDemod;BwSubsumption]
% 2.79/0.99  
% 2.79/0.99  ------ Combination Options
% 2.79/0.99  
% 2.79/0.99  --comb_res_mult                         1
% 2.79/0.99  --comb_sup_mult                         1
% 2.79/0.99  --comb_inst_mult                        1000000
% 2.79/0.99  
% 2.79/0.99  ------ Debug Options
% 2.79/0.99  
% 2.79/0.99  --dbg_backtrace                         false
% 2.79/0.99  --dbg_dump_prop_clauses                 false
% 2.79/0.99  --dbg_dump_prop_clauses_file            -
% 2.79/0.99  --dbg_out_stat                          false
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  ------ Proving...
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  % SZS status Theorem for theBenchmark.p
% 2.79/0.99  
% 2.79/0.99   Resolution empty clause
% 2.79/0.99  
% 2.79/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.79/0.99  
% 2.79/0.99  fof(f8,axiom,(
% 2.79/0.99    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f26,plain,(
% 2.79/0.99    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 2.79/0.99    inference(cnf_transformation,[],[f8])).
% 2.79/0.99  
% 2.79/0.99  fof(f7,axiom,(
% 2.79/0.99    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f25,plain,(
% 2.79/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f7])).
% 2.79/0.99  
% 2.79/0.99  fof(f5,axiom,(
% 2.79/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f23,plain,(
% 2.79/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.79/0.99    inference(cnf_transformation,[],[f5])).
% 2.79/0.99  
% 2.79/0.99  fof(f2,axiom,(
% 2.79/0.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f20,plain,(
% 2.79/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f2])).
% 2.79/0.99  
% 2.79/0.99  fof(f1,axiom,(
% 2.79/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f19,plain,(
% 2.79/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f1])).
% 2.79/0.99  
% 2.79/0.99  fof(f13,conjecture,(
% 2.79/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f14,negated_conjecture,(
% 2.79/0.99    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.79/0.99    inference(negated_conjecture,[],[f13])).
% 2.79/0.99  
% 2.79/0.99  fof(f16,plain,(
% 2.79/0.99    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 2.79/0.99    inference(ennf_transformation,[],[f14])).
% 2.79/0.99  
% 2.79/0.99  fof(f17,plain,(
% 2.79/0.99    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 2.79/0.99    introduced(choice_axiom,[])).
% 2.79/0.99  
% 2.79/0.99  fof(f18,plain,(
% 2.79/0.99    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 2.79/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 2.79/0.99  
% 2.79/0.99  fof(f31,plain,(
% 2.79/0.99    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 2.79/0.99    inference(cnf_transformation,[],[f18])).
% 2.79/0.99  
% 2.79/0.99  fof(f11,axiom,(
% 2.79/0.99    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f29,plain,(
% 2.79/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f11])).
% 2.79/0.99  
% 2.79/0.99  fof(f10,axiom,(
% 2.79/0.99    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f28,plain,(
% 2.79/0.99    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f10])).
% 2.79/0.99  
% 2.79/0.99  fof(f9,axiom,(
% 2.79/0.99    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f27,plain,(
% 2.79/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f9])).
% 2.79/0.99  
% 2.79/0.99  fof(f3,axiom,(
% 2.79/0.99    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f21,plain,(
% 2.79/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f3])).
% 2.79/0.99  
% 2.79/0.99  fof(f32,plain,(
% 2.79/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 2.79/0.99    inference(definition_unfolding,[],[f27,f21])).
% 2.79/0.99  
% 2.79/0.99  fof(f33,plain,(
% 2.79/0.99    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) = k2_tarski(X0,X1)) )),
% 2.79/0.99    inference(definition_unfolding,[],[f28,f32])).
% 2.79/0.99  
% 2.79/0.99  fof(f34,plain,(
% 2.79/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0)))) = k1_enumset1(X0,X1,X2)) )),
% 2.79/0.99    inference(definition_unfolding,[],[f29,f32,f33])).
% 2.79/0.99  
% 2.79/0.99  fof(f37,plain,(
% 2.79/0.99    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0))))),
% 2.79/0.99    inference(definition_unfolding,[],[f31,f33,f34])).
% 2.79/0.99  
% 2.79/0.99  fof(f4,axiom,(
% 2.79/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f15,plain,(
% 2.79/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.79/0.99    inference(ennf_transformation,[],[f4])).
% 2.79/0.99  
% 2.79/0.99  fof(f22,plain,(
% 2.79/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.79/0.99    inference(cnf_transformation,[],[f15])).
% 2.79/0.99  
% 2.79/0.99  fof(f6,axiom,(
% 2.79/0.99    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.79/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.79/0.99  
% 2.79/0.99  fof(f24,plain,(
% 2.79/0.99    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.79/0.99    inference(cnf_transformation,[],[f6])).
% 2.79/0.99  
% 2.79/0.99  fof(f36,plain,(
% 2.79/0.99    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 2.79/0.99    inference(definition_unfolding,[],[f24,f32])).
% 2.79/0.99  
% 2.79/0.99  cnf(c_7,plain,
% 2.79/0.99      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.79/0.99      inference(cnf_transformation,[],[f26]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_6,plain,
% 2.79/0.99      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 2.79/0.99      inference(cnf_transformation,[],[f25]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_89,plain,
% 2.79/0.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_7,c_6]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_4,plain,
% 2.79/0.99      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.79/0.99      inference(cnf_transformation,[],[f23]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_2,plain,
% 2.79/0.99      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 2.79/0.99      inference(cnf_transformation,[],[f20]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_69,plain,
% 2.79/0.99      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_4,c_2]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_96,plain,
% 2.79/0.99      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 2.79/0.99      inference(demodulation,[status(thm)],[c_89,c_69]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_1,plain,
% 2.79/0.99      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.79/0.99      inference(cnf_transformation,[],[f19]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_8,negated_conjecture,
% 2.79/0.99      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0)))) ),
% 2.79/0.99      inference(cnf_transformation,[],[f37]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_55,negated_conjecture,
% 2.79/0.99      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0)))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) ),
% 2.79/0.99      inference(theory_normalisation,[status(thm)],[c_8,c_6,c_2]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_66,plain,
% 2.79/0.99      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k1_tarski(sK0)))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
% 2.79/0.99      inference(demodulation,[status(thm)],[c_1,c_55]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_67,plain,
% 2.79/0.99      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_1,c_66]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_130,plain,
% 2.79/0.99      ( k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
% 2.79/0.99      inference(demodulation,[status(thm)],[c_96,c_67]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_3,plain,
% 2.79/0.99      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 2.79/0.99      inference(cnf_transformation,[],[f22]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_5,plain,
% 2.79/0.99      ( r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
% 2.79/0.99      inference(cnf_transformation,[],[f36]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_43,plain,
% 2.79/0.99      ( X0 != X1
% 2.79/0.99      | k5_xboole_0(X0,k5_xboole_0(X2,k3_xboole_0(X2,X0))) != X3
% 2.79/0.99      | k3_xboole_0(X1,X3) = X1 ),
% 2.79/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_5]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_44,plain,
% 2.79/0.99      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0 ),
% 2.79/0.99      inference(unflattening,[status(thm)],[c_43]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_80,plain,
% 2.79/0.99      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 2.79/0.99      inference(superposition,[status(thm)],[c_1,c_44]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_131,plain,
% 2.79/0.99      ( k5_xboole_0(k1_tarski(sK1),k5_xboole_0(k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
% 2.79/0.99      inference(demodulation,[status(thm)],[c_130,c_80]) ).
% 2.79/0.99  
% 2.79/0.99  cnf(c_155,plain,
% 2.79/0.99      ( $false ),
% 2.79/0.99      inference(theory_normalisation,[status(thm)],[c_131]) ).
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.79/0.99  
% 2.79/0.99  ------                               Statistics
% 2.79/0.99  
% 2.79/0.99  ------ General
% 2.79/0.99  
% 2.79/0.99  abstr_ref_over_cycles:                  0
% 2.79/0.99  abstr_ref_under_cycles:                 0
% 2.79/0.99  gc_basic_clause_elim:                   0
% 2.79/0.99  forced_gc_time:                         0
% 2.79/0.99  parsing_time:                           0.009
% 2.79/0.99  unif_index_cands_time:                  0.
% 2.79/0.99  unif_index_add_time:                    0.
% 2.79/0.99  orderings_time:                         0.
% 2.79/0.99  out_proof_time:                         0.009
% 2.79/0.99  total_time:                             0.046
% 2.79/0.99  num_of_symbols:                         38
% 2.79/0.99  num_of_terms:                           390
% 2.79/0.99  
% 2.79/0.99  ------ Preprocessing
% 2.79/0.99  
% 2.79/0.99  num_of_splits:                          0
% 2.79/0.99  num_of_split_atoms:                     0
% 2.79/0.99  num_of_reused_defs:                     0
% 2.79/0.99  num_eq_ax_congr_red:                    1
% 2.79/0.99  num_of_sem_filtered_clauses:            0
% 2.79/0.99  num_of_subtypes:                        0
% 2.79/0.99  monotx_restored_types:                  0
% 2.79/0.99  sat_num_of_epr_types:                   0
% 2.79/0.99  sat_num_of_non_cyclic_types:            0
% 2.79/0.99  sat_guarded_non_collapsed_types:        0
% 2.79/0.99  num_pure_diseq_elim:                    0
% 2.79/0.99  simp_replaced_by:                       0
% 2.79/0.99  res_preprocessed:                       30
% 2.79/0.99  prep_upred:                             0
% 2.79/0.99  prep_unflattend:                        2
% 2.79/0.99  smt_new_axioms:                         0
% 2.79/0.99  pred_elim_cands:                        0
% 2.79/0.99  pred_elim:                              1
% 2.79/0.99  pred_elim_cl:                           1
% 2.79/0.99  pred_elim_cycles:                       2
% 2.79/0.99  merged_defs:                            0
% 2.79/0.99  merged_defs_ncl:                        0
% 2.79/0.99  bin_hyper_res:                          0
% 2.79/0.99  prep_cycles:                            3
% 2.79/0.99  pred_elim_time:                         0.
% 2.79/0.99  splitting_time:                         0.
% 2.79/0.99  sem_filter_time:                        0.
% 2.79/0.99  monotx_time:                            0.
% 2.79/0.99  subtype_inf_time:                       0.
% 2.79/0.99  
% 2.79/0.99  ------ Problem properties
% 2.79/0.99  
% 2.79/0.99  clauses:                                8
% 2.79/0.99  conjectures:                            1
% 2.79/0.99  epr:                                    0
% 2.79/0.99  horn:                                   8
% 2.79/0.99  ground:                                 1
% 2.79/0.99  unary:                                  8
% 2.79/0.99  binary:                                 0
% 2.79/0.99  lits:                                   8
% 2.79/0.99  lits_eq:                                8
% 2.79/0.99  fd_pure:                                0
% 2.79/0.99  fd_pseudo:                              0
% 2.79/0.99  fd_cond:                                0
% 2.79/0.99  fd_pseudo_cond:                         0
% 2.79/0.99  ac_symbols:                             1
% 2.79/0.99  
% 2.79/0.99  ------ Propositional Solver
% 2.79/0.99  
% 2.79/0.99  prop_solver_calls:                      17
% 2.79/0.99  prop_fast_solver_calls:                 77
% 2.79/0.99  smt_solver_calls:                       0
% 2.79/0.99  smt_fast_solver_calls:                  0
% 2.79/0.99  prop_num_of_clauses:                    42
% 2.79/0.99  prop_preprocess_simplified:             429
% 2.79/0.99  prop_fo_subsumed:                       0
% 2.79/0.99  prop_solver_time:                       0.
% 2.79/0.99  smt_solver_time:                        0.
% 2.79/0.99  smt_fast_solver_time:                   0.
% 2.79/0.99  prop_fast_solver_time:                  0.
% 2.79/0.99  prop_unsat_core_time:                   0.
% 2.79/0.99  
% 2.79/0.99  ------ QBF
% 2.79/0.99  
% 2.79/0.99  qbf_q_res:                              0
% 2.79/0.99  qbf_num_tautologies:                    0
% 2.79/0.99  qbf_prep_cycles:                        0
% 2.79/0.99  
% 2.79/0.99  ------ BMC1
% 2.79/0.99  
% 2.79/0.99  bmc1_current_bound:                     -1
% 2.79/0.99  bmc1_last_solved_bound:                 -1
% 2.79/0.99  bmc1_unsat_core_size:                   -1
% 2.79/0.99  bmc1_unsat_core_parents_size:           -1
% 2.79/0.99  bmc1_merge_next_fun:                    0
% 2.79/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.79/0.99  
% 2.79/0.99  ------ Instantiation
% 2.79/0.99  
% 2.79/0.99  inst_num_of_clauses:                    0
% 2.79/0.99  inst_num_in_passive:                    0
% 2.79/0.99  inst_num_in_active:                     0
% 2.79/0.99  inst_num_in_unprocessed:                0
% 2.79/0.99  inst_num_of_loops:                      0
% 2.79/0.99  inst_num_of_learning_restarts:          0
% 2.79/0.99  inst_num_moves_active_passive:          0
% 2.79/0.99  inst_lit_activity:                      0
% 2.79/0.99  inst_lit_activity_moves:                0
% 2.79/0.99  inst_num_tautologies:                   0
% 2.79/0.99  inst_num_prop_implied:                  0
% 2.79/0.99  inst_num_existing_simplified:           0
% 2.79/0.99  inst_num_eq_res_simplified:             0
% 2.79/0.99  inst_num_child_elim:                    0
% 2.79/0.99  inst_num_of_dismatching_blockings:      0
% 2.79/0.99  inst_num_of_non_proper_insts:           0
% 2.79/0.99  inst_num_of_duplicates:                 0
% 2.79/0.99  inst_inst_num_from_inst_to_res:         0
% 2.79/0.99  inst_dismatching_checking_time:         0.
% 2.79/0.99  
% 2.79/0.99  ------ Resolution
% 2.79/0.99  
% 2.79/0.99  res_num_of_clauses:                     0
% 2.79/0.99  res_num_in_passive:                     0
% 2.79/0.99  res_num_in_active:                      0
% 2.79/0.99  res_num_of_loops:                       33
% 2.79/0.99  res_forward_subset_subsumed:            0
% 2.79/0.99  res_backward_subset_subsumed:           0
% 2.79/0.99  res_forward_subsumed:                   0
% 2.79/0.99  res_backward_subsumed:                  0
% 2.79/0.99  res_forward_subsumption_resolution:     0
% 2.79/0.99  res_backward_subsumption_resolution:    0
% 2.79/0.99  res_clause_to_clause_subsumption:       97
% 2.79/0.99  res_orphan_elimination:                 0
% 2.79/0.99  res_tautology_del:                      0
% 2.79/0.99  res_num_eq_res_simplified:              0
% 2.79/0.99  res_num_sel_changes:                    0
% 2.79/0.99  res_moves_from_active_to_pass:          0
% 2.79/0.99  
% 2.79/0.99  ------ Superposition
% 2.79/0.99  
% 2.79/0.99  sup_time_total:                         0.
% 2.79/0.99  sup_time_generating:                    0.
% 2.79/0.99  sup_time_sim_full:                      0.
% 2.79/0.99  sup_time_sim_immed:                     0.
% 2.79/0.99  
% 2.79/0.99  sup_num_of_clauses:                     29
% 2.79/0.99  sup_num_in_active:                      11
% 2.79/0.99  sup_num_in_passive:                     18
% 2.79/0.99  sup_num_of_loops:                       15
% 2.79/0.99  sup_fw_superposition:                   39
% 2.79/0.99  sup_bw_superposition:                   23
% 2.79/0.99  sup_immediate_simplified:               20
% 2.79/0.99  sup_given_eliminated:                   1
% 2.79/0.99  comparisons_done:                       0
% 2.79/0.99  comparisons_avoided:                    0
% 2.79/0.99  
% 2.79/0.99  ------ Simplifications
% 2.79/0.99  
% 2.79/0.99  
% 2.79/0.99  sim_fw_subset_subsumed:                 0
% 2.79/0.99  sim_bw_subset_subsumed:                 0
% 2.79/0.99  sim_fw_subsumed:                        4
% 2.79/0.99  sim_bw_subsumed:                        0
% 2.79/0.99  sim_fw_subsumption_res:                 0
% 2.79/0.99  sim_bw_subsumption_res:                 0
% 2.79/0.99  sim_tautology_del:                      0
% 2.79/0.99  sim_eq_tautology_del:                   8
% 2.79/0.99  sim_eq_res_simp:                        0
% 2.79/0.99  sim_fw_demodulated:                     12
% 2.79/0.99  sim_bw_demodulated:                     4
% 2.79/0.99  sim_light_normalised:                   7
% 2.79/0.99  sim_joinable_taut:                      0
% 2.79/0.99  sim_joinable_simp:                      1
% 2.79/0.99  sim_ac_normalised:                      0
% 2.79/0.99  sim_smt_subsumption:                    0
% 2.79/0.99  
%------------------------------------------------------------------------------
