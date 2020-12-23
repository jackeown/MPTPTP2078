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
% DateTime   : Thu Dec  3 11:26:55 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 563 expanded)
%              Number of clauses        :   25 ( 152 expanded)
%              Number of leaves         :   11 ( 152 expanded)
%              Depth                    :   15
%              Number of atoms          :   57 ( 564 expanded)
%              Number of equality atoms :   56 ( 563 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    9 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f8,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f25,f20])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f23,f20,f30])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
    inference(definition_unfolding,[],[f22,f30])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f12,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f12])).

fof(f15,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f13])).

fof(f16,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)
   => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f29,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f26,f30])).

fof(f32,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0)))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f27,f30,f31])).

fof(f37,plain,(
    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0)))) ),
    inference(definition_unfolding,[],[f29,f31,f32])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_5,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_69,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_5])).

cnf(c_2,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_71,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_5])).

cnf(c_4,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_58,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_2,c_4])).

cnf(c_61,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_58,c_2])).

cnf(c_76,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_71,c_2,c_61])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_83,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[status(thm)],[c_76,c_6])).

cnf(c_135,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_76,c_83])).

cnf(c_93,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_61,c_61,c_76])).

cnf(c_153,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_135,c_93])).

cnf(c_157,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_153,c_83])).

cnf(c_366,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_69,c_157])).

cnf(c_373,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    inference(light_normalisation,[status(thm)],[c_366,c_93])).

cnf(c_7,negated_conjecture,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0)))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_29,plain,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(demodulation,[status(thm)],[c_1,c_7])).

cnf(c_40,plain,
    ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(demodulation,[status(thm)],[c_6,c_29])).

cnf(c_85,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(demodulation,[status(thm)],[c_40,c_83])).

cnf(c_87,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(superposition,[status(thm)],[c_1,c_85])).

cnf(c_222,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(demodulation,[status(thm)],[c_153,c_87])).

cnf(c_2526,plain,
    ( k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK0)) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
    inference(demodulation,[status(thm)],[c_373,c_222])).

cnf(c_2527,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_2526])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:09:35 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 2.70/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/0.96  
% 2.70/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.70/0.96  
% 2.70/0.96  ------  iProver source info
% 2.70/0.96  
% 2.70/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.70/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.70/0.96  git: non_committed_changes: false
% 2.70/0.96  git: last_make_outside_of_git: false
% 2.70/0.96  
% 2.70/0.96  ------ 
% 2.70/0.96  
% 2.70/0.96  ------ Input Options
% 2.70/0.96  
% 2.70/0.96  --out_options                           all
% 2.70/0.96  --tptp_safe_out                         true
% 2.70/0.96  --problem_path                          ""
% 2.70/0.96  --include_path                          ""
% 2.70/0.96  --clausifier                            res/vclausify_rel
% 2.70/0.96  --clausifier_options                    --mode clausify
% 2.70/0.96  --stdin                                 false
% 2.70/0.96  --stats_out                             all
% 2.70/0.96  
% 2.70/0.96  ------ General Options
% 2.70/0.96  
% 2.70/0.96  --fof                                   false
% 2.70/0.96  --time_out_real                         305.
% 2.70/0.96  --time_out_virtual                      -1.
% 2.70/0.96  --symbol_type_check                     false
% 2.70/0.96  --clausify_out                          false
% 2.70/0.96  --sig_cnt_out                           false
% 2.70/0.96  --trig_cnt_out                          false
% 2.70/0.96  --trig_cnt_out_tolerance                1.
% 2.70/0.96  --trig_cnt_out_sk_spl                   false
% 2.70/0.96  --abstr_cl_out                          false
% 2.70/0.96  
% 2.70/0.96  ------ Global Options
% 2.70/0.96  
% 2.70/0.96  --schedule                              default
% 2.70/0.96  --add_important_lit                     false
% 2.70/0.96  --prop_solver_per_cl                    1000
% 2.70/0.96  --min_unsat_core                        false
% 2.70/0.96  --soft_assumptions                      false
% 2.70/0.96  --soft_lemma_size                       3
% 2.70/0.96  --prop_impl_unit_size                   0
% 2.70/0.96  --prop_impl_unit                        []
% 2.70/0.96  --share_sel_clauses                     true
% 2.70/0.96  --reset_solvers                         false
% 2.70/0.96  --bc_imp_inh                            [conj_cone]
% 2.70/0.96  --conj_cone_tolerance                   3.
% 2.70/0.96  --extra_neg_conj                        none
% 2.70/0.96  --large_theory_mode                     true
% 2.70/0.96  --prolific_symb_bound                   200
% 2.70/0.96  --lt_threshold                          2000
% 2.70/0.96  --clause_weak_htbl                      true
% 2.70/0.96  --gc_record_bc_elim                     false
% 2.70/0.96  
% 2.70/0.96  ------ Preprocessing Options
% 2.70/0.96  
% 2.70/0.96  --preprocessing_flag                    true
% 2.70/0.96  --time_out_prep_mult                    0.1
% 2.70/0.96  --splitting_mode                        input
% 2.70/0.96  --splitting_grd                         true
% 2.70/0.96  --splitting_cvd                         false
% 2.70/0.96  --splitting_cvd_svl                     false
% 2.70/0.96  --splitting_nvd                         32
% 2.70/0.96  --sub_typing                            true
% 2.70/0.96  --prep_gs_sim                           true
% 2.70/0.96  --prep_unflatten                        true
% 2.70/0.96  --prep_res_sim                          true
% 2.70/0.96  --prep_upred                            true
% 2.70/0.96  --prep_sem_filter                       exhaustive
% 2.70/0.96  --prep_sem_filter_out                   false
% 2.70/0.96  --pred_elim                             true
% 2.70/0.96  --res_sim_input                         true
% 2.70/0.96  --eq_ax_congr_red                       true
% 2.70/0.96  --pure_diseq_elim                       true
% 2.70/0.96  --brand_transform                       false
% 2.70/0.96  --non_eq_to_eq                          false
% 2.70/0.96  --prep_def_merge                        true
% 2.70/0.96  --prep_def_merge_prop_impl              false
% 2.70/0.96  --prep_def_merge_mbd                    true
% 2.70/0.96  --prep_def_merge_tr_red                 false
% 2.70/0.96  --prep_def_merge_tr_cl                  false
% 2.70/0.96  --smt_preprocessing                     true
% 2.70/0.96  --smt_ac_axioms                         fast
% 2.70/0.96  --preprocessed_out                      false
% 2.70/0.96  --preprocessed_stats                    false
% 2.70/0.96  
% 2.70/0.96  ------ Abstraction refinement Options
% 2.70/0.96  
% 2.70/0.96  --abstr_ref                             []
% 2.70/0.96  --abstr_ref_prep                        false
% 2.70/0.96  --abstr_ref_until_sat                   false
% 2.70/0.96  --abstr_ref_sig_restrict                funpre
% 2.70/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/0.96  --abstr_ref_under                       []
% 2.70/0.96  
% 2.70/0.96  ------ SAT Options
% 2.70/0.96  
% 2.70/0.96  --sat_mode                              false
% 2.70/0.96  --sat_fm_restart_options                ""
% 2.70/0.96  --sat_gr_def                            false
% 2.70/0.96  --sat_epr_types                         true
% 2.70/0.96  --sat_non_cyclic_types                  false
% 2.70/0.96  --sat_finite_models                     false
% 2.70/0.96  --sat_fm_lemmas                         false
% 2.70/0.96  --sat_fm_prep                           false
% 2.70/0.96  --sat_fm_uc_incr                        true
% 2.70/0.96  --sat_out_model                         small
% 2.70/0.96  --sat_out_clauses                       false
% 2.70/0.96  
% 2.70/0.96  ------ QBF Options
% 2.70/0.96  
% 2.70/0.96  --qbf_mode                              false
% 2.70/0.96  --qbf_elim_univ                         false
% 2.70/0.96  --qbf_dom_inst                          none
% 2.70/0.96  --qbf_dom_pre_inst                      false
% 2.70/0.96  --qbf_sk_in                             false
% 2.70/0.96  --qbf_pred_elim                         true
% 2.70/0.96  --qbf_split                             512
% 2.70/0.96  
% 2.70/0.96  ------ BMC1 Options
% 2.70/0.96  
% 2.70/0.96  --bmc1_incremental                      false
% 2.70/0.96  --bmc1_axioms                           reachable_all
% 2.70/0.96  --bmc1_min_bound                        0
% 2.70/0.96  --bmc1_max_bound                        -1
% 2.70/0.96  --bmc1_max_bound_default                -1
% 2.70/0.96  --bmc1_symbol_reachability              true
% 2.70/0.96  --bmc1_property_lemmas                  false
% 2.70/0.96  --bmc1_k_induction                      false
% 2.70/0.96  --bmc1_non_equiv_states                 false
% 2.70/0.96  --bmc1_deadlock                         false
% 2.70/0.96  --bmc1_ucm                              false
% 2.70/0.96  --bmc1_add_unsat_core                   none
% 2.70/0.97  --bmc1_unsat_core_children              false
% 2.70/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/0.97  --bmc1_out_stat                         full
% 2.70/0.97  --bmc1_ground_init                      false
% 2.70/0.97  --bmc1_pre_inst_next_state              false
% 2.70/0.97  --bmc1_pre_inst_state                   false
% 2.70/0.97  --bmc1_pre_inst_reach_state             false
% 2.70/0.97  --bmc1_out_unsat_core                   false
% 2.70/0.97  --bmc1_aig_witness_out                  false
% 2.70/0.97  --bmc1_verbose                          false
% 2.70/0.97  --bmc1_dump_clauses_tptp                false
% 2.70/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.70/0.97  --bmc1_dump_file                        -
% 2.70/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.70/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.70/0.97  --bmc1_ucm_extend_mode                  1
% 2.70/0.97  --bmc1_ucm_init_mode                    2
% 2.70/0.97  --bmc1_ucm_cone_mode                    none
% 2.70/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.70/0.97  --bmc1_ucm_relax_model                  4
% 2.70/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.70/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/0.97  --bmc1_ucm_layered_model                none
% 2.70/0.97  --bmc1_ucm_max_lemma_size               10
% 2.70/0.97  
% 2.70/0.97  ------ AIG Options
% 2.70/0.97  
% 2.70/0.97  --aig_mode                              false
% 2.70/0.97  
% 2.70/0.97  ------ Instantiation Options
% 2.70/0.97  
% 2.70/0.97  --instantiation_flag                    true
% 2.70/0.97  --inst_sos_flag                         false
% 2.70/0.97  --inst_sos_phase                        true
% 2.70/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/0.97  --inst_lit_sel_side                     num_symb
% 2.70/0.97  --inst_solver_per_active                1400
% 2.70/0.97  --inst_solver_calls_frac                1.
% 2.70/0.97  --inst_passive_queue_type               priority_queues
% 2.70/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/0.97  --inst_passive_queues_freq              [25;2]
% 2.70/0.97  --inst_dismatching                      true
% 2.70/0.97  --inst_eager_unprocessed_to_passive     true
% 2.70/0.97  --inst_prop_sim_given                   true
% 2.70/0.97  --inst_prop_sim_new                     false
% 2.70/0.97  --inst_subs_new                         false
% 2.70/0.97  --inst_eq_res_simp                      false
% 2.70/0.97  --inst_subs_given                       false
% 2.70/0.97  --inst_orphan_elimination               true
% 2.70/0.97  --inst_learning_loop_flag               true
% 2.70/0.97  --inst_learning_start                   3000
% 2.70/0.97  --inst_learning_factor                  2
% 2.70/0.97  --inst_start_prop_sim_after_learn       3
% 2.70/0.97  --inst_sel_renew                        solver
% 2.70/0.97  --inst_lit_activity_flag                true
% 2.70/0.97  --inst_restr_to_given                   false
% 2.70/0.97  --inst_activity_threshold               500
% 2.70/0.97  --inst_out_proof                        true
% 2.70/0.97  
% 2.70/0.97  ------ Resolution Options
% 2.70/0.97  
% 2.70/0.97  --resolution_flag                       true
% 2.70/0.97  --res_lit_sel                           adaptive
% 2.70/0.97  --res_lit_sel_side                      none
% 2.70/0.97  --res_ordering                          kbo
% 2.70/0.97  --res_to_prop_solver                    active
% 2.70/0.97  --res_prop_simpl_new                    false
% 2.70/0.97  --res_prop_simpl_given                  true
% 2.70/0.97  --res_passive_queue_type                priority_queues
% 2.70/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/0.97  --res_passive_queues_freq               [15;5]
% 2.70/0.97  --res_forward_subs                      full
% 2.70/0.97  --res_backward_subs                     full
% 2.70/0.97  --res_forward_subs_resolution           true
% 2.70/0.97  --res_backward_subs_resolution          true
% 2.70/0.97  --res_orphan_elimination                true
% 2.70/0.97  --res_time_limit                        2.
% 2.70/0.97  --res_out_proof                         true
% 2.70/0.97  
% 2.70/0.97  ------ Superposition Options
% 2.70/0.97  
% 2.70/0.97  --superposition_flag                    true
% 2.70/0.97  --sup_passive_queue_type                priority_queues
% 2.70/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.70/0.97  --demod_completeness_check              fast
% 2.70/0.97  --demod_use_ground                      true
% 2.70/0.97  --sup_to_prop_solver                    passive
% 2.70/0.97  --sup_prop_simpl_new                    true
% 2.70/0.97  --sup_prop_simpl_given                  true
% 2.70/0.97  --sup_fun_splitting                     false
% 2.70/0.97  --sup_smt_interval                      50000
% 2.70/0.97  
% 2.70/0.97  ------ Superposition Simplification Setup
% 2.70/0.97  
% 2.70/0.97  --sup_indices_passive                   []
% 2.70/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.70/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.97  --sup_full_bw                           [BwDemod]
% 2.70/0.97  --sup_immed_triv                        [TrivRules]
% 2.70/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.97  --sup_immed_bw_main                     []
% 2.70/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.70/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.70/0.97  
% 2.70/0.97  ------ Combination Options
% 2.70/0.97  
% 2.70/0.97  --comb_res_mult                         3
% 2.70/0.97  --comb_sup_mult                         2
% 2.70/0.97  --comb_inst_mult                        10
% 2.70/0.97  
% 2.70/0.97  ------ Debug Options
% 2.70/0.97  
% 2.70/0.97  --dbg_backtrace                         false
% 2.70/0.97  --dbg_dump_prop_clauses                 false
% 2.70/0.97  --dbg_dump_prop_clauses_file            -
% 2.70/0.97  --dbg_out_stat                          false
% 2.70/0.97  ------ Parsing...
% 2.70/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.70/0.97  
% 2.70/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.70/0.97  
% 2.70/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.70/0.97  
% 2.70/0.97  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.70/0.97  ------ Proving...
% 2.70/0.97  ------ Problem Properties 
% 2.70/0.97  
% 2.70/0.97  
% 2.70/0.97  clauses                                 8
% 2.70/0.97  conjectures                             1
% 2.70/0.97  EPR                                     0
% 2.70/0.97  Horn                                    8
% 2.70/0.97  unary                                   8
% 2.70/0.97  binary                                  0
% 2.70/0.97  lits                                    8
% 2.70/0.97  lits eq                                 8
% 2.70/0.97  fd_pure                                 0
% 2.70/0.97  fd_pseudo                               0
% 2.70/0.97  fd_cond                                 0
% 2.70/0.97  fd_pseudo_cond                          0
% 2.70/0.97  AC symbols                              0
% 2.70/0.97  
% 2.70/0.97  ------ Schedule UEQ
% 2.70/0.97  
% 2.70/0.97  ------ pure equality problem: resolution off 
% 2.70/0.97  
% 2.70/0.97  ------ Option_UEQ Time Limit: Unbounded
% 2.70/0.97  
% 2.70/0.97  
% 2.70/0.97  ------ 
% 2.70/0.97  Current options:
% 2.70/0.97  ------ 
% 2.70/0.97  
% 2.70/0.97  ------ Input Options
% 2.70/0.97  
% 2.70/0.97  --out_options                           all
% 2.70/0.97  --tptp_safe_out                         true
% 2.70/0.97  --problem_path                          ""
% 2.70/0.97  --include_path                          ""
% 2.70/0.97  --clausifier                            res/vclausify_rel
% 2.70/0.97  --clausifier_options                    --mode clausify
% 2.70/0.97  --stdin                                 false
% 2.70/0.97  --stats_out                             all
% 2.70/0.97  
% 2.70/0.97  ------ General Options
% 2.70/0.97  
% 2.70/0.97  --fof                                   false
% 2.70/0.97  --time_out_real                         305.
% 2.70/0.97  --time_out_virtual                      -1.
% 2.70/0.97  --symbol_type_check                     false
% 2.70/0.97  --clausify_out                          false
% 2.70/0.97  --sig_cnt_out                           false
% 2.70/0.97  --trig_cnt_out                          false
% 2.70/0.97  --trig_cnt_out_tolerance                1.
% 2.70/0.97  --trig_cnt_out_sk_spl                   false
% 2.70/0.97  --abstr_cl_out                          false
% 2.70/0.97  
% 2.70/0.97  ------ Global Options
% 2.70/0.97  
% 2.70/0.97  --schedule                              default
% 2.70/0.97  --add_important_lit                     false
% 2.70/0.97  --prop_solver_per_cl                    1000
% 2.70/0.97  --min_unsat_core                        false
% 2.70/0.97  --soft_assumptions                      false
% 2.70/0.97  --soft_lemma_size                       3
% 2.70/0.97  --prop_impl_unit_size                   0
% 2.70/0.97  --prop_impl_unit                        []
% 2.70/0.97  --share_sel_clauses                     true
% 2.70/0.97  --reset_solvers                         false
% 2.70/0.97  --bc_imp_inh                            [conj_cone]
% 2.70/0.97  --conj_cone_tolerance                   3.
% 2.70/0.97  --extra_neg_conj                        none
% 2.70/0.97  --large_theory_mode                     true
% 2.70/0.97  --prolific_symb_bound                   200
% 2.70/0.97  --lt_threshold                          2000
% 2.70/0.97  --clause_weak_htbl                      true
% 2.70/0.97  --gc_record_bc_elim                     false
% 2.70/0.97  
% 2.70/0.97  ------ Preprocessing Options
% 2.70/0.97  
% 2.70/0.97  --preprocessing_flag                    true
% 2.70/0.97  --time_out_prep_mult                    0.1
% 2.70/0.97  --splitting_mode                        input
% 2.70/0.97  --splitting_grd                         true
% 2.70/0.97  --splitting_cvd                         false
% 2.70/0.97  --splitting_cvd_svl                     false
% 2.70/0.97  --splitting_nvd                         32
% 2.70/0.97  --sub_typing                            true
% 2.70/0.97  --prep_gs_sim                           true
% 2.70/0.97  --prep_unflatten                        true
% 2.70/0.97  --prep_res_sim                          true
% 2.70/0.97  --prep_upred                            true
% 2.70/0.97  --prep_sem_filter                       exhaustive
% 2.70/0.97  --prep_sem_filter_out                   false
% 2.70/0.97  --pred_elim                             true
% 2.70/0.97  --res_sim_input                         true
% 2.70/0.97  --eq_ax_congr_red                       true
% 2.70/0.97  --pure_diseq_elim                       true
% 2.70/0.97  --brand_transform                       false
% 2.70/0.97  --non_eq_to_eq                          false
% 2.70/0.97  --prep_def_merge                        true
% 2.70/0.97  --prep_def_merge_prop_impl              false
% 2.70/0.97  --prep_def_merge_mbd                    true
% 2.70/0.97  --prep_def_merge_tr_red                 false
% 2.70/0.97  --prep_def_merge_tr_cl                  false
% 2.70/0.97  --smt_preprocessing                     true
% 2.70/0.97  --smt_ac_axioms                         fast
% 2.70/0.97  --preprocessed_out                      false
% 2.70/0.97  --preprocessed_stats                    false
% 2.70/0.97  
% 2.70/0.97  ------ Abstraction refinement Options
% 2.70/0.97  
% 2.70/0.97  --abstr_ref                             []
% 2.70/0.97  --abstr_ref_prep                        false
% 2.70/0.97  --abstr_ref_until_sat                   false
% 2.70/0.97  --abstr_ref_sig_restrict                funpre
% 2.70/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.70/0.97  --abstr_ref_under                       []
% 2.70/0.97  
% 2.70/0.97  ------ SAT Options
% 2.70/0.97  
% 2.70/0.97  --sat_mode                              false
% 2.70/0.97  --sat_fm_restart_options                ""
% 2.70/0.97  --sat_gr_def                            false
% 2.70/0.97  --sat_epr_types                         true
% 2.70/0.97  --sat_non_cyclic_types                  false
% 2.70/0.97  --sat_finite_models                     false
% 2.70/0.97  --sat_fm_lemmas                         false
% 2.70/0.97  --sat_fm_prep                           false
% 2.70/0.97  --sat_fm_uc_incr                        true
% 2.70/0.97  --sat_out_model                         small
% 2.70/0.97  --sat_out_clauses                       false
% 2.70/0.97  
% 2.70/0.97  ------ QBF Options
% 2.70/0.97  
% 2.70/0.97  --qbf_mode                              false
% 2.70/0.97  --qbf_elim_univ                         false
% 2.70/0.97  --qbf_dom_inst                          none
% 2.70/0.97  --qbf_dom_pre_inst                      false
% 2.70/0.97  --qbf_sk_in                             false
% 2.70/0.97  --qbf_pred_elim                         true
% 2.70/0.97  --qbf_split                             512
% 2.70/0.97  
% 2.70/0.97  ------ BMC1 Options
% 2.70/0.97  
% 2.70/0.97  --bmc1_incremental                      false
% 2.70/0.97  --bmc1_axioms                           reachable_all
% 2.70/0.97  --bmc1_min_bound                        0
% 2.70/0.97  --bmc1_max_bound                        -1
% 2.70/0.97  --bmc1_max_bound_default                -1
% 2.70/0.97  --bmc1_symbol_reachability              true
% 2.70/0.97  --bmc1_property_lemmas                  false
% 2.70/0.97  --bmc1_k_induction                      false
% 2.70/0.97  --bmc1_non_equiv_states                 false
% 2.70/0.97  --bmc1_deadlock                         false
% 2.70/0.97  --bmc1_ucm                              false
% 2.70/0.97  --bmc1_add_unsat_core                   none
% 2.70/0.97  --bmc1_unsat_core_children              false
% 2.70/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.70/0.97  --bmc1_out_stat                         full
% 2.70/0.97  --bmc1_ground_init                      false
% 2.70/0.97  --bmc1_pre_inst_next_state              false
% 2.70/0.97  --bmc1_pre_inst_state                   false
% 2.70/0.97  --bmc1_pre_inst_reach_state             false
% 2.70/0.97  --bmc1_out_unsat_core                   false
% 2.70/0.97  --bmc1_aig_witness_out                  false
% 2.70/0.97  --bmc1_verbose                          false
% 2.70/0.97  --bmc1_dump_clauses_tptp                false
% 2.70/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.70/0.97  --bmc1_dump_file                        -
% 2.70/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.70/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.70/0.97  --bmc1_ucm_extend_mode                  1
% 2.70/0.97  --bmc1_ucm_init_mode                    2
% 2.70/0.97  --bmc1_ucm_cone_mode                    none
% 2.70/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.70/0.97  --bmc1_ucm_relax_model                  4
% 2.70/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.70/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.70/0.97  --bmc1_ucm_layered_model                none
% 2.70/0.97  --bmc1_ucm_max_lemma_size               10
% 2.70/0.97  
% 2.70/0.97  ------ AIG Options
% 2.70/0.97  
% 2.70/0.97  --aig_mode                              false
% 2.70/0.97  
% 2.70/0.97  ------ Instantiation Options
% 2.70/0.97  
% 2.70/0.97  --instantiation_flag                    false
% 2.70/0.97  --inst_sos_flag                         false
% 2.70/0.97  --inst_sos_phase                        true
% 2.70/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.70/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.70/0.97  --inst_lit_sel_side                     num_symb
% 2.70/0.97  --inst_solver_per_active                1400
% 2.70/0.97  --inst_solver_calls_frac                1.
% 2.70/0.97  --inst_passive_queue_type               priority_queues
% 2.70/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.70/0.97  --inst_passive_queues_freq              [25;2]
% 2.70/0.97  --inst_dismatching                      true
% 2.70/0.97  --inst_eager_unprocessed_to_passive     true
% 2.70/0.97  --inst_prop_sim_given                   true
% 2.70/0.97  --inst_prop_sim_new                     false
% 2.70/0.97  --inst_subs_new                         false
% 2.70/0.97  --inst_eq_res_simp                      false
% 2.70/0.97  --inst_subs_given                       false
% 2.70/0.97  --inst_orphan_elimination               true
% 2.70/0.97  --inst_learning_loop_flag               true
% 2.70/0.97  --inst_learning_start                   3000
% 2.70/0.97  --inst_learning_factor                  2
% 2.70/0.97  --inst_start_prop_sim_after_learn       3
% 2.70/0.97  --inst_sel_renew                        solver
% 2.70/0.97  --inst_lit_activity_flag                true
% 2.70/0.97  --inst_restr_to_given                   false
% 2.70/0.97  --inst_activity_threshold               500
% 2.70/0.97  --inst_out_proof                        true
% 2.70/0.97  
% 2.70/0.97  ------ Resolution Options
% 2.70/0.97  
% 2.70/0.97  --resolution_flag                       false
% 2.70/0.97  --res_lit_sel                           adaptive
% 2.70/0.97  --res_lit_sel_side                      none
% 2.70/0.97  --res_ordering                          kbo
% 2.70/0.97  --res_to_prop_solver                    active
% 2.70/0.97  --res_prop_simpl_new                    false
% 2.70/0.97  --res_prop_simpl_given                  true
% 2.70/0.97  --res_passive_queue_type                priority_queues
% 2.70/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.70/0.97  --res_passive_queues_freq               [15;5]
% 2.70/0.97  --res_forward_subs                      full
% 2.70/0.97  --res_backward_subs                     full
% 2.70/0.97  --res_forward_subs_resolution           true
% 2.70/0.97  --res_backward_subs_resolution          true
% 2.70/0.97  --res_orphan_elimination                true
% 2.70/0.97  --res_time_limit                        2.
% 2.70/0.97  --res_out_proof                         true
% 2.70/0.97  
% 2.70/0.97  ------ Superposition Options
% 2.70/0.97  
% 2.70/0.97  --superposition_flag                    true
% 2.70/0.97  --sup_passive_queue_type                priority_queues
% 2.70/0.97  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.70/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.70/0.97  --demod_completeness_check              fast
% 2.70/0.97  --demod_use_ground                      true
% 2.70/0.97  --sup_to_prop_solver                    active
% 2.70/0.97  --sup_prop_simpl_new                    false
% 2.70/0.97  --sup_prop_simpl_given                  false
% 2.70/0.97  --sup_fun_splitting                     true
% 2.70/0.97  --sup_smt_interval                      10000
% 2.70/0.97  
% 2.70/0.97  ------ Superposition Simplification Setup
% 2.70/0.97  
% 2.70/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.70/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.70/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.70/0.97  --sup_full_triv                         [TrivRules]
% 2.70/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.70/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.70/0.97  --sup_immed_triv                        [TrivRules]
% 2.70/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.97  --sup_immed_bw_main                     []
% 2.70/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.70/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.70/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.70/0.97  --sup_input_bw                          [BwDemod;BwSubsumption]
% 2.70/0.97  
% 2.70/0.97  ------ Combination Options
% 2.70/0.97  
% 2.70/0.97  --comb_res_mult                         1
% 2.70/0.97  --comb_sup_mult                         1
% 2.70/0.97  --comb_inst_mult                        1000000
% 2.70/0.97  
% 2.70/0.97  ------ Debug Options
% 2.70/0.97  
% 2.70/0.97  --dbg_backtrace                         false
% 2.70/0.97  --dbg_dump_prop_clauses                 false
% 2.70/0.97  --dbg_dump_prop_clauses_file            -
% 2.70/0.97  --dbg_out_stat                          false
% 2.70/0.97  
% 2.70/0.97  
% 2.70/0.97  
% 2.70/0.97  
% 2.70/0.97  ------ Proving...
% 2.70/0.97  
% 2.70/0.97  
% 2.70/0.97  % SZS status Theorem for theBenchmark.p
% 2.70/0.97  
% 2.70/0.97   Resolution empty clause
% 2.70/0.97  
% 2.70/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.70/0.97  
% 2.70/0.97  fof(f1,axiom,(
% 2.70/0.97    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.70/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.97  
% 2.70/0.97  fof(f18,plain,(
% 2.70/0.97    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.70/0.97    inference(cnf_transformation,[],[f1])).
% 2.70/0.97  
% 2.70/0.97  fof(f6,axiom,(
% 2.70/0.97    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 2.70/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.97  
% 2.70/0.97  fof(f23,plain,(
% 2.70/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 2.70/0.97    inference(cnf_transformation,[],[f6])).
% 2.70/0.97  
% 2.70/0.97  fof(f8,axiom,(
% 2.70/0.97    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.70/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.97  
% 2.70/0.97  fof(f25,plain,(
% 2.70/0.97    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.70/0.97    inference(cnf_transformation,[],[f8])).
% 2.70/0.97  
% 2.70/0.97  fof(f3,axiom,(
% 2.70/0.97    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.70/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.97  
% 2.70/0.97  fof(f20,plain,(
% 2.70/0.97    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.70/0.97    inference(cnf_transformation,[],[f3])).
% 2.70/0.97  
% 2.70/0.97  fof(f30,plain,(
% 2.70/0.97    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1)) )),
% 2.70/0.97    inference(definition_unfolding,[],[f25,f20])).
% 2.70/0.97  
% 2.70/0.97  fof(f36,plain,(
% 2.70/0.97    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0) )),
% 2.70/0.97    inference(definition_unfolding,[],[f23,f20,f30])).
% 2.70/0.97  
% 2.70/0.97  fof(f2,axiom,(
% 2.70/0.97    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.70/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.97  
% 2.70/0.97  fof(f14,plain,(
% 2.70/0.97    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.70/0.97    inference(rectify,[],[f2])).
% 2.70/0.97  
% 2.70/0.97  fof(f19,plain,(
% 2.70/0.97    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.70/0.97    inference(cnf_transformation,[],[f14])).
% 2.70/0.97  
% 2.70/0.97  fof(f5,axiom,(
% 2.70/0.97    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.70/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.97  
% 2.70/0.97  fof(f22,plain,(
% 2.70/0.97    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.70/0.97    inference(cnf_transformation,[],[f5])).
% 2.70/0.97  
% 2.70/0.97  fof(f35,plain,(
% 2.70/0.97    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0) )),
% 2.70/0.97    inference(definition_unfolding,[],[f22,f30])).
% 2.70/0.97  
% 2.70/0.97  fof(f7,axiom,(
% 2.70/0.97    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 2.70/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.97  
% 2.70/0.97  fof(f24,plain,(
% 2.70/0.97    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 2.70/0.97    inference(cnf_transformation,[],[f7])).
% 2.70/0.97  
% 2.70/0.97  fof(f12,conjecture,(
% 2.70/0.97    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.70/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.97  
% 2.70/0.97  fof(f13,negated_conjecture,(
% 2.70/0.97    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.70/0.97    inference(negated_conjecture,[],[f12])).
% 2.70/0.97  
% 2.70/0.97  fof(f15,plain,(
% 2.70/0.97    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 2.70/0.97    inference(ennf_transformation,[],[f13])).
% 2.70/0.97  
% 2.70/0.97  fof(f16,plain,(
% 2.70/0.97    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) => k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 2.70/0.97    introduced(choice_axiom,[])).
% 2.70/0.97  
% 2.70/0.97  fof(f17,plain,(
% 2.70/0.97    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 2.70/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 2.70/0.97  
% 2.70/0.97  fof(f29,plain,(
% 2.70/0.97    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 2.70/0.97    inference(cnf_transformation,[],[f17])).
% 2.70/0.97  
% 2.70/0.97  fof(f10,axiom,(
% 2.70/0.97    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 2.70/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.97  
% 2.70/0.97  fof(f27,plain,(
% 2.70/0.97    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 2.70/0.97    inference(cnf_transformation,[],[f10])).
% 2.70/0.97  
% 2.70/0.97  fof(f9,axiom,(
% 2.70/0.97    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)),
% 2.70/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.70/0.97  
% 2.70/0.97  fof(f26,plain,(
% 2.70/0.97    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k2_tarski(X0,X1)) )),
% 2.70/0.97    inference(cnf_transformation,[],[f9])).
% 2.70/0.97  
% 2.70/0.97  fof(f31,plain,(
% 2.70/0.97    ( ! [X0,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k1_tarski(X1),k3_xboole_0(k1_tarski(X1),k1_tarski(X0)))) = k2_tarski(X0,X1)) )),
% 2.70/0.97    inference(definition_unfolding,[],[f26,f30])).
% 2.70/0.97  
% 2.70/0.97  fof(f32,plain,(
% 2.70/0.97    ( ! [X2,X0,X1] : (k5_xboole_0(k1_tarski(X0),k5_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k3_xboole_0(k5_xboole_0(k1_tarski(X1),k5_xboole_0(k1_tarski(X2),k3_xboole_0(k1_tarski(X2),k1_tarski(X1)))),k1_tarski(X0)))) = k1_enumset1(X0,X1,X2)) )),
% 2.70/0.97    inference(definition_unfolding,[],[f27,f30,f31])).
% 2.70/0.97  
% 2.70/0.97  fof(f37,plain,(
% 2.70/0.97    k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0))))),
% 2.70/0.97    inference(definition_unfolding,[],[f29,f31,f32])).
% 2.70/0.97  
% 2.70/0.97  cnf(c_1,plain,
% 2.70/0.97      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 2.70/0.97      inference(cnf_transformation,[],[f18]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_5,plain,
% 2.70/0.97      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) = k1_xboole_0 ),
% 2.70/0.97      inference(cnf_transformation,[],[f36]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_69,plain,
% 2.70/0.97      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))))) = k1_xboole_0 ),
% 2.70/0.97      inference(superposition,[status(thm)],[c_1,c_5]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_2,plain,
% 2.70/0.97      ( k3_xboole_0(X0,X0) = X0 ),
% 2.70/0.97      inference(cnf_transformation,[],[f19]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_71,plain,
% 2.70/0.97      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X0,X0)))) = k1_xboole_0 ),
% 2.70/0.97      inference(superposition,[status(thm)],[c_2,c_5]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_4,plain,
% 2.70/0.97      ( k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X0))) = X0 ),
% 2.70/0.97      inference(cnf_transformation,[],[f35]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_58,plain,
% 2.70/0.97      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
% 2.70/0.97      inference(superposition,[status(thm)],[c_2,c_4]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_61,plain,
% 2.70/0.97      ( k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
% 2.70/0.97      inference(light_normalisation,[status(thm)],[c_58,c_2]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_76,plain,
% 2.70/0.97      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.70/0.97      inference(light_normalisation,[status(thm)],[c_71,c_2,c_61]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_6,plain,
% 2.70/0.97      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 2.70/0.97      inference(cnf_transformation,[],[f24]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_83,plain,
% 2.70/0.97      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
% 2.70/0.97      inference(superposition,[status(thm)],[c_76,c_6]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_135,plain,
% 2.70/0.97      ( k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
% 2.70/0.97      inference(superposition,[status(thm)],[c_76,c_83]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_93,plain,
% 2.70/0.97      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.70/0.97      inference(light_normalisation,[status(thm)],[c_61,c_61,c_76]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_153,plain,
% 2.70/0.97      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 2.70/0.97      inference(light_normalisation,[status(thm)],[c_135,c_93]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_157,plain,
% 2.70/0.97      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 2.70/0.97      inference(demodulation,[status(thm)],[c_153,c_83]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_366,plain,
% 2.70/0.97      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = k5_xboole_0(X0,k1_xboole_0) ),
% 2.70/0.97      inference(superposition,[status(thm)],[c_69,c_157]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_373,plain,
% 2.70/0.97      ( k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
% 2.70/0.97      inference(light_normalisation,[status(thm)],[c_366,c_93]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_7,negated_conjecture,
% 2.70/0.97      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK1),k1_tarski(sK0)))),k1_tarski(sK0)))) ),
% 2.70/0.97      inference(cnf_transformation,[],[f37]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_29,plain,
% 2.70/0.97      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
% 2.70/0.97      inference(demodulation,[status(thm)],[c_1,c_7]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_40,plain,
% 2.70/0.97      ( k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k1_tarski(sK0))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
% 2.70/0.97      inference(demodulation,[status(thm)],[c_6,c_29]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_85,plain,
% 2.70/0.97      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k3_xboole_0(k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),k1_tarski(sK0)))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
% 2.70/0.97      inference(demodulation,[status(thm)],[c_40,c_83]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_87,plain,
% 2.70/0.97      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
% 2.70/0.97      inference(superposition,[status(thm)],[c_1,c_85]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_222,plain,
% 2.70/0.97      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k3_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))))) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
% 2.70/0.97      inference(demodulation,[status(thm)],[c_153,c_87]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_2526,plain,
% 2.70/0.97      ( k5_xboole_0(k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK0)) != k5_xboole_0(k1_tarski(sK0),k5_xboole_0(k1_tarski(sK1),k3_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))) ),
% 2.70/0.97      inference(demodulation,[status(thm)],[c_373,c_222]) ).
% 2.70/0.97  
% 2.70/0.97  cnf(c_2527,plain,
% 2.70/0.97      ( $false ),
% 2.70/0.97      inference(theory_normalisation,[status(thm)],[c_2526]) ).
% 2.70/0.97  
% 2.70/0.97  
% 2.70/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.70/0.97  
% 2.70/0.97  ------                               Statistics
% 2.70/0.97  
% 2.70/0.97  ------ General
% 2.70/0.97  
% 2.70/0.97  abstr_ref_over_cycles:                  0
% 2.70/0.97  abstr_ref_under_cycles:                 0
% 2.70/0.97  gc_basic_clause_elim:                   0
% 2.70/0.97  forced_gc_time:                         0
% 2.70/0.97  parsing_time:                           0.009
% 2.70/0.97  unif_index_cands_time:                  0.
% 2.70/0.97  unif_index_add_time:                    0.
% 2.70/0.97  orderings_time:                         0.
% 2.70/0.97  out_proof_time:                         0.008
% 2.70/0.97  total_time:                             0.113
% 2.70/0.97  num_of_symbols:                         37
% 2.70/0.97  num_of_terms:                           3314
% 2.70/0.97  
% 2.70/0.97  ------ Preprocessing
% 2.70/0.97  
% 2.70/0.97  num_of_splits:                          0
% 2.70/0.97  num_of_split_atoms:                     0
% 2.70/0.97  num_of_reused_defs:                     0
% 2.70/0.97  num_eq_ax_congr_red:                    0
% 2.70/0.97  num_of_sem_filtered_clauses:            0
% 2.70/0.97  num_of_subtypes:                        0
% 2.70/0.97  monotx_restored_types:                  0
% 2.70/0.97  sat_num_of_epr_types:                   0
% 2.70/0.97  sat_num_of_non_cyclic_types:            0
% 2.70/0.97  sat_guarded_non_collapsed_types:        0
% 2.70/0.97  num_pure_diseq_elim:                    0
% 2.70/0.97  simp_replaced_by:                       0
% 2.70/0.97  res_preprocessed:                       21
% 2.70/0.97  prep_upred:                             0
% 2.70/0.97  prep_unflattend:                        0
% 2.70/0.97  smt_new_axioms:                         0
% 2.70/0.97  pred_elim_cands:                        0
% 2.70/0.97  pred_elim:                              0
% 2.70/0.97  pred_elim_cl:                           0
% 2.70/0.97  pred_elim_cycles:                       0
% 2.70/0.97  merged_defs:                            0
% 2.70/0.97  merged_defs_ncl:                        0
% 2.70/0.97  bin_hyper_res:                          0
% 2.70/0.97  prep_cycles:                            2
% 2.70/0.97  pred_elim_time:                         0.
% 2.70/0.97  splitting_time:                         0.
% 2.70/0.97  sem_filter_time:                        0.
% 2.70/0.97  monotx_time:                            0.
% 2.70/0.97  subtype_inf_time:                       0.
% 2.70/0.97  
% 2.70/0.97  ------ Problem properties
% 2.70/0.97  
% 2.70/0.97  clauses:                                8
% 2.70/0.97  conjectures:                            1
% 2.70/0.97  epr:                                    0
% 2.70/0.97  horn:                                   8
% 2.70/0.97  ground:                                 1
% 2.70/0.97  unary:                                  8
% 2.70/0.97  binary:                                 0
% 2.70/0.97  lits:                                   8
% 2.70/0.97  lits_eq:                                8
% 2.70/0.97  fd_pure:                                0
% 2.70/0.97  fd_pseudo:                              0
% 2.70/0.97  fd_cond:                                0
% 2.70/0.97  fd_pseudo_cond:                         0
% 2.70/0.97  ac_symbols:                             1
% 2.70/0.97  
% 2.70/0.97  ------ Propositional Solver
% 2.70/0.97  
% 2.70/0.97  prop_solver_calls:                      13
% 2.70/0.97  prop_fast_solver_calls:                 56
% 2.70/0.97  smt_solver_calls:                       0
% 2.70/0.97  smt_fast_solver_calls:                  0
% 2.70/0.97  prop_num_of_clauses:                    110
% 2.70/0.97  prop_preprocess_simplified:             301
% 2.70/0.97  prop_fo_subsumed:                       0
% 2.70/0.97  prop_solver_time:                       0.
% 2.70/0.97  smt_solver_time:                        0.
% 2.70/0.97  smt_fast_solver_time:                   0.
% 2.70/0.97  prop_fast_solver_time:                  0.
% 2.70/0.97  prop_unsat_core_time:                   0.
% 2.70/0.97  
% 2.70/0.97  ------ QBF
% 2.70/0.97  
% 2.70/0.97  qbf_q_res:                              0
% 2.70/0.97  qbf_num_tautologies:                    0
% 2.70/0.97  qbf_prep_cycles:                        0
% 2.70/0.97  
% 2.70/0.97  ------ BMC1
% 2.70/0.97  
% 2.70/0.97  bmc1_current_bound:                     -1
% 2.70/0.97  bmc1_last_solved_bound:                 -1
% 2.70/0.97  bmc1_unsat_core_size:                   -1
% 2.70/0.97  bmc1_unsat_core_parents_size:           -1
% 2.70/0.97  bmc1_merge_next_fun:                    0
% 2.70/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.70/0.97  
% 2.70/0.97  ------ Instantiation
% 2.70/0.97  
% 2.70/0.97  inst_num_of_clauses:                    0
% 2.70/0.97  inst_num_in_passive:                    0
% 2.70/0.97  inst_num_in_active:                     0
% 2.70/0.97  inst_num_in_unprocessed:                0
% 2.70/0.97  inst_num_of_loops:                      0
% 2.70/0.97  inst_num_of_learning_restarts:          0
% 2.70/0.97  inst_num_moves_active_passive:          0
% 2.70/0.97  inst_lit_activity:                      0
% 2.70/0.97  inst_lit_activity_moves:                0
% 2.70/0.97  inst_num_tautologies:                   0
% 2.70/0.97  inst_num_prop_implied:                  0
% 2.70/0.97  inst_num_existing_simplified:           0
% 2.70/0.97  inst_num_eq_res_simplified:             0
% 2.70/0.97  inst_num_child_elim:                    0
% 2.70/0.97  inst_num_of_dismatching_blockings:      0
% 2.70/0.97  inst_num_of_non_proper_insts:           0
% 2.70/0.97  inst_num_of_duplicates:                 0
% 2.70/0.97  inst_inst_num_from_inst_to_res:         0
% 2.70/0.97  inst_dismatching_checking_time:         0.
% 2.70/0.97  
% 2.70/0.97  ------ Resolution
% 2.70/0.97  
% 2.70/0.97  res_num_of_clauses:                     0
% 2.70/0.97  res_num_in_passive:                     0
% 2.70/0.97  res_num_in_active:                      0
% 2.70/0.97  res_num_of_loops:                       23
% 2.70/0.97  res_forward_subset_subsumed:            0
% 2.70/0.97  res_backward_subset_subsumed:           0
% 2.70/0.97  res_forward_subsumed:                   0
% 2.70/0.97  res_backward_subsumed:                  0
% 2.70/0.97  res_forward_subsumption_resolution:     0
% 2.70/0.97  res_backward_subsumption_resolution:    0
% 2.70/0.97  res_clause_to_clause_subsumption:       3891
% 2.70/0.97  res_orphan_elimination:                 0
% 2.70/0.97  res_tautology_del:                      0
% 2.70/0.97  res_num_eq_res_simplified:              0
% 2.70/0.97  res_num_sel_changes:                    0
% 2.70/0.97  res_moves_from_active_to_pass:          0
% 2.70/0.97  
% 2.70/0.97  ------ Superposition
% 2.70/0.97  
% 2.70/0.97  sup_time_total:                         0.
% 2.70/0.97  sup_time_generating:                    0.
% 2.70/0.97  sup_time_sim_full:                      0.
% 2.70/0.97  sup_time_sim_immed:                     0.
% 2.70/0.97  
% 2.70/0.97  sup_num_of_clauses:                     248
% 2.70/0.97  sup_num_in_active:                      41
% 2.70/0.97  sup_num_in_passive:                     207
% 2.70/0.97  sup_num_of_loops:                       63
% 2.70/0.97  sup_fw_superposition:                   1073
% 2.70/0.97  sup_bw_superposition:                   705
% 2.70/0.97  sup_immediate_simplified:               569
% 2.70/0.97  sup_given_eliminated:                   5
% 2.70/0.97  comparisons_done:                       0
% 2.70/0.97  comparisons_avoided:                    0
% 2.70/0.97  
% 2.70/0.97  ------ Simplifications
% 2.70/0.97  
% 2.70/0.97  
% 2.70/0.97  sim_fw_subset_subsumed:                 0
% 2.70/0.97  sim_bw_subset_subsumed:                 0
% 2.70/0.97  sim_fw_subsumed:                        55
% 2.70/0.97  sim_bw_subsumed:                        1
% 2.70/0.97  sim_fw_subsumption_res:                 0
% 2.70/0.97  sim_bw_subsumption_res:                 0
% 2.70/0.97  sim_tautology_del:                      0
% 2.70/0.97  sim_eq_tautology_del:                   186
% 2.70/0.97  sim_eq_res_simp:                        0
% 2.70/0.97  sim_fw_demodulated:                     266
% 2.70/0.97  sim_bw_demodulated:                     50
% 2.70/0.97  sim_light_normalised:                   305
% 2.70/0.97  sim_joinable_taut:                      26
% 2.70/0.97  sim_joinable_simp:                      1
% 2.70/0.97  sim_ac_normalised:                      0
% 2.70/0.97  sim_smt_subsumption:                    0
% 2.70/0.97  
%------------------------------------------------------------------------------
