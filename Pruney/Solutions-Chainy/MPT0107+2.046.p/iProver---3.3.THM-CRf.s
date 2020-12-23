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
% DateTime   : Thu Dec  3 11:25:26 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 710 expanded)
%              Number of clauses        :   40 ( 267 expanded)
%              Number of leaves         :   12 ( 187 expanded)
%              Depth                    :   17
%              Number of atoms          :   80 ( 844 expanded)
%              Number of equality atoms :   71 ( 691 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f25,f26,f23])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f18,f26])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f19,f23])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) ),
    inference(definition_unfolding,[],[f22,f26])).

fof(f11,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f12])).

fof(f15,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1)
   => k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f27,plain,(
    k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,sK1) ),
    inference(definition_unfolding,[],[f27,f23])).

cnf(c_7,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_6,plain,
    ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_53,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(theory_normalisation,[status(thm)],[c_7,c_6,c_0])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_3,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_42,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X3
    | k5_xboole_0(X3,k4_xboole_0(X1,X3)) = X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_43,plain,
    ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(unflattening,[status(thm)],[c_42])).

cnf(c_90,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_4,c_43])).

cnf(c_2,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_61,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2,c_4])).

cnf(c_99,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_90,c_61])).

cnf(c_63,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_179,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_99,c_63])).

cnf(c_193,plain,
    ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_6,c_179])).

cnf(c_337,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X1,X1)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_53,c_193])).

cnf(c_92,plain,
    ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[status(thm)],[c_61,c_43])).

cnf(c_98,plain,
    ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_92,c_4])).

cnf(c_5,plain,
    ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_71,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_5,c_4])).

cnf(c_72,plain,
    ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_71,c_4])).

cnf(c_95,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_43,c_72])).

cnf(c_257,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_95,c_53])).

cnf(c_276,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_257,c_4,c_61])).

cnf(c_277,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_276,c_98,c_99])).

cnf(c_395,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_337,c_98,c_99,c_277])).

cnf(c_8,negated_conjecture,
    ( k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1517,plain,
    ( k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))) != k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_395,c_8])).

cnf(c_64,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
    inference(superposition,[status(thm)],[c_6,c_0])).

cnf(c_410,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_277,c_64])).

cnf(c_429,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(demodulation,[status(thm)],[c_410,c_99])).

cnf(c_498,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_43,c_429])).

cnf(c_499,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[status(thm)],[c_53,c_429])).

cnf(c_541,plain,
    ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),X0)) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(demodulation,[status(thm)],[c_498,c_499])).

cnf(c_421,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_277,c_64])).

cnf(c_424,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(demodulation,[status(thm)],[c_421,c_99])).

cnf(c_542,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_541,c_424])).

cnf(c_1518,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_1517,c_542])).

cnf(c_1519,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_1518])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:14:22 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.86/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/0.98  
% 2.86/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.86/0.98  
% 2.86/0.98  ------  iProver source info
% 2.86/0.98  
% 2.86/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.86/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.86/0.98  git: non_committed_changes: false
% 2.86/0.98  git: last_make_outside_of_git: false
% 2.86/0.98  
% 2.86/0.98  ------ 
% 2.86/0.98  
% 2.86/0.98  ------ Input Options
% 2.86/0.98  
% 2.86/0.98  --out_options                           all
% 2.86/0.98  --tptp_safe_out                         true
% 2.86/0.98  --problem_path                          ""
% 2.86/0.98  --include_path                          ""
% 2.86/0.98  --clausifier                            res/vclausify_rel
% 2.86/0.98  --clausifier_options                    --mode clausify
% 2.86/0.98  --stdin                                 false
% 2.86/0.98  --stats_out                             all
% 2.86/0.98  
% 2.86/0.98  ------ General Options
% 2.86/0.98  
% 2.86/0.98  --fof                                   false
% 2.86/0.98  --time_out_real                         305.
% 2.86/0.98  --time_out_virtual                      -1.
% 2.86/0.98  --symbol_type_check                     false
% 2.86/0.98  --clausify_out                          false
% 2.86/0.98  --sig_cnt_out                           false
% 2.86/0.98  --trig_cnt_out                          false
% 2.86/0.98  --trig_cnt_out_tolerance                1.
% 2.86/0.98  --trig_cnt_out_sk_spl                   false
% 2.86/0.98  --abstr_cl_out                          false
% 2.86/0.98  
% 2.86/0.98  ------ Global Options
% 2.86/0.98  
% 2.86/0.98  --schedule                              default
% 2.86/0.98  --add_important_lit                     false
% 2.86/0.98  --prop_solver_per_cl                    1000
% 2.86/0.98  --min_unsat_core                        false
% 2.86/0.98  --soft_assumptions                      false
% 2.86/0.98  --soft_lemma_size                       3
% 2.86/0.98  --prop_impl_unit_size                   0
% 2.86/0.98  --prop_impl_unit                        []
% 2.86/0.98  --share_sel_clauses                     true
% 2.86/0.98  --reset_solvers                         false
% 2.86/0.98  --bc_imp_inh                            [conj_cone]
% 2.86/0.98  --conj_cone_tolerance                   3.
% 2.86/0.98  --extra_neg_conj                        none
% 2.86/0.98  --large_theory_mode                     true
% 2.86/0.98  --prolific_symb_bound                   200
% 2.86/0.98  --lt_threshold                          2000
% 2.86/0.98  --clause_weak_htbl                      true
% 2.86/0.98  --gc_record_bc_elim                     false
% 2.86/0.98  
% 2.86/0.98  ------ Preprocessing Options
% 2.86/0.98  
% 2.86/0.98  --preprocessing_flag                    true
% 2.86/0.98  --time_out_prep_mult                    0.1
% 2.86/0.98  --splitting_mode                        input
% 2.86/0.98  --splitting_grd                         true
% 2.86/0.98  --splitting_cvd                         false
% 2.86/0.98  --splitting_cvd_svl                     false
% 2.86/0.98  --splitting_nvd                         32
% 2.86/0.98  --sub_typing                            true
% 2.86/0.98  --prep_gs_sim                           true
% 2.86/0.98  --prep_unflatten                        true
% 2.86/0.98  --prep_res_sim                          true
% 2.86/0.98  --prep_upred                            true
% 2.86/0.98  --prep_sem_filter                       exhaustive
% 2.86/0.98  --prep_sem_filter_out                   false
% 2.86/0.98  --pred_elim                             true
% 2.86/0.98  --res_sim_input                         true
% 2.86/0.98  --eq_ax_congr_red                       true
% 2.86/0.98  --pure_diseq_elim                       true
% 2.86/0.98  --brand_transform                       false
% 2.86/0.98  --non_eq_to_eq                          false
% 2.86/0.98  --prep_def_merge                        true
% 2.86/0.98  --prep_def_merge_prop_impl              false
% 2.86/0.98  --prep_def_merge_mbd                    true
% 2.86/0.98  --prep_def_merge_tr_red                 false
% 2.86/0.98  --prep_def_merge_tr_cl                  false
% 2.86/0.98  --smt_preprocessing                     true
% 2.86/0.98  --smt_ac_axioms                         fast
% 2.86/0.98  --preprocessed_out                      false
% 2.86/0.98  --preprocessed_stats                    false
% 2.86/0.98  
% 2.86/0.98  ------ Abstraction refinement Options
% 2.86/0.98  
% 2.86/0.98  --abstr_ref                             []
% 2.86/0.98  --abstr_ref_prep                        false
% 2.86/0.98  --abstr_ref_until_sat                   false
% 2.86/0.98  --abstr_ref_sig_restrict                funpre
% 2.86/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.86/0.98  --abstr_ref_under                       []
% 2.86/0.98  
% 2.86/0.98  ------ SAT Options
% 2.86/0.98  
% 2.86/0.98  --sat_mode                              false
% 2.86/0.98  --sat_fm_restart_options                ""
% 2.86/0.98  --sat_gr_def                            false
% 2.86/0.98  --sat_epr_types                         true
% 2.86/0.98  --sat_non_cyclic_types                  false
% 2.86/0.98  --sat_finite_models                     false
% 2.86/0.98  --sat_fm_lemmas                         false
% 2.86/0.98  --sat_fm_prep                           false
% 2.86/0.98  --sat_fm_uc_incr                        true
% 2.86/0.98  --sat_out_model                         small
% 2.86/0.98  --sat_out_clauses                       false
% 2.86/0.98  
% 2.86/0.98  ------ QBF Options
% 2.86/0.98  
% 2.86/0.98  --qbf_mode                              false
% 2.86/0.98  --qbf_elim_univ                         false
% 2.86/0.98  --qbf_dom_inst                          none
% 2.86/0.98  --qbf_dom_pre_inst                      false
% 2.86/0.98  --qbf_sk_in                             false
% 2.86/0.98  --qbf_pred_elim                         true
% 2.86/0.98  --qbf_split                             512
% 2.86/0.98  
% 2.86/0.98  ------ BMC1 Options
% 2.86/0.98  
% 2.86/0.98  --bmc1_incremental                      false
% 2.86/0.98  --bmc1_axioms                           reachable_all
% 2.86/0.98  --bmc1_min_bound                        0
% 2.86/0.98  --bmc1_max_bound                        -1
% 2.86/0.98  --bmc1_max_bound_default                -1
% 2.86/0.98  --bmc1_symbol_reachability              true
% 2.86/0.98  --bmc1_property_lemmas                  false
% 2.86/0.98  --bmc1_k_induction                      false
% 2.86/0.98  --bmc1_non_equiv_states                 false
% 2.86/0.98  --bmc1_deadlock                         false
% 2.86/0.98  --bmc1_ucm                              false
% 2.86/0.98  --bmc1_add_unsat_core                   none
% 2.86/0.98  --bmc1_unsat_core_children              false
% 2.86/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.86/0.98  --bmc1_out_stat                         full
% 2.86/0.98  --bmc1_ground_init                      false
% 2.86/0.98  --bmc1_pre_inst_next_state              false
% 2.86/0.98  --bmc1_pre_inst_state                   false
% 2.86/0.98  --bmc1_pre_inst_reach_state             false
% 2.86/0.98  --bmc1_out_unsat_core                   false
% 2.86/0.98  --bmc1_aig_witness_out                  false
% 2.86/0.98  --bmc1_verbose                          false
% 2.86/0.98  --bmc1_dump_clauses_tptp                false
% 2.86/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.86/0.98  --bmc1_dump_file                        -
% 2.86/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.86/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.86/0.98  --bmc1_ucm_extend_mode                  1
% 2.86/0.98  --bmc1_ucm_init_mode                    2
% 2.86/0.98  --bmc1_ucm_cone_mode                    none
% 2.86/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.86/0.98  --bmc1_ucm_relax_model                  4
% 2.86/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.86/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.86/0.98  --bmc1_ucm_layered_model                none
% 2.86/0.98  --bmc1_ucm_max_lemma_size               10
% 2.86/0.98  
% 2.86/0.98  ------ AIG Options
% 2.86/0.98  
% 2.86/0.98  --aig_mode                              false
% 2.86/0.98  
% 2.86/0.98  ------ Instantiation Options
% 2.86/0.98  
% 2.86/0.98  --instantiation_flag                    true
% 2.86/0.98  --inst_sos_flag                         false
% 2.86/0.98  --inst_sos_phase                        true
% 2.86/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.86/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.86/0.98  --inst_lit_sel_side                     num_symb
% 2.86/0.98  --inst_solver_per_active                1400
% 2.86/0.98  --inst_solver_calls_frac                1.
% 2.86/0.98  --inst_passive_queue_type               priority_queues
% 2.86/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.86/0.98  --inst_passive_queues_freq              [25;2]
% 2.86/0.98  --inst_dismatching                      true
% 2.86/0.98  --inst_eager_unprocessed_to_passive     true
% 2.86/0.98  --inst_prop_sim_given                   true
% 2.86/0.98  --inst_prop_sim_new                     false
% 2.86/0.98  --inst_subs_new                         false
% 2.86/0.98  --inst_eq_res_simp                      false
% 2.86/0.98  --inst_subs_given                       false
% 2.86/0.98  --inst_orphan_elimination               true
% 2.86/0.98  --inst_learning_loop_flag               true
% 2.86/0.98  --inst_learning_start                   3000
% 2.86/0.98  --inst_learning_factor                  2
% 2.86/0.98  --inst_start_prop_sim_after_learn       3
% 2.86/0.98  --inst_sel_renew                        solver
% 2.86/0.98  --inst_lit_activity_flag                true
% 2.86/0.98  --inst_restr_to_given                   false
% 2.86/0.98  --inst_activity_threshold               500
% 2.86/0.98  --inst_out_proof                        true
% 2.86/0.98  
% 2.86/0.98  ------ Resolution Options
% 2.86/0.98  
% 2.86/0.98  --resolution_flag                       true
% 2.86/0.98  --res_lit_sel                           adaptive
% 2.86/0.98  --res_lit_sel_side                      none
% 2.86/0.98  --res_ordering                          kbo
% 2.86/0.98  --res_to_prop_solver                    active
% 2.86/0.98  --res_prop_simpl_new                    false
% 2.86/0.98  --res_prop_simpl_given                  true
% 2.86/0.98  --res_passive_queue_type                priority_queues
% 2.86/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.86/0.98  --res_passive_queues_freq               [15;5]
% 2.86/0.98  --res_forward_subs                      full
% 2.86/0.98  --res_backward_subs                     full
% 2.86/0.98  --res_forward_subs_resolution           true
% 2.86/0.98  --res_backward_subs_resolution          true
% 2.86/0.98  --res_orphan_elimination                true
% 2.86/0.98  --res_time_limit                        2.
% 2.86/0.98  --res_out_proof                         true
% 2.86/0.98  
% 2.86/0.98  ------ Superposition Options
% 2.86/0.98  
% 2.86/0.98  --superposition_flag                    true
% 2.86/0.98  --sup_passive_queue_type                priority_queues
% 2.86/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.86/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.86/0.98  --demod_completeness_check              fast
% 2.86/0.98  --demod_use_ground                      true
% 2.86/0.98  --sup_to_prop_solver                    passive
% 2.86/0.98  --sup_prop_simpl_new                    true
% 2.86/0.98  --sup_prop_simpl_given                  true
% 2.86/0.98  --sup_fun_splitting                     false
% 2.86/0.98  --sup_smt_interval                      50000
% 2.86/0.98  
% 2.86/0.98  ------ Superposition Simplification Setup
% 2.86/0.98  
% 2.86/0.98  --sup_indices_passive                   []
% 2.86/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.86/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.98  --sup_full_bw                           [BwDemod]
% 2.86/0.98  --sup_immed_triv                        [TrivRules]
% 2.86/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.86/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.98  --sup_immed_bw_main                     []
% 2.86/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.86/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.86/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.86/0.98  
% 2.86/0.98  ------ Combination Options
% 2.86/0.98  
% 2.86/0.98  --comb_res_mult                         3
% 2.86/0.98  --comb_sup_mult                         2
% 2.86/0.98  --comb_inst_mult                        10
% 2.86/0.98  
% 2.86/0.98  ------ Debug Options
% 2.86/0.98  
% 2.86/0.98  --dbg_backtrace                         false
% 2.86/0.98  --dbg_dump_prop_clauses                 false
% 2.86/0.98  --dbg_dump_prop_clauses_file            -
% 2.86/0.98  --dbg_out_stat                          false
% 2.86/0.98  ------ Parsing...
% 2.86/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.86/0.98  
% 2.86/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.86/0.98  
% 2.86/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.86/0.98  
% 2.86/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.86/0.98  ------ Proving...
% 2.86/0.98  ------ Problem Properties 
% 2.86/0.98  
% 2.86/0.98  
% 2.86/0.98  clauses                                 8
% 2.86/0.98  conjectures                             1
% 2.86/0.98  EPR                                     0
% 2.86/0.98  Horn                                    8
% 2.86/0.98  unary                                   8
% 2.86/0.98  binary                                  0
% 2.86/0.98  lits                                    8
% 2.86/0.98  lits eq                                 8
% 2.86/0.98  fd_pure                                 0
% 2.86/0.98  fd_pseudo                               0
% 2.86/0.98  fd_cond                                 0
% 2.86/0.98  fd_pseudo_cond                          0
% 2.86/0.98  AC symbols                              1
% 2.86/0.98  
% 2.86/0.98  ------ Schedule UEQ
% 2.86/0.98  
% 2.86/0.98  ------ pure equality problem: resolution off 
% 2.86/0.98  
% 2.86/0.98  ------ Option_UEQ Time Limit: Unbounded
% 2.86/0.98  
% 2.86/0.98  
% 2.86/0.98  ------ 
% 2.86/0.98  Current options:
% 2.86/0.98  ------ 
% 2.86/0.98  
% 2.86/0.98  ------ Input Options
% 2.86/0.98  
% 2.86/0.98  --out_options                           all
% 2.86/0.98  --tptp_safe_out                         true
% 2.86/0.98  --problem_path                          ""
% 2.86/0.98  --include_path                          ""
% 2.86/0.98  --clausifier                            res/vclausify_rel
% 2.86/0.98  --clausifier_options                    --mode clausify
% 2.86/0.98  --stdin                                 false
% 2.86/0.98  --stats_out                             all
% 2.86/0.98  
% 2.86/0.98  ------ General Options
% 2.86/0.98  
% 2.86/0.98  --fof                                   false
% 2.86/0.98  --time_out_real                         305.
% 2.86/0.98  --time_out_virtual                      -1.
% 2.86/0.98  --symbol_type_check                     false
% 2.86/0.98  --clausify_out                          false
% 2.86/0.98  --sig_cnt_out                           false
% 2.86/0.98  --trig_cnt_out                          false
% 2.86/0.98  --trig_cnt_out_tolerance                1.
% 2.86/0.98  --trig_cnt_out_sk_spl                   false
% 2.86/0.98  --abstr_cl_out                          false
% 2.86/0.98  
% 2.86/0.98  ------ Global Options
% 2.86/0.98  
% 2.86/0.98  --schedule                              default
% 2.86/0.98  --add_important_lit                     false
% 2.86/0.98  --prop_solver_per_cl                    1000
% 2.86/0.98  --min_unsat_core                        false
% 2.86/0.98  --soft_assumptions                      false
% 2.86/0.98  --soft_lemma_size                       3
% 2.86/0.98  --prop_impl_unit_size                   0
% 2.86/0.98  --prop_impl_unit                        []
% 2.86/0.98  --share_sel_clauses                     true
% 2.86/0.98  --reset_solvers                         false
% 2.86/0.98  --bc_imp_inh                            [conj_cone]
% 2.86/0.98  --conj_cone_tolerance                   3.
% 2.86/0.98  --extra_neg_conj                        none
% 2.86/0.98  --large_theory_mode                     true
% 2.86/0.98  --prolific_symb_bound                   200
% 2.86/0.98  --lt_threshold                          2000
% 2.86/0.98  --clause_weak_htbl                      true
% 2.86/0.98  --gc_record_bc_elim                     false
% 2.86/0.98  
% 2.86/0.98  ------ Preprocessing Options
% 2.86/0.98  
% 2.86/0.98  --preprocessing_flag                    true
% 2.86/0.98  --time_out_prep_mult                    0.1
% 2.86/0.98  --splitting_mode                        input
% 2.86/0.98  --splitting_grd                         true
% 2.86/0.98  --splitting_cvd                         false
% 2.86/0.98  --splitting_cvd_svl                     false
% 2.86/0.98  --splitting_nvd                         32
% 2.86/0.98  --sub_typing                            true
% 2.86/0.98  --prep_gs_sim                           true
% 2.86/0.98  --prep_unflatten                        true
% 2.86/0.98  --prep_res_sim                          true
% 2.86/0.98  --prep_upred                            true
% 2.86/0.98  --prep_sem_filter                       exhaustive
% 2.86/0.98  --prep_sem_filter_out                   false
% 2.86/0.98  --pred_elim                             true
% 2.86/0.98  --res_sim_input                         true
% 2.86/0.98  --eq_ax_congr_red                       true
% 2.86/0.98  --pure_diseq_elim                       true
% 2.86/0.98  --brand_transform                       false
% 2.86/0.98  --non_eq_to_eq                          false
% 2.86/0.98  --prep_def_merge                        true
% 2.86/0.98  --prep_def_merge_prop_impl              false
% 2.86/0.98  --prep_def_merge_mbd                    true
% 2.86/0.98  --prep_def_merge_tr_red                 false
% 2.86/0.98  --prep_def_merge_tr_cl                  false
% 2.86/0.98  --smt_preprocessing                     true
% 2.86/0.98  --smt_ac_axioms                         fast
% 2.86/0.98  --preprocessed_out                      false
% 2.86/0.98  --preprocessed_stats                    false
% 2.86/0.98  
% 2.86/0.98  ------ Abstraction refinement Options
% 2.86/0.98  
% 2.86/0.98  --abstr_ref                             []
% 2.86/0.98  --abstr_ref_prep                        false
% 2.86/0.98  --abstr_ref_until_sat                   false
% 2.86/0.98  --abstr_ref_sig_restrict                funpre
% 2.86/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.86/0.98  --abstr_ref_under                       []
% 2.86/0.98  
% 2.86/0.98  ------ SAT Options
% 2.86/0.98  
% 2.86/0.98  --sat_mode                              false
% 2.86/0.98  --sat_fm_restart_options                ""
% 2.86/0.98  --sat_gr_def                            false
% 2.86/0.98  --sat_epr_types                         true
% 2.86/0.98  --sat_non_cyclic_types                  false
% 2.86/0.98  --sat_finite_models                     false
% 2.86/0.98  --sat_fm_lemmas                         false
% 2.86/0.98  --sat_fm_prep                           false
% 2.86/0.98  --sat_fm_uc_incr                        true
% 2.86/0.98  --sat_out_model                         small
% 2.86/0.98  --sat_out_clauses                       false
% 2.86/0.98  
% 2.86/0.98  ------ QBF Options
% 2.86/0.98  
% 2.86/0.98  --qbf_mode                              false
% 2.86/0.98  --qbf_elim_univ                         false
% 2.86/0.98  --qbf_dom_inst                          none
% 2.86/0.98  --qbf_dom_pre_inst                      false
% 2.86/0.98  --qbf_sk_in                             false
% 2.86/0.98  --qbf_pred_elim                         true
% 2.86/0.98  --qbf_split                             512
% 2.86/0.98  
% 2.86/0.98  ------ BMC1 Options
% 2.86/0.98  
% 2.86/0.98  --bmc1_incremental                      false
% 2.86/0.98  --bmc1_axioms                           reachable_all
% 2.86/0.98  --bmc1_min_bound                        0
% 2.86/0.98  --bmc1_max_bound                        -1
% 2.86/0.98  --bmc1_max_bound_default                -1
% 2.86/0.98  --bmc1_symbol_reachability              true
% 2.86/0.98  --bmc1_property_lemmas                  false
% 2.86/0.98  --bmc1_k_induction                      false
% 2.86/0.98  --bmc1_non_equiv_states                 false
% 2.86/0.98  --bmc1_deadlock                         false
% 2.86/0.98  --bmc1_ucm                              false
% 2.86/0.98  --bmc1_add_unsat_core                   none
% 2.86/0.98  --bmc1_unsat_core_children              false
% 2.86/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.86/0.98  --bmc1_out_stat                         full
% 2.86/0.98  --bmc1_ground_init                      false
% 2.86/0.98  --bmc1_pre_inst_next_state              false
% 2.86/0.98  --bmc1_pre_inst_state                   false
% 2.86/0.98  --bmc1_pre_inst_reach_state             false
% 2.86/0.98  --bmc1_out_unsat_core                   false
% 2.86/0.98  --bmc1_aig_witness_out                  false
% 2.86/0.98  --bmc1_verbose                          false
% 2.86/0.98  --bmc1_dump_clauses_tptp                false
% 2.86/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.86/0.98  --bmc1_dump_file                        -
% 2.86/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.86/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.86/0.98  --bmc1_ucm_extend_mode                  1
% 2.86/0.98  --bmc1_ucm_init_mode                    2
% 2.86/0.98  --bmc1_ucm_cone_mode                    none
% 2.86/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.86/0.98  --bmc1_ucm_relax_model                  4
% 2.86/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.86/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.86/0.98  --bmc1_ucm_layered_model                none
% 2.86/0.98  --bmc1_ucm_max_lemma_size               10
% 2.86/0.98  
% 2.86/0.98  ------ AIG Options
% 2.86/0.98  
% 2.86/0.98  --aig_mode                              false
% 2.86/0.98  
% 2.86/0.98  ------ Instantiation Options
% 2.86/0.98  
% 2.86/0.98  --instantiation_flag                    false
% 2.86/0.98  --inst_sos_flag                         false
% 2.86/0.98  --inst_sos_phase                        true
% 2.86/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.86/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.86/0.98  --inst_lit_sel_side                     num_symb
% 2.86/0.98  --inst_solver_per_active                1400
% 2.86/0.98  --inst_solver_calls_frac                1.
% 2.86/0.98  --inst_passive_queue_type               priority_queues
% 2.86/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.86/0.98  --inst_passive_queues_freq              [25;2]
% 2.86/0.98  --inst_dismatching                      true
% 2.86/0.98  --inst_eager_unprocessed_to_passive     true
% 2.86/0.98  --inst_prop_sim_given                   true
% 2.86/0.98  --inst_prop_sim_new                     false
% 2.86/0.98  --inst_subs_new                         false
% 2.86/0.98  --inst_eq_res_simp                      false
% 2.86/0.98  --inst_subs_given                       false
% 2.86/0.98  --inst_orphan_elimination               true
% 2.86/0.98  --inst_learning_loop_flag               true
% 2.86/0.98  --inst_learning_start                   3000
% 2.86/0.98  --inst_learning_factor                  2
% 2.86/0.98  --inst_start_prop_sim_after_learn       3
% 2.86/0.98  --inst_sel_renew                        solver
% 2.86/0.98  --inst_lit_activity_flag                true
% 2.86/0.98  --inst_restr_to_given                   false
% 2.86/0.98  --inst_activity_threshold               500
% 2.86/0.98  --inst_out_proof                        true
% 2.86/0.98  
% 2.86/0.98  ------ Resolution Options
% 2.86/0.98  
% 2.86/0.98  --resolution_flag                       false
% 2.86/0.98  --res_lit_sel                           adaptive
% 2.86/0.98  --res_lit_sel_side                      none
% 2.86/0.98  --res_ordering                          kbo
% 2.86/0.98  --res_to_prop_solver                    active
% 2.86/0.98  --res_prop_simpl_new                    false
% 2.86/0.98  --res_prop_simpl_given                  true
% 2.86/0.98  --res_passive_queue_type                priority_queues
% 2.86/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.86/0.98  --res_passive_queues_freq               [15;5]
% 2.86/0.98  --res_forward_subs                      full
% 2.86/0.98  --res_backward_subs                     full
% 2.86/0.98  --res_forward_subs_resolution           true
% 2.86/0.98  --res_backward_subs_resolution          true
% 2.86/0.98  --res_orphan_elimination                true
% 2.86/0.98  --res_time_limit                        2.
% 2.86/0.98  --res_out_proof                         true
% 2.86/0.98  
% 2.86/0.98  ------ Superposition Options
% 2.86/0.98  
% 2.86/0.98  --superposition_flag                    true
% 2.86/0.98  --sup_passive_queue_type                priority_queues
% 2.86/0.98  --sup_passive_queues                    [[-conj_dist;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.86/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.86/0.98  --demod_completeness_check              fast
% 2.86/0.98  --demod_use_ground                      true
% 2.86/0.98  --sup_to_prop_solver                    active
% 2.86/0.98  --sup_prop_simpl_new                    false
% 2.86/0.98  --sup_prop_simpl_given                  false
% 2.86/0.98  --sup_fun_splitting                     true
% 2.86/0.98  --sup_smt_interval                      10000
% 2.86/0.98  
% 2.86/0.98  ------ Superposition Simplification Setup
% 2.86/0.98  
% 2.86/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.86/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.86/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.86/0.98  --sup_full_triv                         [TrivRules]
% 2.86/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.86/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.86/0.98  --sup_immed_triv                        [TrivRules]
% 2.86/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.86/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.86/0.98  --sup_immed_bw_main                     []
% 2.86/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.86/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.86/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.86/0.98  --sup_input_bw                          [BwDemod;BwSubsumption]
% 2.86/0.98  
% 2.86/0.98  ------ Combination Options
% 2.86/0.98  
% 2.86/0.98  --comb_res_mult                         1
% 2.86/0.98  --comb_sup_mult                         1
% 2.86/0.98  --comb_inst_mult                        1000000
% 2.86/0.98  
% 2.86/0.98  ------ Debug Options
% 2.86/0.98  
% 2.86/0.98  --dbg_backtrace                         false
% 2.86/0.98  --dbg_dump_prop_clauses                 false
% 2.86/0.98  --dbg_dump_prop_clauses_file            -
% 2.86/0.98  --dbg_out_stat                          false
% 2.86/0.98  
% 2.86/0.98  
% 2.86/0.98  
% 2.86/0.98  
% 2.86/0.98  ------ Proving...
% 2.86/0.98  
% 2.86/0.98  
% 2.86/0.98  % SZS status Theorem for theBenchmark.p
% 2.86/0.98  
% 2.86/0.98   Resolution empty clause
% 2.86/0.98  
% 2.86/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.86/0.98  
% 2.86/0.98  fof(f9,axiom,(
% 2.86/0.98    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.98  
% 2.86/0.98  fof(f25,plain,(
% 2.86/0.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.86/0.98    inference(cnf_transformation,[],[f9])).
% 2.86/0.98  
% 2.86/0.98  fof(f10,axiom,(
% 2.86/0.98    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.98  
% 2.86/0.98  fof(f26,plain,(
% 2.86/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.86/0.98    inference(cnf_transformation,[],[f10])).
% 2.86/0.98  
% 2.86/0.98  fof(f7,axiom,(
% 2.86/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.98  
% 2.86/0.98  fof(f23,plain,(
% 2.86/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.86/0.98    inference(cnf_transformation,[],[f7])).
% 2.86/0.98  
% 2.86/0.98  fof(f31,plain,(
% 2.86/0.98    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.86/0.98    inference(definition_unfolding,[],[f25,f26,f23])).
% 2.86/0.98  
% 2.86/0.98  fof(f8,axiom,(
% 2.86/0.98    ! [X0,X1,X2] : k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)),
% 2.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.98  
% 2.86/0.98  fof(f24,plain,(
% 2.86/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(k5_xboole_0(X0,X1),X2)) )),
% 2.86/0.98    inference(cnf_transformation,[],[f8])).
% 2.86/0.98  
% 2.86/0.98  fof(f1,axiom,(
% 2.86/0.98    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.98  
% 2.86/0.98  fof(f17,plain,(
% 2.86/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.86/0.98    inference(cnf_transformation,[],[f1])).
% 2.86/0.98  
% 2.86/0.98  fof(f5,axiom,(
% 2.86/0.98    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.98  
% 2.86/0.98  fof(f21,plain,(
% 2.86/0.98    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.86/0.98    inference(cnf_transformation,[],[f5])).
% 2.86/0.98  
% 2.86/0.98  fof(f2,axiom,(
% 2.86/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.98  
% 2.86/0.98  fof(f13,plain,(
% 2.86/0.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.86/0.98    inference(ennf_transformation,[],[f2])).
% 2.86/0.98  
% 2.86/0.98  fof(f18,plain,(
% 2.86/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.86/0.98    inference(cnf_transformation,[],[f13])).
% 2.86/0.98  
% 2.86/0.98  fof(f28,plain,(
% 2.86/0.98    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 2.86/0.98    inference(definition_unfolding,[],[f18,f26])).
% 2.86/0.98  
% 2.86/0.98  fof(f4,axiom,(
% 2.86/0.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.98  
% 2.86/0.98  fof(f20,plain,(
% 2.86/0.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.86/0.98    inference(cnf_transformation,[],[f4])).
% 2.86/0.98  
% 2.86/0.98  fof(f3,axiom,(
% 2.86/0.98    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.98  
% 2.86/0.98  fof(f19,plain,(
% 2.86/0.98    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.86/0.98    inference(cnf_transformation,[],[f3])).
% 2.86/0.98  
% 2.86/0.98  fof(f29,plain,(
% 2.86/0.98    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.86/0.98    inference(definition_unfolding,[],[f19,f23])).
% 2.86/0.98  
% 2.86/0.98  fof(f6,axiom,(
% 2.86/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.98  
% 2.86/0.98  fof(f22,plain,(
% 2.86/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.86/0.98    inference(cnf_transformation,[],[f6])).
% 2.86/0.98  
% 2.86/0.98  fof(f30,plain,(
% 2.86/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1)) )),
% 2.86/0.98    inference(definition_unfolding,[],[f22,f26])).
% 2.86/0.98  
% 2.86/0.98  fof(f11,conjecture,(
% 2.86/0.98    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.86/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.86/0.98  
% 2.86/0.98  fof(f12,negated_conjecture,(
% 2.86/0.98    ~! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 2.86/0.98    inference(negated_conjecture,[],[f11])).
% 2.86/0.98  
% 2.86/0.98  fof(f14,plain,(
% 2.86/0.98    ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1)),
% 2.86/0.98    inference(ennf_transformation,[],[f12])).
% 2.86/0.98  
% 2.86/0.98  fof(f15,plain,(
% 2.86/0.98    ? [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) != k4_xboole_0(X0,X1) => k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1)),
% 2.86/0.98    introduced(choice_axiom,[])).
% 2.86/0.98  
% 2.86/0.98  fof(f16,plain,(
% 2.86/0.98    k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1)),
% 2.86/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 2.86/0.98  
% 2.86/0.98  fof(f27,plain,(
% 2.86/0.98    k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(sK0,sK1)),
% 2.86/0.98    inference(cnf_transformation,[],[f16])).
% 2.86/0.98  
% 2.86/0.98  fof(f32,plain,(
% 2.86/0.98    k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,sK1)),
% 2.86/0.98    inference(definition_unfolding,[],[f27,f23])).
% 2.86/0.98  
% 2.86/0.98  cnf(c_7,plain,
% 2.86/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 2.86/0.98      inference(cnf_transformation,[],[f31]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_6,plain,
% 2.86/0.98      ( k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
% 2.86/0.98      inference(cnf_transformation,[],[f24]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_0,plain,
% 2.86/0.98      ( k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
% 2.86/0.98      inference(cnf_transformation,[],[f17]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_53,plain,
% 2.86/0.98      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0)))) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
% 2.86/0.98      inference(theory_normalisation,[status(thm)],[c_7,c_6,c_0]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_4,plain,
% 2.86/0.98      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.86/0.98      inference(cnf_transformation,[],[f21]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_1,plain,
% 2.86/0.98      ( ~ r1_tarski(X0,X1) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
% 2.86/0.98      inference(cnf_transformation,[],[f28]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_3,plain,
% 2.86/0.98      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 2.86/0.98      inference(cnf_transformation,[],[f20]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_42,plain,
% 2.86/0.98      ( X0 != X1
% 2.86/0.98      | k4_xboole_0(X0,X2) != X3
% 2.86/0.98      | k5_xboole_0(X3,k4_xboole_0(X1,X3)) = X1 ),
% 2.86/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_3]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_43,plain,
% 2.86/0.98      ( k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 2.86/0.98      inference(unflattening,[status(thm)],[c_42]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_90,plain,
% 2.86/0.98      ( k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
% 2.86/0.98      inference(superposition,[status(thm)],[c_4,c_43]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_2,plain,
% 2.86/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.86/0.98      inference(cnf_transformation,[],[f29]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_61,plain,
% 2.86/0.98      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.86/0.98      inference(light_normalisation,[status(thm)],[c_2,c_4]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_99,plain,
% 2.86/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.86/0.98      inference(light_normalisation,[status(thm)],[c_90,c_61]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_63,plain,
% 2.86/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X2,k5_xboole_0(X1,X0)) ),
% 2.86/0.98      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_179,plain,
% 2.86/0.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,X0) ),
% 2.86/0.98      inference(superposition,[status(thm)],[c_99,c_63]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_193,plain,
% 2.86/0.98      ( k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k5_xboole_0(X1,X2))) = k5_xboole_0(X2,k5_xboole_0(X0,X1)) ),
% 2.86/0.98      inference(superposition,[status(thm)],[c_6,c_179]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_337,plain,
% 2.86/0.98      ( k5_xboole_0(k5_xboole_0(X0,k4_xboole_0(X0,X1)),k5_xboole_0(X1,X1)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 2.86/0.98      inference(superposition,[status(thm)],[c_53,c_193]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_92,plain,
% 2.86/0.98      ( k5_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
% 2.86/0.98      inference(superposition,[status(thm)],[c_61,c_43]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_98,plain,
% 2.86/0.98      ( k5_xboole_0(k1_xboole_0,X0) = X0 ),
% 2.86/0.98      inference(light_normalisation,[status(thm)],[c_92,c_4]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_5,plain,
% 2.86/0.98      ( k4_xboole_0(k5_xboole_0(X0,k4_xboole_0(X1,X0)),X1) = k4_xboole_0(X0,X1) ),
% 2.86/0.98      inference(cnf_transformation,[],[f30]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_71,plain,
% 2.86/0.98      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = k4_xboole_0(X0,k1_xboole_0) ),
% 2.86/0.98      inference(superposition,[status(thm)],[c_5,c_4]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_72,plain,
% 2.86/0.98      ( k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
% 2.86/0.98      inference(light_normalisation,[status(thm)],[c_71,c_4]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_95,plain,
% 2.86/0.98      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.86/0.98      inference(superposition,[status(thm)],[c_43,c_72]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_257,plain,
% 2.86/0.98      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 2.86/0.98      inference(superposition,[status(thm)],[c_95,c_53]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_276,plain,
% 2.86/0.98      ( k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0))) = k1_xboole_0 ),
% 2.86/0.98      inference(light_normalisation,[status(thm)],[c_257,c_4,c_61]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_277,plain,
% 2.86/0.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.86/0.98      inference(demodulation,[status(thm)],[c_276,c_98,c_99]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_395,plain,
% 2.86/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 2.86/0.98      inference(demodulation,[status(thm)],[c_337,c_98,c_99,c_277]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_8,negated_conjecture,
% 2.86/0.98      ( k5_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k4_xboole_0(sK0,sK1) ),
% 2.86/0.98      inference(cnf_transformation,[],[f32]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_1517,plain,
% 2.86/0.98      ( k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))) != k4_xboole_0(sK0,sK1) ),
% 2.86/0.98      inference(demodulation,[status(thm)],[c_395,c_8]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_64,plain,
% 2.86/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X2)) = k5_xboole_0(X1,k5_xboole_0(X2,X0)) ),
% 2.86/0.98      inference(superposition,[status(thm)],[c_6,c_0]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_410,plain,
% 2.86/0.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(X1,k1_xboole_0) ),
% 2.86/0.98      inference(superposition,[status(thm)],[c_277,c_64]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_429,plain,
% 2.86/0.98      ( k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
% 2.86/0.98      inference(demodulation,[status(thm)],[c_410,c_99]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_498,plain,
% 2.86/0.98      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k5_xboole_0(k4_xboole_0(X0,X1),X0) ),
% 2.86/0.98      inference(superposition,[status(thm)],[c_43,c_429]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_499,plain,
% 2.86/0.98      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 2.86/0.98      inference(superposition,[status(thm)],[c_53,c_429]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_541,plain,
% 2.86/0.98      ( k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,X1),X0)) = k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) ),
% 2.86/0.98      inference(demodulation,[status(thm)],[c_498,c_499]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_421,plain,
% 2.86/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = k5_xboole_0(X1,k1_xboole_0) ),
% 2.86/0.98      inference(superposition,[status(thm)],[c_277,c_64]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_424,plain,
% 2.86/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
% 2.86/0.98      inference(demodulation,[status(thm)],[c_421,c_99]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_542,plain,
% 2.86/0.98      ( k5_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 2.86/0.98      inference(demodulation,[status(thm)],[c_541,c_424]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_1518,plain,
% 2.86/0.98      ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
% 2.86/0.98      inference(demodulation,[status(thm)],[c_1517,c_542]) ).
% 2.86/0.98  
% 2.86/0.98  cnf(c_1519,plain,
% 2.86/0.98      ( $false ),
% 2.86/0.98      inference(equality_resolution_simp,[status(thm)],[c_1518]) ).
% 2.86/0.98  
% 2.86/0.98  
% 2.86/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.86/0.98  
% 2.86/0.98  ------                               Statistics
% 2.86/0.98  
% 2.86/0.98  ------ General
% 2.86/0.98  
% 2.86/0.98  abstr_ref_over_cycles:                  0
% 2.86/0.98  abstr_ref_under_cycles:                 0
% 2.86/0.98  gc_basic_clause_elim:                   0
% 2.86/0.98  forced_gc_time:                         0
% 2.86/0.98  parsing_time:                           0.008
% 2.86/0.98  unif_index_cands_time:                  0.
% 2.86/0.98  unif_index_add_time:                    0.
% 2.86/0.98  orderings_time:                         0.
% 2.86/0.98  out_proof_time:                         0.009
% 2.86/0.98  total_time:                             0.075
% 2.86/0.98  num_of_symbols:                         37
% 2.86/0.98  num_of_terms:                           2473
% 2.86/0.98  
% 2.86/0.98  ------ Preprocessing
% 2.86/0.98  
% 2.86/0.98  num_of_splits:                          0
% 2.86/0.98  num_of_split_atoms:                     0
% 2.86/0.98  num_of_reused_defs:                     0
% 2.86/0.98  num_eq_ax_congr_red:                    1
% 2.86/0.98  num_of_sem_filtered_clauses:            0
% 2.86/0.98  num_of_subtypes:                        0
% 2.86/0.98  monotx_restored_types:                  0
% 2.86/0.98  sat_num_of_epr_types:                   0
% 2.86/0.98  sat_num_of_non_cyclic_types:            0
% 2.86/0.98  sat_guarded_non_collapsed_types:        0
% 2.86/0.98  num_pure_diseq_elim:                    0
% 2.86/0.98  simp_replaced_by:                       0
% 2.86/0.98  res_preprocessed:                       29
% 2.86/0.98  prep_upred:                             0
% 2.86/0.98  prep_unflattend:                        2
% 2.86/0.98  smt_new_axioms:                         0
% 2.86/0.98  pred_elim_cands:                        0
% 2.86/0.98  pred_elim:                              1
% 2.86/0.98  pred_elim_cl:                           1
% 2.86/0.98  pred_elim_cycles:                       2
% 2.86/0.98  merged_defs:                            0
% 2.86/0.98  merged_defs_ncl:                        0
% 2.86/0.98  bin_hyper_res:                          0
% 2.86/0.98  prep_cycles:                            3
% 2.86/0.98  pred_elim_time:                         0.
% 2.86/0.98  splitting_time:                         0.
% 2.86/0.98  sem_filter_time:                        0.
% 2.86/0.98  monotx_time:                            0.
% 2.86/0.98  subtype_inf_time:                       0.
% 2.86/0.98  
% 2.86/0.98  ------ Problem properties
% 2.86/0.98  
% 2.86/0.98  clauses:                                8
% 2.86/0.98  conjectures:                            1
% 2.86/0.98  epr:                                    0
% 2.86/0.98  horn:                                   8
% 2.86/0.98  ground:                                 1
% 2.86/0.98  unary:                                  8
% 2.86/0.98  binary:                                 0
% 2.86/0.98  lits:                                   8
% 2.86/0.98  lits_eq:                                8
% 2.86/0.98  fd_pure:                                0
% 2.86/0.98  fd_pseudo:                              0
% 2.86/0.98  fd_cond:                                0
% 2.86/0.98  fd_pseudo_cond:                         0
% 2.86/0.98  ac_symbols:                             1
% 2.86/0.98  
% 2.86/0.98  ------ Propositional Solver
% 2.86/0.98  
% 2.86/0.98  prop_solver_calls:                      17
% 2.86/0.98  prop_fast_solver_calls:                 73
% 2.86/0.98  smt_solver_calls:                       0
% 2.86/0.98  smt_fast_solver_calls:                  0
% 2.86/0.98  prop_num_of_clauses:                    77
% 2.86/0.98  prop_preprocess_simplified:             416
% 2.86/0.98  prop_fo_subsumed:                       0
% 2.86/0.98  prop_solver_time:                       0.
% 2.86/0.98  smt_solver_time:                        0.
% 2.86/0.98  smt_fast_solver_time:                   0.
% 2.86/0.98  prop_fast_solver_time:                  0.
% 2.86/0.98  prop_unsat_core_time:                   0.
% 2.86/0.98  
% 2.86/0.98  ------ QBF
% 2.86/0.98  
% 2.86/0.98  qbf_q_res:                              0
% 2.86/0.98  qbf_num_tautologies:                    0
% 2.86/0.98  qbf_prep_cycles:                        0
% 2.86/0.98  
% 2.86/0.98  ------ BMC1
% 2.86/0.98  
% 2.86/0.98  bmc1_current_bound:                     -1
% 2.86/0.98  bmc1_last_solved_bound:                 -1
% 2.86/0.98  bmc1_unsat_core_size:                   -1
% 2.86/0.98  bmc1_unsat_core_parents_size:           -1
% 2.86/0.98  bmc1_merge_next_fun:                    0
% 2.86/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.86/0.98  
% 2.86/0.98  ------ Instantiation
% 2.86/0.98  
% 2.86/0.98  inst_num_of_clauses:                    0
% 2.86/0.98  inst_num_in_passive:                    0
% 2.86/0.98  inst_num_in_active:                     0
% 2.86/0.98  inst_num_in_unprocessed:                0
% 2.86/0.98  inst_num_of_loops:                      0
% 2.86/0.98  inst_num_of_learning_restarts:          0
% 2.86/0.98  inst_num_moves_active_passive:          0
% 2.86/0.98  inst_lit_activity:                      0
% 2.86/0.98  inst_lit_activity_moves:                0
% 2.86/0.98  inst_num_tautologies:                   0
% 2.86/0.98  inst_num_prop_implied:                  0
% 2.86/0.98  inst_num_existing_simplified:           0
% 2.86/0.98  inst_num_eq_res_simplified:             0
% 2.86/0.98  inst_num_child_elim:                    0
% 2.86/0.98  inst_num_of_dismatching_blockings:      0
% 2.86/0.98  inst_num_of_non_proper_insts:           0
% 2.86/0.98  inst_num_of_duplicates:                 0
% 2.86/0.98  inst_inst_num_from_inst_to_res:         0
% 2.86/0.98  inst_dismatching_checking_time:         0.
% 2.86/0.98  
% 2.86/0.98  ------ Resolution
% 2.86/0.98  
% 2.86/0.98  res_num_of_clauses:                     0
% 2.86/0.98  res_num_in_passive:                     0
% 2.86/0.98  res_num_in_active:                      0
% 2.86/0.98  res_num_of_loops:                       32
% 2.86/0.98  res_forward_subset_subsumed:            0
% 2.86/0.98  res_backward_subset_subsumed:           0
% 2.86/0.98  res_forward_subsumed:                   0
% 2.86/0.98  res_backward_subsumed:                  0
% 2.86/0.98  res_forward_subsumption_resolution:     0
% 2.86/0.98  res_backward_subsumption_resolution:    0
% 2.86/0.98  res_clause_to_clause_subsumption:       2550
% 2.86/0.98  res_orphan_elimination:                 0
% 2.86/0.98  res_tautology_del:                      0
% 2.86/0.98  res_num_eq_res_simplified:              0
% 2.86/0.98  res_num_sel_changes:                    0
% 2.86/0.98  res_moves_from_active_to_pass:          0
% 2.86/0.98  
% 2.86/0.98  ------ Superposition
% 2.86/0.98  
% 2.86/0.98  sup_time_total:                         0.
% 2.86/0.98  sup_time_generating:                    0.
% 2.86/0.98  sup_time_sim_full:                      0.
% 2.86/0.98  sup_time_sim_immed:                     0.
% 2.86/0.98  
% 2.86/0.98  sup_num_of_clauses:                     173
% 2.86/0.98  sup_num_in_active:                      29
% 2.86/0.98  sup_num_in_passive:                     144
% 2.86/0.98  sup_num_of_loops:                       33
% 2.86/0.98  sup_fw_superposition:                   616
% 2.86/0.98  sup_bw_superposition:                   382
% 2.86/0.98  sup_immediate_simplified:               393
% 2.86/0.98  sup_given_eliminated:                   0
% 2.86/0.98  comparisons_done:                       0
% 2.86/0.98  comparisons_avoided:                    0
% 2.86/0.98  
% 2.86/0.98  ------ Simplifications
% 2.86/0.98  
% 2.86/0.98  
% 2.86/0.98  sim_fw_subset_subsumed:                 0
% 2.86/0.98  sim_bw_subset_subsumed:                 0
% 2.86/0.98  sim_fw_subsumed:                        45
% 2.86/0.98  sim_bw_subsumed:                        3
% 2.86/0.98  sim_fw_subsumption_res:                 0
% 2.86/0.98  sim_bw_subsumption_res:                 0
% 2.86/0.98  sim_tautology_del:                      0
% 2.86/0.98  sim_eq_tautology_del:                   120
% 2.86/0.98  sim_eq_res_simp:                        0
% 2.86/0.98  sim_fw_demodulated:                     223
% 2.86/0.98  sim_bw_demodulated:                     12
% 2.86/0.98  sim_light_normalised:                   157
% 2.86/0.98  sim_joinable_taut:                      24
% 2.86/0.98  sim_joinable_simp:                      0
% 2.86/0.98  sim_ac_normalised:                      0
% 2.86/0.98  sim_smt_subsumption:                    0
% 2.86/0.98  
%------------------------------------------------------------------------------
