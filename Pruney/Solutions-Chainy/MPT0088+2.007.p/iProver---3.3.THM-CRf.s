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
% DateTime   : Thu Dec  3 11:24:33 EST 2020

% Result     : Theorem 6.52s
% Output     : CNFRefutation 6.52s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 111 expanded)
%              Number of clauses        :   32 (  41 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   15
%              Number of atoms          :   87 ( 145 expanded)
%              Number of equality atoms :   59 ( 102 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f17,f24])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
        & r1_xboole_0(X0,k4_xboole_0(X1,X2)) )
   => ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
      & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f26,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f24])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f25,f24,f24])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f19,f24])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f18,f24])).

fof(f27,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_44,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_10,negated_conjecture,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_85,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | k4_xboole_0(sK1,sK2) != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_44,c_10])).

cnf(c_86,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_85])).

cnf(c_7,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_329,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_86,c_7])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_357,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_329,c_5])).

cnf(c_8,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_132,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(demodulation,[status(thm)],[c_8,c_6])).

cnf(c_797,plain,
    ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(sK1,sK2))) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
    inference(superposition,[status(thm)],[c_357,c_132])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_113,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3,c_5])).

cnf(c_304,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_113])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_306,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_304,c_4])).

cnf(c_1187,plain,
    ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_797,c_306])).

cnf(c_1189,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1187,c_6])).

cnf(c_11906,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1189])).

cnf(c_303,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_6,c_4])).

cnf(c_12485,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,sK0))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11906,c_303])).

cnf(c_1,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_42,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_9,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_80,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | k4_xboole_0(sK0,sK2) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_9])).

cnf(c_81,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_80])).

cnf(c_134,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK0),sK2)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_132,c_81])).

cnf(c_203,plain,
    ( k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,sK0))) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_0,c_134])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12485,c_203])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:17:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.52/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.52/1.49  
% 6.52/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.52/1.49  
% 6.52/1.49  ------  iProver source info
% 6.52/1.49  
% 6.52/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.52/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.52/1.49  git: non_committed_changes: false
% 6.52/1.49  git: last_make_outside_of_git: false
% 6.52/1.49  
% 6.52/1.49  ------ 
% 6.52/1.49  
% 6.52/1.49  ------ Input Options
% 6.52/1.49  
% 6.52/1.49  --out_options                           all
% 6.52/1.49  --tptp_safe_out                         true
% 6.52/1.49  --problem_path                          ""
% 6.52/1.49  --include_path                          ""
% 6.52/1.49  --clausifier                            res/vclausify_rel
% 6.52/1.49  --clausifier_options                    --mode clausify
% 6.52/1.49  --stdin                                 false
% 6.52/1.49  --stats_out                             all
% 6.52/1.49  
% 6.52/1.49  ------ General Options
% 6.52/1.49  
% 6.52/1.49  --fof                                   false
% 6.52/1.49  --time_out_real                         305.
% 6.52/1.49  --time_out_virtual                      -1.
% 6.52/1.49  --symbol_type_check                     false
% 6.52/1.49  --clausify_out                          false
% 6.52/1.49  --sig_cnt_out                           false
% 6.52/1.49  --trig_cnt_out                          false
% 6.52/1.49  --trig_cnt_out_tolerance                1.
% 6.52/1.49  --trig_cnt_out_sk_spl                   false
% 6.52/1.49  --abstr_cl_out                          false
% 6.52/1.49  
% 6.52/1.49  ------ Global Options
% 6.52/1.49  
% 6.52/1.49  --schedule                              default
% 6.52/1.49  --add_important_lit                     false
% 6.52/1.49  --prop_solver_per_cl                    1000
% 6.52/1.49  --min_unsat_core                        false
% 6.52/1.49  --soft_assumptions                      false
% 6.52/1.49  --soft_lemma_size                       3
% 6.52/1.49  --prop_impl_unit_size                   0
% 6.52/1.49  --prop_impl_unit                        []
% 6.52/1.49  --share_sel_clauses                     true
% 6.52/1.49  --reset_solvers                         false
% 6.52/1.49  --bc_imp_inh                            [conj_cone]
% 6.52/1.49  --conj_cone_tolerance                   3.
% 6.52/1.49  --extra_neg_conj                        none
% 6.52/1.49  --large_theory_mode                     true
% 6.52/1.49  --prolific_symb_bound                   200
% 6.52/1.49  --lt_threshold                          2000
% 6.52/1.49  --clause_weak_htbl                      true
% 6.52/1.49  --gc_record_bc_elim                     false
% 6.52/1.49  
% 6.52/1.49  ------ Preprocessing Options
% 6.52/1.49  
% 6.52/1.49  --preprocessing_flag                    true
% 6.52/1.49  --time_out_prep_mult                    0.1
% 6.52/1.49  --splitting_mode                        input
% 6.52/1.49  --splitting_grd                         true
% 6.52/1.49  --splitting_cvd                         false
% 6.52/1.49  --splitting_cvd_svl                     false
% 6.52/1.49  --splitting_nvd                         32
% 6.52/1.49  --sub_typing                            true
% 6.52/1.49  --prep_gs_sim                           true
% 6.52/1.49  --prep_unflatten                        true
% 6.52/1.49  --prep_res_sim                          true
% 6.52/1.49  --prep_upred                            true
% 6.52/1.49  --prep_sem_filter                       exhaustive
% 6.52/1.49  --prep_sem_filter_out                   false
% 6.52/1.49  --pred_elim                             true
% 6.52/1.49  --res_sim_input                         true
% 6.52/1.49  --eq_ax_congr_red                       true
% 6.52/1.49  --pure_diseq_elim                       true
% 6.52/1.49  --brand_transform                       false
% 6.52/1.49  --non_eq_to_eq                          false
% 6.52/1.49  --prep_def_merge                        true
% 6.52/1.49  --prep_def_merge_prop_impl              false
% 6.52/1.49  --prep_def_merge_mbd                    true
% 6.52/1.49  --prep_def_merge_tr_red                 false
% 6.52/1.49  --prep_def_merge_tr_cl                  false
% 6.52/1.49  --smt_preprocessing                     true
% 6.52/1.49  --smt_ac_axioms                         fast
% 6.52/1.49  --preprocessed_out                      false
% 6.52/1.49  --preprocessed_stats                    false
% 6.52/1.49  
% 6.52/1.49  ------ Abstraction refinement Options
% 6.52/1.49  
% 6.52/1.49  --abstr_ref                             []
% 6.52/1.49  --abstr_ref_prep                        false
% 6.52/1.49  --abstr_ref_until_sat                   false
% 6.52/1.49  --abstr_ref_sig_restrict                funpre
% 6.52/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.52/1.49  --abstr_ref_under                       []
% 6.52/1.49  
% 6.52/1.49  ------ SAT Options
% 6.52/1.49  
% 6.52/1.49  --sat_mode                              false
% 6.52/1.49  --sat_fm_restart_options                ""
% 6.52/1.49  --sat_gr_def                            false
% 6.52/1.49  --sat_epr_types                         true
% 6.52/1.49  --sat_non_cyclic_types                  false
% 6.52/1.49  --sat_finite_models                     false
% 6.52/1.49  --sat_fm_lemmas                         false
% 6.52/1.49  --sat_fm_prep                           false
% 6.52/1.49  --sat_fm_uc_incr                        true
% 6.52/1.49  --sat_out_model                         small
% 6.52/1.49  --sat_out_clauses                       false
% 6.52/1.49  
% 6.52/1.49  ------ QBF Options
% 6.52/1.49  
% 6.52/1.49  --qbf_mode                              false
% 6.52/1.49  --qbf_elim_univ                         false
% 6.52/1.49  --qbf_dom_inst                          none
% 6.52/1.49  --qbf_dom_pre_inst                      false
% 6.52/1.49  --qbf_sk_in                             false
% 6.52/1.49  --qbf_pred_elim                         true
% 6.52/1.49  --qbf_split                             512
% 6.52/1.49  
% 6.52/1.49  ------ BMC1 Options
% 6.52/1.49  
% 6.52/1.49  --bmc1_incremental                      false
% 6.52/1.49  --bmc1_axioms                           reachable_all
% 6.52/1.49  --bmc1_min_bound                        0
% 6.52/1.49  --bmc1_max_bound                        -1
% 6.52/1.49  --bmc1_max_bound_default                -1
% 6.52/1.49  --bmc1_symbol_reachability              true
% 6.52/1.49  --bmc1_property_lemmas                  false
% 6.52/1.49  --bmc1_k_induction                      false
% 6.52/1.49  --bmc1_non_equiv_states                 false
% 6.52/1.49  --bmc1_deadlock                         false
% 6.52/1.49  --bmc1_ucm                              false
% 6.52/1.49  --bmc1_add_unsat_core                   none
% 6.52/1.49  --bmc1_unsat_core_children              false
% 6.52/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.52/1.49  --bmc1_out_stat                         full
% 6.52/1.49  --bmc1_ground_init                      false
% 6.52/1.49  --bmc1_pre_inst_next_state              false
% 6.52/1.49  --bmc1_pre_inst_state                   false
% 6.52/1.49  --bmc1_pre_inst_reach_state             false
% 6.52/1.49  --bmc1_out_unsat_core                   false
% 6.52/1.49  --bmc1_aig_witness_out                  false
% 6.52/1.49  --bmc1_verbose                          false
% 6.52/1.49  --bmc1_dump_clauses_tptp                false
% 6.52/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.52/1.49  --bmc1_dump_file                        -
% 6.52/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.52/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.52/1.49  --bmc1_ucm_extend_mode                  1
% 6.52/1.49  --bmc1_ucm_init_mode                    2
% 6.52/1.49  --bmc1_ucm_cone_mode                    none
% 6.52/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.52/1.49  --bmc1_ucm_relax_model                  4
% 6.52/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.52/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.52/1.49  --bmc1_ucm_layered_model                none
% 6.52/1.49  --bmc1_ucm_max_lemma_size               10
% 6.52/1.49  
% 6.52/1.49  ------ AIG Options
% 6.52/1.49  
% 6.52/1.49  --aig_mode                              false
% 6.52/1.49  
% 6.52/1.49  ------ Instantiation Options
% 6.52/1.49  
% 6.52/1.49  --instantiation_flag                    true
% 6.52/1.49  --inst_sos_flag                         false
% 6.52/1.49  --inst_sos_phase                        true
% 6.52/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.52/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.52/1.49  --inst_lit_sel_side                     num_symb
% 6.52/1.49  --inst_solver_per_active                1400
% 6.52/1.49  --inst_solver_calls_frac                1.
% 6.52/1.49  --inst_passive_queue_type               priority_queues
% 6.52/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.52/1.49  --inst_passive_queues_freq              [25;2]
% 6.52/1.49  --inst_dismatching                      true
% 6.52/1.49  --inst_eager_unprocessed_to_passive     true
% 6.52/1.49  --inst_prop_sim_given                   true
% 6.52/1.49  --inst_prop_sim_new                     false
% 6.52/1.49  --inst_subs_new                         false
% 6.52/1.49  --inst_eq_res_simp                      false
% 6.52/1.49  --inst_subs_given                       false
% 6.52/1.49  --inst_orphan_elimination               true
% 6.52/1.49  --inst_learning_loop_flag               true
% 6.52/1.49  --inst_learning_start                   3000
% 6.52/1.49  --inst_learning_factor                  2
% 6.52/1.49  --inst_start_prop_sim_after_learn       3
% 6.52/1.49  --inst_sel_renew                        solver
% 6.52/1.49  --inst_lit_activity_flag                true
% 6.52/1.49  --inst_restr_to_given                   false
% 6.52/1.49  --inst_activity_threshold               500
% 6.52/1.49  --inst_out_proof                        true
% 6.52/1.49  
% 6.52/1.49  ------ Resolution Options
% 6.52/1.49  
% 6.52/1.49  --resolution_flag                       true
% 6.52/1.49  --res_lit_sel                           adaptive
% 6.52/1.49  --res_lit_sel_side                      none
% 6.52/1.49  --res_ordering                          kbo
% 6.52/1.49  --res_to_prop_solver                    active
% 6.52/1.49  --res_prop_simpl_new                    false
% 6.52/1.49  --res_prop_simpl_given                  true
% 6.52/1.49  --res_passive_queue_type                priority_queues
% 6.52/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.52/1.49  --res_passive_queues_freq               [15;5]
% 6.52/1.49  --res_forward_subs                      full
% 6.52/1.49  --res_backward_subs                     full
% 6.52/1.49  --res_forward_subs_resolution           true
% 6.52/1.49  --res_backward_subs_resolution          true
% 6.52/1.49  --res_orphan_elimination                true
% 6.52/1.49  --res_time_limit                        2.
% 6.52/1.49  --res_out_proof                         true
% 6.52/1.49  
% 6.52/1.49  ------ Superposition Options
% 6.52/1.49  
% 6.52/1.49  --superposition_flag                    true
% 6.52/1.49  --sup_passive_queue_type                priority_queues
% 6.52/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.52/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.52/1.49  --demod_completeness_check              fast
% 6.52/1.49  --demod_use_ground                      true
% 6.52/1.49  --sup_to_prop_solver                    passive
% 6.52/1.49  --sup_prop_simpl_new                    true
% 6.52/1.49  --sup_prop_simpl_given                  true
% 6.52/1.49  --sup_fun_splitting                     false
% 6.52/1.49  --sup_smt_interval                      50000
% 6.52/1.49  
% 6.52/1.49  ------ Superposition Simplification Setup
% 6.52/1.49  
% 6.52/1.49  --sup_indices_passive                   []
% 6.52/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.52/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.52/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.52/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.52/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.52/1.49  --sup_full_bw                           [BwDemod]
% 6.52/1.49  --sup_immed_triv                        [TrivRules]
% 6.52/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.52/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.52/1.49  --sup_immed_bw_main                     []
% 6.52/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.52/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.52/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.52/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.52/1.49  
% 6.52/1.49  ------ Combination Options
% 6.52/1.49  
% 6.52/1.49  --comb_res_mult                         3
% 6.52/1.49  --comb_sup_mult                         2
% 6.52/1.49  --comb_inst_mult                        10
% 6.52/1.49  
% 6.52/1.49  ------ Debug Options
% 6.52/1.49  
% 6.52/1.49  --dbg_backtrace                         false
% 6.52/1.49  --dbg_dump_prop_clauses                 false
% 6.52/1.49  --dbg_dump_prop_clauses_file            -
% 6.52/1.49  --dbg_out_stat                          false
% 6.52/1.49  ------ Parsing...
% 6.52/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.52/1.49  
% 6.52/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 6.52/1.49  
% 6.52/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.52/1.49  
% 6.52/1.49  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 6.52/1.49  ------ Proving...
% 6.52/1.49  ------ Problem Properties 
% 6.52/1.49  
% 6.52/1.49  
% 6.52/1.49  clauses                                 10
% 6.52/1.49  conjectures                             0
% 6.52/1.49  EPR                                     0
% 6.52/1.49  Horn                                    10
% 6.52/1.49  unary                                   9
% 6.52/1.49  binary                                  1
% 6.52/1.49  lits                                    11
% 6.52/1.49  lits eq                                 11
% 6.52/1.49  fd_pure                                 0
% 6.52/1.49  fd_pseudo                               0
% 6.52/1.49  fd_cond                                 0
% 6.52/1.49  fd_pseudo_cond                          0
% 6.52/1.49  AC symbols                              0
% 6.52/1.49  
% 6.52/1.49  ------ Schedule dynamic 5 is on 
% 6.52/1.49  
% 6.52/1.49  ------ no conjectures: strip conj schedule 
% 6.52/1.49  
% 6.52/1.49  ------ pure equality problem: resolution off 
% 6.52/1.49  
% 6.52/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" stripped conjectures Time Limit: 10.
% 6.52/1.49  
% 6.52/1.49  
% 6.52/1.49  ------ 
% 6.52/1.49  Current options:
% 6.52/1.49  ------ 
% 6.52/1.49  
% 6.52/1.49  ------ Input Options
% 6.52/1.49  
% 6.52/1.49  --out_options                           all
% 6.52/1.49  --tptp_safe_out                         true
% 6.52/1.49  --problem_path                          ""
% 6.52/1.49  --include_path                          ""
% 6.52/1.49  --clausifier                            res/vclausify_rel
% 6.52/1.49  --clausifier_options                    --mode clausify
% 6.52/1.49  --stdin                                 false
% 6.52/1.49  --stats_out                             all
% 6.52/1.49  
% 6.52/1.49  ------ General Options
% 6.52/1.49  
% 6.52/1.49  --fof                                   false
% 6.52/1.49  --time_out_real                         305.
% 6.52/1.49  --time_out_virtual                      -1.
% 6.52/1.49  --symbol_type_check                     false
% 6.52/1.49  --clausify_out                          false
% 6.52/1.49  --sig_cnt_out                           false
% 6.52/1.49  --trig_cnt_out                          false
% 6.52/1.49  --trig_cnt_out_tolerance                1.
% 6.52/1.49  --trig_cnt_out_sk_spl                   false
% 6.52/1.49  --abstr_cl_out                          false
% 6.52/1.49  
% 6.52/1.49  ------ Global Options
% 6.52/1.49  
% 6.52/1.49  --schedule                              default
% 6.52/1.49  --add_important_lit                     false
% 6.52/1.49  --prop_solver_per_cl                    1000
% 6.52/1.49  --min_unsat_core                        false
% 6.52/1.49  --soft_assumptions                      false
% 6.52/1.49  --soft_lemma_size                       3
% 6.52/1.49  --prop_impl_unit_size                   0
% 6.52/1.49  --prop_impl_unit                        []
% 6.52/1.49  --share_sel_clauses                     true
% 6.52/1.49  --reset_solvers                         false
% 6.52/1.49  --bc_imp_inh                            [conj_cone]
% 6.52/1.49  --conj_cone_tolerance                   3.
% 6.52/1.49  --extra_neg_conj                        none
% 6.52/1.49  --large_theory_mode                     true
% 6.52/1.49  --prolific_symb_bound                   200
% 6.52/1.49  --lt_threshold                          2000
% 6.52/1.49  --clause_weak_htbl                      true
% 6.52/1.49  --gc_record_bc_elim                     false
% 6.52/1.49  
% 6.52/1.49  ------ Preprocessing Options
% 6.52/1.49  
% 6.52/1.49  --preprocessing_flag                    true
% 6.52/1.49  --time_out_prep_mult                    0.1
% 6.52/1.49  --splitting_mode                        input
% 6.52/1.49  --splitting_grd                         true
% 6.52/1.49  --splitting_cvd                         false
% 6.52/1.49  --splitting_cvd_svl                     false
% 6.52/1.49  --splitting_nvd                         32
% 6.52/1.49  --sub_typing                            true
% 6.52/1.49  --prep_gs_sim                           true
% 6.52/1.49  --prep_unflatten                        true
% 6.52/1.49  --prep_res_sim                          true
% 6.52/1.49  --prep_upred                            true
% 6.52/1.49  --prep_sem_filter                       exhaustive
% 6.52/1.49  --prep_sem_filter_out                   false
% 6.52/1.49  --pred_elim                             true
% 6.52/1.49  --res_sim_input                         true
% 6.52/1.49  --eq_ax_congr_red                       true
% 6.52/1.49  --pure_diseq_elim                       true
% 6.52/1.49  --brand_transform                       false
% 6.52/1.49  --non_eq_to_eq                          false
% 6.52/1.49  --prep_def_merge                        true
% 6.52/1.49  --prep_def_merge_prop_impl              false
% 6.52/1.49  --prep_def_merge_mbd                    true
% 6.52/1.49  --prep_def_merge_tr_red                 false
% 6.52/1.49  --prep_def_merge_tr_cl                  false
% 6.52/1.49  --smt_preprocessing                     true
% 6.52/1.49  --smt_ac_axioms                         fast
% 6.52/1.49  --preprocessed_out                      false
% 6.52/1.49  --preprocessed_stats                    false
% 6.52/1.49  
% 6.52/1.49  ------ Abstraction refinement Options
% 6.52/1.49  
% 6.52/1.49  --abstr_ref                             []
% 6.52/1.49  --abstr_ref_prep                        false
% 6.52/1.49  --abstr_ref_until_sat                   false
% 6.52/1.49  --abstr_ref_sig_restrict                funpre
% 6.52/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.52/1.49  --abstr_ref_under                       []
% 6.52/1.49  
% 6.52/1.49  ------ SAT Options
% 6.52/1.49  
% 6.52/1.49  --sat_mode                              false
% 6.52/1.49  --sat_fm_restart_options                ""
% 6.52/1.49  --sat_gr_def                            false
% 6.52/1.49  --sat_epr_types                         true
% 6.52/1.49  --sat_non_cyclic_types                  false
% 6.52/1.49  --sat_finite_models                     false
% 6.52/1.49  --sat_fm_lemmas                         false
% 6.52/1.49  --sat_fm_prep                           false
% 6.52/1.49  --sat_fm_uc_incr                        true
% 6.52/1.49  --sat_out_model                         small
% 6.52/1.49  --sat_out_clauses                       false
% 6.52/1.49  
% 6.52/1.49  ------ QBF Options
% 6.52/1.49  
% 6.52/1.49  --qbf_mode                              false
% 6.52/1.49  --qbf_elim_univ                         false
% 6.52/1.49  --qbf_dom_inst                          none
% 6.52/1.49  --qbf_dom_pre_inst                      false
% 6.52/1.49  --qbf_sk_in                             false
% 6.52/1.49  --qbf_pred_elim                         true
% 6.52/1.49  --qbf_split                             512
% 6.52/1.49  
% 6.52/1.49  ------ BMC1 Options
% 6.52/1.49  
% 6.52/1.49  --bmc1_incremental                      false
% 6.52/1.49  --bmc1_axioms                           reachable_all
% 6.52/1.49  --bmc1_min_bound                        0
% 6.52/1.49  --bmc1_max_bound                        -1
% 6.52/1.49  --bmc1_max_bound_default                -1
% 6.52/1.49  --bmc1_symbol_reachability              true
% 6.52/1.49  --bmc1_property_lemmas                  false
% 6.52/1.49  --bmc1_k_induction                      false
% 6.52/1.49  --bmc1_non_equiv_states                 false
% 6.52/1.49  --bmc1_deadlock                         false
% 6.52/1.49  --bmc1_ucm                              false
% 6.52/1.49  --bmc1_add_unsat_core                   none
% 6.52/1.49  --bmc1_unsat_core_children              false
% 6.52/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.52/1.49  --bmc1_out_stat                         full
% 6.52/1.49  --bmc1_ground_init                      false
% 6.52/1.49  --bmc1_pre_inst_next_state              false
% 6.52/1.49  --bmc1_pre_inst_state                   false
% 6.52/1.49  --bmc1_pre_inst_reach_state             false
% 6.52/1.49  --bmc1_out_unsat_core                   false
% 6.52/1.49  --bmc1_aig_witness_out                  false
% 6.52/1.49  --bmc1_verbose                          false
% 6.52/1.49  --bmc1_dump_clauses_tptp                false
% 6.52/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.52/1.49  --bmc1_dump_file                        -
% 6.52/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.52/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.52/1.49  --bmc1_ucm_extend_mode                  1
% 6.52/1.49  --bmc1_ucm_init_mode                    2
% 6.52/1.49  --bmc1_ucm_cone_mode                    none
% 6.52/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.52/1.49  --bmc1_ucm_relax_model                  4
% 6.52/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.52/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.52/1.49  --bmc1_ucm_layered_model                none
% 6.52/1.49  --bmc1_ucm_max_lemma_size               10
% 6.52/1.49  
% 6.52/1.49  ------ AIG Options
% 6.52/1.49  
% 6.52/1.49  --aig_mode                              false
% 6.52/1.49  
% 6.52/1.49  ------ Instantiation Options
% 6.52/1.49  
% 6.52/1.49  --instantiation_flag                    true
% 6.52/1.49  --inst_sos_flag                         false
% 6.52/1.49  --inst_sos_phase                        true
% 6.52/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.52/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.52/1.49  --inst_lit_sel_side                     none
% 6.52/1.49  --inst_solver_per_active                1400
% 6.52/1.49  --inst_solver_calls_frac                1.
% 6.52/1.49  --inst_passive_queue_type               priority_queues
% 6.52/1.49  --inst_passive_queues                   [[-num_var];[+age;-num_symb]]
% 6.52/1.49  --inst_passive_queues_freq              [25;2]
% 6.52/1.49  --inst_dismatching                      true
% 6.52/1.49  --inst_eager_unprocessed_to_passive     true
% 6.52/1.49  --inst_prop_sim_given                   true
% 6.52/1.49  --inst_prop_sim_new                     false
% 6.52/1.49  --inst_subs_new                         false
% 6.52/1.49  --inst_eq_res_simp                      false
% 6.52/1.49  --inst_subs_given                       false
% 6.52/1.49  --inst_orphan_elimination               true
% 6.52/1.49  --inst_learning_loop_flag               true
% 6.52/1.49  --inst_learning_start                   3000
% 6.52/1.49  --inst_learning_factor                  2
% 6.52/1.49  --inst_start_prop_sim_after_learn       3
% 6.52/1.49  --inst_sel_renew                        solver
% 6.52/1.49  --inst_lit_activity_flag                true
% 6.52/1.49  --inst_restr_to_given                   false
% 6.52/1.49  --inst_activity_threshold               500
% 6.52/1.49  --inst_out_proof                        true
% 6.52/1.49  
% 6.52/1.49  ------ Resolution Options
% 6.52/1.49  
% 6.52/1.49  --resolution_flag                       false
% 6.52/1.49  --res_lit_sel                           adaptive
% 6.52/1.49  --res_lit_sel_side                      none
% 6.52/1.49  --res_ordering                          kbo
% 6.52/1.49  --res_to_prop_solver                    active
% 6.52/1.49  --res_prop_simpl_new                    false
% 6.52/1.49  --res_prop_simpl_given                  true
% 6.52/1.49  --res_passive_queue_type                priority_queues
% 6.52/1.49  --res_passive_queues                    [[-num_symb];[+age;-num_symb]]
% 6.52/1.49  --res_passive_queues_freq               [15;5]
% 6.52/1.49  --res_forward_subs                      full
% 6.52/1.49  --res_backward_subs                     full
% 6.52/1.49  --res_forward_subs_resolution           true
% 6.52/1.49  --res_backward_subs_resolution          true
% 6.52/1.49  --res_orphan_elimination                true
% 6.52/1.49  --res_time_limit                        2.
% 6.52/1.49  --res_out_proof                         true
% 6.52/1.49  
% 6.52/1.49  ------ Superposition Options
% 6.52/1.49  
% 6.52/1.49  --superposition_flag                    true
% 6.52/1.49  --sup_passive_queue_type                priority_queues
% 6.52/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.52/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.52/1.49  --demod_completeness_check              fast
% 6.52/1.49  --demod_use_ground                      true
% 6.52/1.49  --sup_to_prop_solver                    passive
% 6.52/1.49  --sup_prop_simpl_new                    true
% 6.52/1.49  --sup_prop_simpl_given                  true
% 6.52/1.49  --sup_fun_splitting                     false
% 6.52/1.49  --sup_smt_interval                      50000
% 6.52/1.49  
% 6.52/1.49  ------ Superposition Simplification Setup
% 6.52/1.49  
% 6.52/1.49  --sup_indices_passive                   []
% 6.52/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.52/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.52/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.52/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.52/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.52/1.49  --sup_full_bw                           [BwDemod]
% 6.52/1.49  --sup_immed_triv                        [TrivRules]
% 6.52/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.52/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.52/1.49  --sup_immed_bw_main                     []
% 6.52/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.52/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.52/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.52/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.52/1.49  
% 6.52/1.49  ------ Combination Options
% 6.52/1.49  
% 6.52/1.49  --comb_res_mult                         3
% 6.52/1.49  --comb_sup_mult                         2
% 6.52/1.49  --comb_inst_mult                        10
% 6.52/1.49  
% 6.52/1.49  ------ Debug Options
% 6.52/1.49  
% 6.52/1.49  --dbg_backtrace                         false
% 6.52/1.49  --dbg_dump_prop_clauses                 false
% 6.52/1.49  --dbg_dump_prop_clauses_file            -
% 6.52/1.49  --dbg_out_stat                          false
% 6.52/1.49  
% 6.52/1.49  
% 6.52/1.49  
% 6.52/1.49  
% 6.52/1.49  ------ Proving...
% 6.52/1.49  
% 6.52/1.49  
% 6.52/1.49  % SZS status Theorem for theBenchmark.p
% 6.52/1.49  
% 6.52/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.52/1.49  
% 6.52/1.49  fof(f1,axiom,(
% 6.52/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 6.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.52/1.49  
% 6.52/1.49  fof(f16,plain,(
% 6.52/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 6.52/1.49    inference(cnf_transformation,[],[f1])).
% 6.52/1.49  
% 6.52/1.49  fof(f2,axiom,(
% 6.52/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 6.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.52/1.49  
% 6.52/1.49  fof(f13,plain,(
% 6.52/1.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 6.52/1.49    inference(nnf_transformation,[],[f2])).
% 6.52/1.49  
% 6.52/1.49  fof(f17,plain,(
% 6.52/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 6.52/1.49    inference(cnf_transformation,[],[f13])).
% 6.52/1.49  
% 6.52/1.49  fof(f8,axiom,(
% 6.52/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.52/1.49  
% 6.52/1.49  fof(f24,plain,(
% 6.52/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.52/1.49    inference(cnf_transformation,[],[f8])).
% 6.52/1.49  
% 6.52/1.49  fof(f29,plain,(
% 6.52/1.49    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 6.52/1.49    inference(definition_unfolding,[],[f17,f24])).
% 6.52/1.49  
% 6.52/1.49  fof(f10,conjecture,(
% 6.52/1.49    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 6.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.52/1.49  
% 6.52/1.49  fof(f11,negated_conjecture,(
% 6.52/1.49    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 6.52/1.49    inference(negated_conjecture,[],[f10])).
% 6.52/1.49  
% 6.52/1.49  fof(f12,plain,(
% 6.52/1.49    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 6.52/1.49    inference(ennf_transformation,[],[f11])).
% 6.52/1.49  
% 6.52/1.49  fof(f14,plain,(
% 6.52/1.49    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 6.52/1.49    introduced(choice_axiom,[])).
% 6.52/1.49  
% 6.52/1.49  fof(f15,plain,(
% 6.52/1.49    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 6.52/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 6.52/1.49  
% 6.52/1.49  fof(f26,plain,(
% 6.52/1.49    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 6.52/1.49    inference(cnf_transformation,[],[f15])).
% 6.52/1.49  
% 6.52/1.49  fof(f7,axiom,(
% 6.52/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.52/1.49  
% 6.52/1.49  fof(f23,plain,(
% 6.52/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.52/1.49    inference(cnf_transformation,[],[f7])).
% 6.52/1.49  
% 6.52/1.49  fof(f31,plain,(
% 6.52/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 6.52/1.49    inference(definition_unfolding,[],[f23,f24])).
% 6.52/1.49  
% 6.52/1.49  fof(f5,axiom,(
% 6.52/1.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 6.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.52/1.49  
% 6.52/1.49  fof(f21,plain,(
% 6.52/1.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.52/1.49    inference(cnf_transformation,[],[f5])).
% 6.52/1.49  
% 6.52/1.49  fof(f9,axiom,(
% 6.52/1.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 6.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.52/1.49  
% 6.52/1.49  fof(f25,plain,(
% 6.52/1.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 6.52/1.49    inference(cnf_transformation,[],[f9])).
% 6.52/1.49  
% 6.52/1.49  fof(f32,plain,(
% 6.52/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 6.52/1.49    inference(definition_unfolding,[],[f25,f24,f24])).
% 6.52/1.49  
% 6.52/1.49  fof(f6,axiom,(
% 6.52/1.49    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 6.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.52/1.49  
% 6.52/1.49  fof(f22,plain,(
% 6.52/1.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 6.52/1.49    inference(cnf_transformation,[],[f6])).
% 6.52/1.49  
% 6.52/1.49  fof(f3,axiom,(
% 6.52/1.49    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 6.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.52/1.49  
% 6.52/1.49  fof(f19,plain,(
% 6.52/1.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 6.52/1.49    inference(cnf_transformation,[],[f3])).
% 6.52/1.49  
% 6.52/1.49  fof(f30,plain,(
% 6.52/1.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 6.52/1.49    inference(definition_unfolding,[],[f19,f24])).
% 6.52/1.49  
% 6.52/1.49  fof(f4,axiom,(
% 6.52/1.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 6.52/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.52/1.49  
% 6.52/1.49  fof(f20,plain,(
% 6.52/1.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.52/1.49    inference(cnf_transformation,[],[f4])).
% 6.52/1.49  
% 6.52/1.49  fof(f18,plain,(
% 6.52/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 6.52/1.49    inference(cnf_transformation,[],[f13])).
% 6.52/1.49  
% 6.52/1.49  fof(f28,plain,(
% 6.52/1.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.52/1.49    inference(definition_unfolding,[],[f18,f24])).
% 6.52/1.49  
% 6.52/1.49  fof(f27,plain,(
% 6.52/1.49    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 6.52/1.49    inference(cnf_transformation,[],[f15])).
% 6.52/1.49  
% 6.52/1.49  cnf(c_0,plain,
% 6.52/1.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 6.52/1.49      inference(cnf_transformation,[],[f16]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_2,plain,
% 6.52/1.49      ( ~ r1_xboole_0(X0,X1)
% 6.52/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 6.52/1.49      inference(cnf_transformation,[],[f29]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_44,plain,
% 6.52/1.49      ( ~ r1_xboole_0(X0,X1)
% 6.52/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 6.52/1.49      inference(prop_impl,[status(thm)],[c_2]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_10,negated_conjecture,
% 6.52/1.49      ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 6.52/1.49      inference(cnf_transformation,[],[f26]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_85,plain,
% 6.52/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 6.52/1.49      | k4_xboole_0(sK1,sK2) != X1
% 6.52/1.49      | sK0 != X0 ),
% 6.52/1.49      inference(resolution_lifted,[status(thm)],[c_44,c_10]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_86,plain,
% 6.52/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 6.52/1.49      inference(unflattening,[status(thm)],[c_85]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_7,plain,
% 6.52/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 6.52/1.49      inference(cnf_transformation,[],[f31]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_329,plain,
% 6.52/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 6.52/1.49      inference(superposition,[status(thm)],[c_86,c_7]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_5,plain,
% 6.52/1.49      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 6.52/1.49      inference(cnf_transformation,[],[f21]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_357,plain,
% 6.52/1.49      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = sK0 ),
% 6.52/1.49      inference(demodulation,[status(thm)],[c_329,c_5]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_8,plain,
% 6.52/1.49      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 6.52/1.49      inference(cnf_transformation,[],[f32]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_6,plain,
% 6.52/1.49      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 6.52/1.49      inference(cnf_transformation,[],[f22]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_132,plain,
% 6.52/1.49      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 6.52/1.49      inference(demodulation,[status(thm)],[c_8,c_6]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_797,plain,
% 6.52/1.49      ( k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,sK0),k4_xboole_0(sK1,sK2))) = k4_xboole_0(X0,k4_xboole_0(X0,sK0)) ),
% 6.52/1.49      inference(superposition,[status(thm)],[c_357,c_132]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_3,plain,
% 6.52/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 6.52/1.49      inference(cnf_transformation,[],[f30]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_113,plain,
% 6.52/1.49      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 6.52/1.49      inference(light_normalisation,[status(thm)],[c_3,c_5]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_304,plain,
% 6.52/1.49      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 6.52/1.49      inference(superposition,[status(thm)],[c_6,c_113]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_4,plain,
% 6.52/1.49      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 6.52/1.49      inference(cnf_transformation,[],[f20]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_306,plain,
% 6.52/1.49      ( k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k1_xboole_0 ),
% 6.52/1.49      inference(demodulation,[status(thm)],[c_304,c_4]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_1187,plain,
% 6.52/1.49      ( k4_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(k4_xboole_0(sK1,sK2),sK0)) = k1_xboole_0 ),
% 6.52/1.49      inference(superposition,[status(thm)],[c_797,c_306]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_1189,plain,
% 6.52/1.49      ( k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK2,sK0)))) = k1_xboole_0 ),
% 6.52/1.49      inference(demodulation,[status(thm)],[c_1187,c_6]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_11906,plain,
% 6.52/1.49      ( k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)))) = k1_xboole_0 ),
% 6.52/1.49      inference(superposition,[status(thm)],[c_0,c_1189]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_303,plain,
% 6.52/1.49      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 6.52/1.49      inference(superposition,[status(thm)],[c_6,c_4]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_12485,plain,
% 6.52/1.49      ( k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,sK0))) = k1_xboole_0 ),
% 6.52/1.49      inference(demodulation,[status(thm)],[c_11906,c_303]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_1,plain,
% 6.52/1.49      ( r1_xboole_0(X0,X1)
% 6.52/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 6.52/1.49      inference(cnf_transformation,[],[f28]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_42,plain,
% 6.52/1.49      ( r1_xboole_0(X0,X1)
% 6.52/1.49      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 6.52/1.49      inference(prop_impl,[status(thm)],[c_1]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_9,negated_conjecture,
% 6.52/1.49      ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
% 6.52/1.49      inference(cnf_transformation,[],[f27]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_80,plain,
% 6.52/1.49      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 6.52/1.49      | k4_xboole_0(sK0,sK2) != X1
% 6.52/1.49      | sK1 != X0 ),
% 6.52/1.49      inference(resolution_lifted,[status(thm)],[c_42,c_9]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_81,plain,
% 6.52/1.49      ( k4_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(sK0,sK2))) != k1_xboole_0 ),
% 6.52/1.49      inference(unflattening,[status(thm)],[c_80]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_134,plain,
% 6.52/1.49      ( k4_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK1,sK0),sK2)) != k1_xboole_0 ),
% 6.52/1.49      inference(demodulation,[status(thm)],[c_132,c_81]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(c_203,plain,
% 6.52/1.49      ( k4_xboole_0(sK1,k2_xboole_0(sK2,k4_xboole_0(sK1,sK0))) != k1_xboole_0 ),
% 6.52/1.49      inference(demodulation,[status(thm)],[c_0,c_134]) ).
% 6.52/1.49  
% 6.52/1.49  cnf(contradiction,plain,
% 6.52/1.49      ( $false ),
% 6.52/1.49      inference(minisat,[status(thm)],[c_12485,c_203]) ).
% 6.52/1.49  
% 6.52/1.49  
% 6.52/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 6.52/1.49  
% 6.52/1.49  ------                               Statistics
% 6.52/1.49  
% 6.52/1.49  ------ General
% 6.52/1.49  
% 6.52/1.49  abstr_ref_over_cycles:                  0
% 6.52/1.49  abstr_ref_under_cycles:                 0
% 6.52/1.49  gc_basic_clause_elim:                   0
% 6.52/1.49  forced_gc_time:                         0
% 6.52/1.49  parsing_time:                           0.01
% 6.52/1.49  unif_index_cands_time:                  0.
% 6.52/1.49  unif_index_add_time:                    0.
% 6.52/1.49  orderings_time:                         0.
% 6.52/1.49  out_proof_time:                         0.006
% 6.52/1.49  total_time:                             0.593
% 6.52/1.49  num_of_symbols:                         38
% 6.52/1.49  num_of_terms:                           20540
% 6.52/1.49  
% 6.52/1.49  ------ Preprocessing
% 6.52/1.49  
% 6.52/1.49  num_of_splits:                          0
% 6.52/1.49  num_of_split_atoms:                     0
% 6.52/1.49  num_of_reused_defs:                     0
% 6.52/1.49  num_eq_ax_congr_red:                    3
% 6.52/1.49  num_of_sem_filtered_clauses:            0
% 6.52/1.49  num_of_subtypes:                        0
% 6.52/1.49  monotx_restored_types:                  0
% 6.52/1.49  sat_num_of_epr_types:                   0
% 6.52/1.49  sat_num_of_non_cyclic_types:            0
% 6.52/1.49  sat_guarded_non_collapsed_types:        0
% 6.52/1.49  num_pure_diseq_elim:                    0
% 6.52/1.49  simp_replaced_by:                       0
% 6.52/1.49  res_preprocessed:                       35
% 6.52/1.49  prep_upred:                             0
% 6.52/1.49  prep_unflattend:                        4
% 6.52/1.49  smt_new_axioms:                         0
% 6.52/1.49  pred_elim_cands:                        0
% 6.52/1.49  pred_elim:                              1
% 6.52/1.49  pred_elim_cl:                           1
% 6.52/1.49  pred_elim_cycles:                       2
% 6.52/1.49  merged_defs:                            2
% 6.52/1.49  merged_defs_ncl:                        0
% 6.52/1.49  bin_hyper_res:                          2
% 6.52/1.49  prep_cycles:                            3
% 6.52/1.49  pred_elim_time:                         0.001
% 6.52/1.49  splitting_time:                         0.
% 6.52/1.49  sem_filter_time:                        0.
% 6.52/1.49  monotx_time:                            0.001
% 6.52/1.49  subtype_inf_time:                       0.
% 6.52/1.49  
% 6.52/1.49  ------ Problem properties
% 6.52/1.49  
% 6.52/1.49  clauses:                                10
% 6.52/1.49  conjectures:                            0
% 6.52/1.49  epr:                                    0
% 6.52/1.49  horn:                                   10
% 6.52/1.49  ground:                                 3
% 6.52/1.49  unary:                                  9
% 6.52/1.49  binary:                                 1
% 6.52/1.49  lits:                                   11
% 6.52/1.49  lits_eq:                                11
% 6.52/1.49  fd_pure:                                0
% 6.52/1.49  fd_pseudo:                              0
% 6.52/1.49  fd_cond:                                0
% 6.52/1.49  fd_pseudo_cond:                         0
% 6.52/1.49  ac_symbols:                             0
% 6.52/1.49  
% 6.52/1.49  ------ Propositional Solver
% 6.52/1.49  
% 6.52/1.49  prop_solver_calls:                      28
% 6.52/1.49  prop_fast_solver_calls:                 201
% 6.52/1.49  smt_solver_calls:                       0
% 6.52/1.49  smt_fast_solver_calls:                  0
% 6.52/1.49  prop_num_of_clauses:                    3679
% 6.52/1.49  prop_preprocess_simplified:             4124
% 6.52/1.49  prop_fo_subsumed:                       0
% 6.52/1.49  prop_solver_time:                       0.
% 6.52/1.49  smt_solver_time:                        0.
% 6.52/1.49  smt_fast_solver_time:                   0.
% 6.52/1.49  prop_fast_solver_time:                  0.
% 6.52/1.49  prop_unsat_core_time:                   0.
% 6.52/1.49  
% 6.52/1.49  ------ QBF
% 6.52/1.49  
% 6.52/1.49  qbf_q_res:                              0
% 6.52/1.49  qbf_num_tautologies:                    0
% 6.52/1.49  qbf_prep_cycles:                        0
% 6.52/1.49  
% 6.52/1.49  ------ BMC1
% 6.52/1.49  
% 6.52/1.49  bmc1_current_bound:                     -1
% 6.52/1.49  bmc1_last_solved_bound:                 -1
% 6.52/1.49  bmc1_unsat_core_size:                   -1
% 6.52/1.49  bmc1_unsat_core_parents_size:           -1
% 6.52/1.49  bmc1_merge_next_fun:                    0
% 6.52/1.49  bmc1_unsat_core_clauses_time:           0.
% 6.52/1.49  
% 6.52/1.49  ------ Instantiation
% 6.52/1.49  
% 6.52/1.49  inst_num_of_clauses:                    1078
% 6.52/1.49  inst_num_in_passive:                    595
% 6.52/1.49  inst_num_in_active:                     484
% 6.52/1.49  inst_num_in_unprocessed:                0
% 6.52/1.49  inst_num_of_loops:                      490
% 6.52/1.49  inst_num_of_learning_restarts:          0
% 6.52/1.49  inst_num_moves_active_passive:          1
% 6.52/1.49  inst_lit_activity:                      0
% 6.52/1.49  inst_lit_activity_moves:                0
% 6.52/1.49  inst_num_tautologies:                   0
% 6.52/1.49  inst_num_prop_implied:                  0
% 6.52/1.49  inst_num_existing_simplified:           0
% 6.52/1.49  inst_num_eq_res_simplified:             0
% 6.52/1.49  inst_num_child_elim:                    0
% 6.52/1.49  inst_num_of_dismatching_blockings:      278
% 6.52/1.49  inst_num_of_non_proper_insts:           1000
% 6.52/1.49  inst_num_of_duplicates:                 0
% 6.52/1.49  inst_inst_num_from_inst_to_res:         0
% 6.52/1.49  inst_dismatching_checking_time:         0.
% 6.52/1.49  
% 6.52/1.49  ------ Resolution
% 6.52/1.49  
% 6.52/1.49  res_num_of_clauses:                     0
% 6.52/1.49  res_num_in_passive:                     0
% 6.52/1.49  res_num_in_active:                      0
% 6.52/1.49  res_num_of_loops:                       38
% 6.52/1.49  res_forward_subset_subsumed:            140
% 6.52/1.49  res_backward_subset_subsumed:           4
% 6.52/1.49  res_forward_subsumed:                   0
% 6.52/1.49  res_backward_subsumed:                  0
% 6.52/1.49  res_forward_subsumption_resolution:     0
% 6.52/1.49  res_backward_subsumption_resolution:    0
% 6.52/1.49  res_clause_to_clause_subsumption:       15390
% 6.52/1.49  res_orphan_elimination:                 0
% 6.52/1.49  res_tautology_del:                      110
% 6.52/1.49  res_num_eq_res_simplified:              0
% 6.52/1.49  res_num_sel_changes:                    0
% 6.52/1.49  res_moves_from_active_to_pass:          0
% 6.52/1.49  
% 6.52/1.49  ------ Superposition
% 6.52/1.49  
% 6.52/1.49  sup_time_total:                         0.
% 6.52/1.49  sup_time_generating:                    0.
% 6.52/1.49  sup_time_sim_full:                      0.
% 6.52/1.49  sup_time_sim_immed:                     0.
% 6.52/1.49  
% 6.52/1.49  sup_num_of_clauses:                     1296
% 6.52/1.49  sup_num_in_active:                      84
% 6.52/1.49  sup_num_in_passive:                     1212
% 6.52/1.49  sup_num_of_loops:                       96
% 6.52/1.49  sup_fw_superposition:                   1989
% 6.52/1.49  sup_bw_superposition:                   1290
% 6.52/1.49  sup_immediate_simplified:               1702
% 6.52/1.49  sup_given_eliminated:                   10
% 6.52/1.49  comparisons_done:                       0
% 6.52/1.49  comparisons_avoided:                    0
% 6.52/1.49  
% 6.52/1.49  ------ Simplifications
% 6.52/1.49  
% 6.52/1.49  
% 6.52/1.49  sim_fw_subset_subsumed:                 0
% 6.52/1.49  sim_bw_subset_subsumed:                 0
% 6.52/1.49  sim_fw_subsumed:                        607
% 6.52/1.49  sim_bw_subsumed:                        66
% 6.52/1.49  sim_fw_subsumption_res:                 0
% 6.52/1.49  sim_bw_subsumption_res:                 0
% 6.52/1.49  sim_tautology_del:                      0
% 6.52/1.49  sim_eq_tautology_del:                   339
% 6.52/1.49  sim_eq_res_simp:                        0
% 6.52/1.49  sim_fw_demodulated:                     747
% 6.52/1.49  sim_bw_demodulated:                     70
% 6.52/1.49  sim_light_normalised:                   575
% 6.52/1.49  sim_joinable_taut:                      0
% 6.52/1.49  sim_joinable_simp:                      0
% 6.52/1.49  sim_ac_normalised:                      0
% 6.52/1.49  sim_smt_subsumption:                    0
% 6.52/1.49  
%------------------------------------------------------------------------------
