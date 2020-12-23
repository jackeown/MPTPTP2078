%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:23:05 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 283 expanded)
%              Number of clauses        :   41 ( 103 expanded)
%              Number of leaves         :   11 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  128 ( 568 expanded)
%              Number of equality atoms :   65 ( 207 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f17])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r1_tarski(sK1,sK2)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r1_tarski(sK1,sK2)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f20])).

fof(f35,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f30,f33,f33])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f34,f33])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_14,negated_conjecture,
    ( r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_160,plain,
    ( r1_tarski(X0,X1)
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_14])).

cnf(c_161,plain,
    ( r1_tarski(sK0,sK1) ),
    inference(unflattening,[status(thm)],[c_160])).

cnf(c_623,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_161])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_629,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2680,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_623,c_629])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_625,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_627,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1311,plain,
    ( k2_xboole_0(sK1,sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_625,c_627])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_1524,plain,
    ( k2_xboole_0(sK2,sK1) = sK2 ),
    inference(superposition,[status(thm)],[c_1311,c_0])).

cnf(c_8,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_626,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1668,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,sK1))),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1524,c_626])).

cnf(c_2996,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,k1_xboole_0)),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2680,c_1668])).

cnf(c_10,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_11,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_861,plain,
    ( r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_626])).

cnf(c_1047,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_861])).

cnf(c_9,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1052,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1047,c_9])).

cnf(c_1172,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1052])).

cnf(c_1317,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1172,c_627])).

cnf(c_3001,plain,
    ( r1_tarski(sK0,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2996,c_10,c_1317])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_12,negated_conjecture,
    ( ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_150,plain,
    ( ~ r1_tarski(X0,X1)
    | X1 = X0
    | sK2 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_12])).

cnf(c_151,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK2 = sK0 ),
    inference(unflattening,[status(thm)],[c_150])).

cnf(c_624,plain,
    ( sK2 = sK0
    | r1_tarski(sK0,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_151])).

cnf(c_3442,plain,
    ( sK2 = sK0 ),
    inference(superposition,[status(thm)],[c_3001,c_624])).

cnf(c_3763,plain,
    ( k2_xboole_0(sK0,sK1) = sK0 ),
    inference(demodulation,[status(thm)],[c_3442,c_1524])).

cnf(c_1313,plain,
    ( k2_xboole_0(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_623,c_627])).

cnf(c_4342,plain,
    ( sK1 = sK0 ),
    inference(demodulation,[status(thm)],[c_3763,c_1313])).

cnf(c_172,plain,
    ( sK1 != sK2
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_283,plain,
    ( sK1 != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_172])).

cnf(c_3765,plain,
    ( sK1 != sK0 ),
    inference(demodulation,[status(thm)],[c_3442,c_283])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4342,c_3765])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.91/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.06  
% 2.91/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.91/1.06  
% 2.91/1.06  ------  iProver source info
% 2.91/1.06  
% 2.91/1.06  git: date: 2020-06-30 10:37:57 +0100
% 2.91/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.91/1.06  git: non_committed_changes: false
% 2.91/1.06  git: last_make_outside_of_git: false
% 2.91/1.06  
% 2.91/1.06  ------ 
% 2.91/1.06  
% 2.91/1.06  ------ Input Options
% 2.91/1.06  
% 2.91/1.06  --out_options                           all
% 2.91/1.06  --tptp_safe_out                         true
% 2.91/1.06  --problem_path                          ""
% 2.91/1.06  --include_path                          ""
% 2.91/1.06  --clausifier                            res/vclausify_rel
% 2.91/1.06  --clausifier_options                    ""
% 2.91/1.06  --stdin                                 false
% 2.91/1.06  --stats_out                             all
% 2.91/1.06  
% 2.91/1.06  ------ General Options
% 2.91/1.06  
% 2.91/1.06  --fof                                   false
% 2.91/1.06  --time_out_real                         305.
% 2.91/1.06  --time_out_virtual                      -1.
% 2.91/1.06  --symbol_type_check                     false
% 2.91/1.06  --clausify_out                          false
% 2.91/1.06  --sig_cnt_out                           false
% 3.95/1.06  --trig_cnt_out                          false
% 3.95/1.06  --trig_cnt_out_tolerance                1.
% 3.95/1.06  --trig_cnt_out_sk_spl                   false
% 3.95/1.06  --abstr_cl_out                          false
% 3.95/1.06  
% 3.95/1.06  ------ Global Options
% 3.95/1.06  
% 3.95/1.06  --schedule                              default
% 3.95/1.06  --add_important_lit                     false
% 3.95/1.06  --prop_solver_per_cl                    1000
% 3.95/1.06  --min_unsat_core                        false
% 3.95/1.06  --soft_assumptions                      false
% 3.95/1.06  --soft_lemma_size                       3
% 3.95/1.06  --prop_impl_unit_size                   0
% 3.95/1.06  --prop_impl_unit                        []
% 3.95/1.06  --share_sel_clauses                     true
% 3.95/1.06  --reset_solvers                         false
% 3.95/1.06  --bc_imp_inh                            [conj_cone]
% 3.95/1.06  --conj_cone_tolerance                   3.
% 3.95/1.06  --extra_neg_conj                        none
% 3.95/1.06  --large_theory_mode                     true
% 3.95/1.06  --prolific_symb_bound                   200
% 3.95/1.06  --lt_threshold                          2000
% 3.95/1.06  --clause_weak_htbl                      true
% 3.95/1.06  --gc_record_bc_elim                     false
% 3.95/1.06  
% 3.95/1.06  ------ Preprocessing Options
% 3.95/1.06  
% 3.95/1.06  --preprocessing_flag                    true
% 3.95/1.06  --time_out_prep_mult                    0.1
% 3.95/1.06  --splitting_mode                        input
% 3.95/1.06  --splitting_grd                         true
% 3.95/1.06  --splitting_cvd                         false
% 3.95/1.06  --splitting_cvd_svl                     false
% 3.95/1.06  --splitting_nvd                         32
% 3.95/1.06  --sub_typing                            true
% 3.95/1.06  --prep_gs_sim                           true
% 3.95/1.06  --prep_unflatten                        true
% 3.95/1.06  --prep_res_sim                          true
% 3.95/1.06  --prep_upred                            true
% 3.95/1.06  --prep_sem_filter                       exhaustive
% 3.95/1.06  --prep_sem_filter_out                   false
% 3.95/1.06  --pred_elim                             true
% 3.95/1.06  --res_sim_input                         true
% 3.95/1.06  --eq_ax_congr_red                       true
% 3.95/1.06  --pure_diseq_elim                       true
% 3.95/1.06  --brand_transform                       false
% 3.95/1.06  --non_eq_to_eq                          false
% 3.95/1.06  --prep_def_merge                        true
% 3.95/1.06  --prep_def_merge_prop_impl              false
% 3.95/1.06  --prep_def_merge_mbd                    true
% 3.95/1.06  --prep_def_merge_tr_red                 false
% 3.95/1.06  --prep_def_merge_tr_cl                  false
% 3.95/1.06  --smt_preprocessing                     true
% 3.95/1.06  --smt_ac_axioms                         fast
% 3.95/1.06  --preprocessed_out                      false
% 3.95/1.06  --preprocessed_stats                    false
% 3.95/1.06  
% 3.95/1.06  ------ Abstraction refinement Options
% 3.95/1.06  
% 3.95/1.06  --abstr_ref                             []
% 3.95/1.06  --abstr_ref_prep                        false
% 3.95/1.06  --abstr_ref_until_sat                   false
% 3.95/1.06  --abstr_ref_sig_restrict                funpre
% 3.95/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 3.95/1.06  --abstr_ref_under                       []
% 3.95/1.06  
% 3.95/1.06  ------ SAT Options
% 3.95/1.06  
% 3.95/1.06  --sat_mode                              false
% 3.95/1.06  --sat_fm_restart_options                ""
% 3.95/1.06  --sat_gr_def                            false
% 3.95/1.06  --sat_epr_types                         true
% 3.95/1.06  --sat_non_cyclic_types                  false
% 3.95/1.06  --sat_finite_models                     false
% 3.95/1.06  --sat_fm_lemmas                         false
% 3.95/1.06  --sat_fm_prep                           false
% 3.95/1.06  --sat_fm_uc_incr                        true
% 3.95/1.06  --sat_out_model                         small
% 3.95/1.06  --sat_out_clauses                       false
% 3.95/1.06  
% 3.95/1.06  ------ QBF Options
% 3.95/1.06  
% 3.95/1.06  --qbf_mode                              false
% 3.95/1.06  --qbf_elim_univ                         false
% 3.95/1.06  --qbf_dom_inst                          none
% 3.95/1.06  --qbf_dom_pre_inst                      false
% 3.95/1.06  --qbf_sk_in                             false
% 3.95/1.06  --qbf_pred_elim                         true
% 3.95/1.06  --qbf_split                             512
% 3.95/1.06  
% 3.95/1.06  ------ BMC1 Options
% 3.95/1.06  
% 3.95/1.06  --bmc1_incremental                      false
% 3.95/1.06  --bmc1_axioms                           reachable_all
% 3.95/1.06  --bmc1_min_bound                        0
% 3.95/1.06  --bmc1_max_bound                        -1
% 3.95/1.06  --bmc1_max_bound_default                -1
% 3.95/1.06  --bmc1_symbol_reachability              true
% 3.95/1.06  --bmc1_property_lemmas                  false
% 3.95/1.06  --bmc1_k_induction                      false
% 3.95/1.06  --bmc1_non_equiv_states                 false
% 3.95/1.06  --bmc1_deadlock                         false
% 3.95/1.06  --bmc1_ucm                              false
% 3.95/1.06  --bmc1_add_unsat_core                   none
% 3.95/1.06  --bmc1_unsat_core_children              false
% 3.95/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 3.95/1.06  --bmc1_out_stat                         full
% 3.95/1.06  --bmc1_ground_init                      false
% 3.95/1.06  --bmc1_pre_inst_next_state              false
% 3.95/1.06  --bmc1_pre_inst_state                   false
% 3.95/1.06  --bmc1_pre_inst_reach_state             false
% 3.95/1.06  --bmc1_out_unsat_core                   false
% 3.95/1.06  --bmc1_aig_witness_out                  false
% 3.95/1.06  --bmc1_verbose                          false
% 3.95/1.06  --bmc1_dump_clauses_tptp                false
% 3.95/1.06  --bmc1_dump_unsat_core_tptp             false
% 3.95/1.06  --bmc1_dump_file                        -
% 3.95/1.06  --bmc1_ucm_expand_uc_limit              128
% 3.95/1.06  --bmc1_ucm_n_expand_iterations          6
% 3.95/1.06  --bmc1_ucm_extend_mode                  1
% 3.95/1.06  --bmc1_ucm_init_mode                    2
% 3.95/1.06  --bmc1_ucm_cone_mode                    none
% 3.95/1.06  --bmc1_ucm_reduced_relation_type        0
% 3.95/1.06  --bmc1_ucm_relax_model                  4
% 3.95/1.06  --bmc1_ucm_full_tr_after_sat            true
% 3.95/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 3.95/1.06  --bmc1_ucm_layered_model                none
% 3.95/1.06  --bmc1_ucm_max_lemma_size               10
% 3.95/1.06  
% 3.95/1.06  ------ AIG Options
% 3.95/1.06  
% 3.95/1.06  --aig_mode                              false
% 3.95/1.06  
% 3.95/1.06  ------ Instantiation Options
% 3.95/1.06  
% 3.95/1.06  --instantiation_flag                    true
% 3.95/1.06  --inst_sos_flag                         true
% 3.95/1.06  --inst_sos_phase                        true
% 3.95/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.95/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.95/1.06  --inst_lit_sel_side                     num_symb
% 3.95/1.06  --inst_solver_per_active                1400
% 3.95/1.06  --inst_solver_calls_frac                1.
% 3.95/1.06  --inst_passive_queue_type               priority_queues
% 3.95/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.95/1.06  --inst_passive_queues_freq              [25;2]
% 3.95/1.06  --inst_dismatching                      true
% 3.95/1.06  --inst_eager_unprocessed_to_passive     true
% 3.95/1.06  --inst_prop_sim_given                   true
% 3.95/1.06  --inst_prop_sim_new                     false
% 3.95/1.06  --inst_subs_new                         false
% 3.95/1.06  --inst_eq_res_simp                      false
% 3.95/1.06  --inst_subs_given                       false
% 3.95/1.06  --inst_orphan_elimination               true
% 3.95/1.06  --inst_learning_loop_flag               true
% 3.95/1.06  --inst_learning_start                   3000
% 3.95/1.06  --inst_learning_factor                  2
% 3.95/1.06  --inst_start_prop_sim_after_learn       3
% 3.95/1.06  --inst_sel_renew                        solver
% 3.95/1.06  --inst_lit_activity_flag                true
% 3.95/1.06  --inst_restr_to_given                   false
% 3.95/1.06  --inst_activity_threshold               500
% 3.95/1.06  --inst_out_proof                        true
% 3.95/1.06  
% 3.95/1.06  ------ Resolution Options
% 3.95/1.06  
% 3.95/1.06  --resolution_flag                       true
% 3.95/1.06  --res_lit_sel                           adaptive
% 3.95/1.06  --res_lit_sel_side                      none
% 3.95/1.06  --res_ordering                          kbo
% 3.95/1.06  --res_to_prop_solver                    active
% 3.95/1.06  --res_prop_simpl_new                    false
% 3.95/1.06  --res_prop_simpl_given                  true
% 3.95/1.06  --res_passive_queue_type                priority_queues
% 3.95/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.95/1.06  --res_passive_queues_freq               [15;5]
% 3.95/1.06  --res_forward_subs                      full
% 3.95/1.06  --res_backward_subs                     full
% 3.95/1.06  --res_forward_subs_resolution           true
% 3.95/1.06  --res_backward_subs_resolution          true
% 3.95/1.06  --res_orphan_elimination                true
% 3.95/1.06  --res_time_limit                        2.
% 3.95/1.06  --res_out_proof                         true
% 3.95/1.06  
% 3.95/1.06  ------ Superposition Options
% 3.95/1.06  
% 3.95/1.06  --superposition_flag                    true
% 3.95/1.06  --sup_passive_queue_type                priority_queues
% 3.95/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.95/1.06  --sup_passive_queues_freq               [8;1;4]
% 3.95/1.06  --demod_completeness_check              fast
% 3.95/1.06  --demod_use_ground                      true
% 3.95/1.06  --sup_to_prop_solver                    passive
% 3.95/1.06  --sup_prop_simpl_new                    true
% 3.95/1.06  --sup_prop_simpl_given                  true
% 3.95/1.06  --sup_fun_splitting                     true
% 3.95/1.06  --sup_smt_interval                      50000
% 3.95/1.06  
% 3.95/1.06  ------ Superposition Simplification Setup
% 3.95/1.06  
% 3.95/1.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.95/1.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.95/1.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.95/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.95/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 3.95/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.95/1.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.95/1.06  --sup_immed_triv                        [TrivRules]
% 3.95/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/1.06  --sup_immed_bw_main                     []
% 3.95/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.95/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 3.95/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/1.06  --sup_input_bw                          []
% 3.95/1.06  
% 3.95/1.06  ------ Combination Options
% 3.95/1.06  
% 3.95/1.06  --comb_res_mult                         3
% 3.95/1.06  --comb_sup_mult                         2
% 3.95/1.06  --comb_inst_mult                        10
% 3.95/1.06  
% 3.95/1.06  ------ Debug Options
% 3.95/1.06  
% 3.95/1.06  --dbg_backtrace                         false
% 3.95/1.06  --dbg_dump_prop_clauses                 false
% 3.95/1.06  --dbg_dump_prop_clauses_file            -
% 3.95/1.06  --dbg_out_stat                          false
% 3.95/1.06  ------ Parsing...
% 3.95/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.95/1.06  
% 3.95/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.95/1.06  
% 3.95/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.95/1.06  
% 3.95/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.95/1.06  ------ Proving...
% 3.95/1.06  ------ Problem Properties 
% 3.95/1.06  
% 3.95/1.06  
% 3.95/1.06  clauses                                 13
% 3.95/1.06  conjectures                             1
% 3.95/1.06  EPR                                     5
% 3.95/1.06  Horn                                    13
% 3.95/1.06  unary                                   9
% 3.95/1.06  binary                                  4
% 3.95/1.06  lits                                    17
% 3.95/1.06  lits eq                                 10
% 3.95/1.06  fd_pure                                 0
% 3.95/1.06  fd_pseudo                               0
% 3.95/1.06  fd_cond                                 0
% 3.95/1.06  fd_pseudo_cond                          0
% 3.95/1.06  AC symbols                              0
% 3.95/1.06  
% 3.95/1.06  ------ Schedule dynamic 5 is on 
% 3.95/1.06  
% 3.95/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.95/1.06  
% 3.95/1.06  
% 3.95/1.06  ------ 
% 3.95/1.06  Current options:
% 3.95/1.06  ------ 
% 3.95/1.06  
% 3.95/1.06  ------ Input Options
% 3.95/1.06  
% 3.95/1.06  --out_options                           all
% 3.95/1.06  --tptp_safe_out                         true
% 3.95/1.06  --problem_path                          ""
% 3.95/1.06  --include_path                          ""
% 3.95/1.06  --clausifier                            res/vclausify_rel
% 3.95/1.06  --clausifier_options                    ""
% 3.95/1.06  --stdin                                 false
% 3.95/1.06  --stats_out                             all
% 3.95/1.06  
% 3.95/1.06  ------ General Options
% 3.95/1.06  
% 3.95/1.06  --fof                                   false
% 3.95/1.06  --time_out_real                         305.
% 3.95/1.06  --time_out_virtual                      -1.
% 3.95/1.06  --symbol_type_check                     false
% 3.95/1.06  --clausify_out                          false
% 3.95/1.06  --sig_cnt_out                           false
% 3.95/1.06  --trig_cnt_out                          false
% 3.95/1.06  --trig_cnt_out_tolerance                1.
% 3.95/1.06  --trig_cnt_out_sk_spl                   false
% 3.95/1.06  --abstr_cl_out                          false
% 3.95/1.06  
% 3.95/1.06  ------ Global Options
% 3.95/1.06  
% 3.95/1.06  --schedule                              default
% 3.95/1.06  --add_important_lit                     false
% 3.95/1.06  --prop_solver_per_cl                    1000
% 3.95/1.06  --min_unsat_core                        false
% 3.95/1.06  --soft_assumptions                      false
% 3.95/1.06  --soft_lemma_size                       3
% 3.95/1.06  --prop_impl_unit_size                   0
% 3.95/1.06  --prop_impl_unit                        []
% 3.95/1.06  --share_sel_clauses                     true
% 3.95/1.06  --reset_solvers                         false
% 3.95/1.06  --bc_imp_inh                            [conj_cone]
% 3.95/1.06  --conj_cone_tolerance                   3.
% 3.95/1.06  --extra_neg_conj                        none
% 3.95/1.06  --large_theory_mode                     true
% 3.95/1.06  --prolific_symb_bound                   200
% 3.95/1.06  --lt_threshold                          2000
% 3.95/1.06  --clause_weak_htbl                      true
% 3.95/1.06  --gc_record_bc_elim                     false
% 3.95/1.06  
% 3.95/1.06  ------ Preprocessing Options
% 3.95/1.06  
% 3.95/1.06  --preprocessing_flag                    true
% 3.95/1.06  --time_out_prep_mult                    0.1
% 3.95/1.06  --splitting_mode                        input
% 3.95/1.06  --splitting_grd                         true
% 3.95/1.06  --splitting_cvd                         false
% 3.95/1.06  --splitting_cvd_svl                     false
% 3.95/1.06  --splitting_nvd                         32
% 3.95/1.06  --sub_typing                            true
% 3.95/1.06  --prep_gs_sim                           true
% 3.95/1.06  --prep_unflatten                        true
% 3.95/1.06  --prep_res_sim                          true
% 3.95/1.06  --prep_upred                            true
% 3.95/1.06  --prep_sem_filter                       exhaustive
% 3.95/1.06  --prep_sem_filter_out                   false
% 3.95/1.06  --pred_elim                             true
% 3.95/1.06  --res_sim_input                         true
% 3.95/1.06  --eq_ax_congr_red                       true
% 3.95/1.06  --pure_diseq_elim                       true
% 3.95/1.06  --brand_transform                       false
% 3.95/1.06  --non_eq_to_eq                          false
% 3.95/1.06  --prep_def_merge                        true
% 3.95/1.06  --prep_def_merge_prop_impl              false
% 3.95/1.06  --prep_def_merge_mbd                    true
% 3.95/1.06  --prep_def_merge_tr_red                 false
% 3.95/1.06  --prep_def_merge_tr_cl                  false
% 3.95/1.06  --smt_preprocessing                     true
% 3.95/1.06  --smt_ac_axioms                         fast
% 3.95/1.06  --preprocessed_out                      false
% 3.95/1.06  --preprocessed_stats                    false
% 3.95/1.06  
% 3.95/1.06  ------ Abstraction refinement Options
% 3.95/1.06  
% 3.95/1.06  --abstr_ref                             []
% 3.95/1.06  --abstr_ref_prep                        false
% 3.95/1.06  --abstr_ref_until_sat                   false
% 3.95/1.06  --abstr_ref_sig_restrict                funpre
% 3.95/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 3.95/1.06  --abstr_ref_under                       []
% 3.95/1.06  
% 3.95/1.06  ------ SAT Options
% 3.95/1.06  
% 3.95/1.06  --sat_mode                              false
% 3.95/1.06  --sat_fm_restart_options                ""
% 3.95/1.06  --sat_gr_def                            false
% 3.95/1.06  --sat_epr_types                         true
% 3.95/1.06  --sat_non_cyclic_types                  false
% 3.95/1.06  --sat_finite_models                     false
% 3.95/1.06  --sat_fm_lemmas                         false
% 3.95/1.06  --sat_fm_prep                           false
% 3.95/1.06  --sat_fm_uc_incr                        true
% 3.95/1.06  --sat_out_model                         small
% 3.95/1.06  --sat_out_clauses                       false
% 3.95/1.06  
% 3.95/1.06  ------ QBF Options
% 3.95/1.06  
% 3.95/1.06  --qbf_mode                              false
% 3.95/1.06  --qbf_elim_univ                         false
% 3.95/1.06  --qbf_dom_inst                          none
% 3.95/1.06  --qbf_dom_pre_inst                      false
% 3.95/1.06  --qbf_sk_in                             false
% 3.95/1.06  --qbf_pred_elim                         true
% 3.95/1.06  --qbf_split                             512
% 3.95/1.06  
% 3.95/1.06  ------ BMC1 Options
% 3.95/1.06  
% 3.95/1.06  --bmc1_incremental                      false
% 3.95/1.06  --bmc1_axioms                           reachable_all
% 3.95/1.06  --bmc1_min_bound                        0
% 3.95/1.06  --bmc1_max_bound                        -1
% 3.95/1.06  --bmc1_max_bound_default                -1
% 3.95/1.06  --bmc1_symbol_reachability              true
% 3.95/1.06  --bmc1_property_lemmas                  false
% 3.95/1.06  --bmc1_k_induction                      false
% 3.95/1.06  --bmc1_non_equiv_states                 false
% 3.95/1.06  --bmc1_deadlock                         false
% 3.95/1.06  --bmc1_ucm                              false
% 3.95/1.06  --bmc1_add_unsat_core                   none
% 3.95/1.06  --bmc1_unsat_core_children              false
% 3.95/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 3.95/1.06  --bmc1_out_stat                         full
% 3.95/1.06  --bmc1_ground_init                      false
% 3.95/1.06  --bmc1_pre_inst_next_state              false
% 3.95/1.06  --bmc1_pre_inst_state                   false
% 3.95/1.06  --bmc1_pre_inst_reach_state             false
% 3.95/1.06  --bmc1_out_unsat_core                   false
% 3.95/1.06  --bmc1_aig_witness_out                  false
% 3.95/1.06  --bmc1_verbose                          false
% 3.95/1.06  --bmc1_dump_clauses_tptp                false
% 3.95/1.06  --bmc1_dump_unsat_core_tptp             false
% 3.95/1.06  --bmc1_dump_file                        -
% 3.95/1.06  --bmc1_ucm_expand_uc_limit              128
% 3.95/1.06  --bmc1_ucm_n_expand_iterations          6
% 3.95/1.06  --bmc1_ucm_extend_mode                  1
% 3.95/1.06  --bmc1_ucm_init_mode                    2
% 3.95/1.06  --bmc1_ucm_cone_mode                    none
% 3.95/1.06  --bmc1_ucm_reduced_relation_type        0
% 3.95/1.06  --bmc1_ucm_relax_model                  4
% 3.95/1.06  --bmc1_ucm_full_tr_after_sat            true
% 3.95/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 3.95/1.06  --bmc1_ucm_layered_model                none
% 3.95/1.06  --bmc1_ucm_max_lemma_size               10
% 3.95/1.06  
% 3.95/1.06  ------ AIG Options
% 3.95/1.06  
% 3.95/1.06  --aig_mode                              false
% 3.95/1.06  
% 3.95/1.06  ------ Instantiation Options
% 3.95/1.06  
% 3.95/1.06  --instantiation_flag                    true
% 3.95/1.06  --inst_sos_flag                         true
% 3.95/1.06  --inst_sos_phase                        true
% 3.95/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.95/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.95/1.06  --inst_lit_sel_side                     none
% 3.95/1.06  --inst_solver_per_active                1400
% 3.95/1.06  --inst_solver_calls_frac                1.
% 3.95/1.06  --inst_passive_queue_type               priority_queues
% 3.95/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.95/1.06  --inst_passive_queues_freq              [25;2]
% 3.95/1.06  --inst_dismatching                      true
% 3.95/1.06  --inst_eager_unprocessed_to_passive     true
% 3.95/1.06  --inst_prop_sim_given                   true
% 3.95/1.06  --inst_prop_sim_new                     false
% 3.95/1.06  --inst_subs_new                         false
% 3.95/1.06  --inst_eq_res_simp                      false
% 3.95/1.06  --inst_subs_given                       false
% 3.95/1.06  --inst_orphan_elimination               true
% 3.95/1.06  --inst_learning_loop_flag               true
% 3.95/1.06  --inst_learning_start                   3000
% 3.95/1.06  --inst_learning_factor                  2
% 3.95/1.06  --inst_start_prop_sim_after_learn       3
% 3.95/1.06  --inst_sel_renew                        solver
% 3.95/1.06  --inst_lit_activity_flag                true
% 3.95/1.06  --inst_restr_to_given                   false
% 3.95/1.06  --inst_activity_threshold               500
% 3.95/1.06  --inst_out_proof                        true
% 3.95/1.06  
% 3.95/1.06  ------ Resolution Options
% 3.95/1.06  
% 3.95/1.06  --resolution_flag                       false
% 3.95/1.06  --res_lit_sel                           adaptive
% 3.95/1.06  --res_lit_sel_side                      none
% 3.95/1.06  --res_ordering                          kbo
% 3.95/1.06  --res_to_prop_solver                    active
% 3.95/1.06  --res_prop_simpl_new                    false
% 3.95/1.06  --res_prop_simpl_given                  true
% 3.95/1.06  --res_passive_queue_type                priority_queues
% 3.95/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.95/1.06  --res_passive_queues_freq               [15;5]
% 3.95/1.06  --res_forward_subs                      full
% 3.95/1.06  --res_backward_subs                     full
% 3.95/1.06  --res_forward_subs_resolution           true
% 3.95/1.06  --res_backward_subs_resolution          true
% 3.95/1.06  --res_orphan_elimination                true
% 3.95/1.06  --res_time_limit                        2.
% 3.95/1.06  --res_out_proof                         true
% 3.95/1.06  
% 3.95/1.06  ------ Superposition Options
% 3.95/1.06  
% 3.95/1.06  --superposition_flag                    true
% 3.95/1.06  --sup_passive_queue_type                priority_queues
% 3.95/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.95/1.06  --sup_passive_queues_freq               [8;1;4]
% 3.95/1.06  --demod_completeness_check              fast
% 3.95/1.06  --demod_use_ground                      true
% 3.95/1.06  --sup_to_prop_solver                    passive
% 3.95/1.06  --sup_prop_simpl_new                    true
% 3.95/1.06  --sup_prop_simpl_given                  true
% 3.95/1.06  --sup_fun_splitting                     true
% 3.95/1.06  --sup_smt_interval                      50000
% 3.95/1.06  
% 3.95/1.06  ------ Superposition Simplification Setup
% 3.95/1.06  
% 3.95/1.06  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.95/1.06  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.95/1.06  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.95/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.95/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 3.95/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.95/1.06  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.95/1.06  --sup_immed_triv                        [TrivRules]
% 3.95/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/1.06  --sup_immed_bw_main                     []
% 3.95/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.95/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 3.95/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/1.06  --sup_input_bw                          []
% 3.95/1.06  
% 3.95/1.06  ------ Combination Options
% 3.95/1.06  
% 3.95/1.06  --comb_res_mult                         3
% 3.95/1.06  --comb_sup_mult                         2
% 3.95/1.06  --comb_inst_mult                        10
% 3.95/1.06  
% 3.95/1.06  ------ Debug Options
% 3.95/1.06  
% 3.95/1.06  --dbg_backtrace                         false
% 3.95/1.06  --dbg_dump_prop_clauses                 false
% 3.95/1.06  --dbg_dump_prop_clauses_file            -
% 3.95/1.06  --dbg_out_stat                          false
% 3.95/1.06  
% 3.95/1.06  
% 3.95/1.06  
% 3.95/1.06  
% 3.95/1.06  ------ Proving...
% 3.95/1.06  
% 3.95/1.06  
% 3.95/1.06  % SZS status Theorem for theBenchmark.p
% 3.95/1.06  
% 3.95/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 3.95/1.06  
% 3.95/1.06  fof(f2,axiom,(
% 3.95/1.06    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 3.95/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.06  
% 3.95/1.06  fof(f17,plain,(
% 3.95/1.06    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 3.95/1.06    inference(nnf_transformation,[],[f2])).
% 3.95/1.06  
% 3.95/1.06  fof(f18,plain,(
% 3.95/1.06    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 3.95/1.06    inference(flattening,[],[f17])).
% 3.95/1.06  
% 3.95/1.06  fof(f23,plain,(
% 3.95/1.06    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 3.95/1.06    inference(cnf_transformation,[],[f18])).
% 3.95/1.06  
% 3.95/1.06  fof(f11,conjecture,(
% 3.95/1.06    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 3.95/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.06  
% 3.95/1.06  fof(f12,negated_conjecture,(
% 3.95/1.06    ~! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 3.95/1.06    inference(negated_conjecture,[],[f11])).
% 3.95/1.06  
% 3.95/1.06  fof(f15,plain,(
% 3.95/1.06    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r1_tarski(X1,X2) & r2_xboole_0(X0,X1)))),
% 3.95/1.06    inference(ennf_transformation,[],[f12])).
% 3.95/1.06  
% 3.95/1.06  fof(f16,plain,(
% 3.95/1.06    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1))),
% 3.95/1.06    inference(flattening,[],[f15])).
% 3.95/1.06  
% 3.95/1.06  fof(f20,plain,(
% 3.95/1.06    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => (~r2_xboole_0(sK0,sK2) & r1_tarski(sK1,sK2) & r2_xboole_0(sK0,sK1))),
% 3.95/1.06    introduced(choice_axiom,[])).
% 3.95/1.06  
% 3.95/1.06  fof(f21,plain,(
% 3.95/1.06    ~r2_xboole_0(sK0,sK2) & r1_tarski(sK1,sK2) & r2_xboole_0(sK0,sK1)),
% 3.95/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f20])).
% 3.95/1.06  
% 3.95/1.06  fof(f35,plain,(
% 3.95/1.06    r2_xboole_0(sK0,sK1)),
% 3.95/1.06    inference(cnf_transformation,[],[f21])).
% 3.95/1.06  
% 3.95/1.06  fof(f4,axiom,(
% 3.95/1.06    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.95/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.06  
% 3.95/1.06  fof(f19,plain,(
% 3.95/1.06    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.95/1.06    inference(nnf_transformation,[],[f4])).
% 3.95/1.06  
% 3.95/1.06  fof(f28,plain,(
% 3.95/1.06    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.95/1.06    inference(cnf_transformation,[],[f19])).
% 3.95/1.06  
% 3.95/1.06  fof(f36,plain,(
% 3.95/1.06    r1_tarski(sK1,sK2)),
% 3.95/1.06    inference(cnf_transformation,[],[f21])).
% 3.95/1.06  
% 3.95/1.06  fof(f5,axiom,(
% 3.95/1.06    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.95/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.06  
% 3.95/1.06  fof(f14,plain,(
% 3.95/1.06    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.95/1.06    inference(ennf_transformation,[],[f5])).
% 3.95/1.06  
% 3.95/1.06  fof(f29,plain,(
% 3.95/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.95/1.06    inference(cnf_transformation,[],[f14])).
% 3.95/1.06  
% 3.95/1.06  fof(f1,axiom,(
% 3.95/1.06    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.95/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.06  
% 3.95/1.06  fof(f22,plain,(
% 3.95/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.95/1.06    inference(cnf_transformation,[],[f1])).
% 3.95/1.06  
% 3.95/1.06  fof(f6,axiom,(
% 3.95/1.06    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 3.95/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.06  
% 3.95/1.06  fof(f30,plain,(
% 3.95/1.06    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 3.95/1.06    inference(cnf_transformation,[],[f6])).
% 3.95/1.06  
% 3.95/1.06  fof(f9,axiom,(
% 3.95/1.06    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 3.95/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.06  
% 3.95/1.06  fof(f33,plain,(
% 3.95/1.06    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 3.95/1.06    inference(cnf_transformation,[],[f9])).
% 3.95/1.06  
% 3.95/1.06  fof(f38,plain,(
% 3.95/1.06    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2))) )),
% 3.95/1.06    inference(definition_unfolding,[],[f30,f33,f33])).
% 3.95/1.06  
% 3.95/1.06  fof(f8,axiom,(
% 3.95/1.06    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.95/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.06  
% 3.95/1.06  fof(f32,plain,(
% 3.95/1.06    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.95/1.06    inference(cnf_transformation,[],[f8])).
% 3.95/1.06  
% 3.95/1.06  fof(f10,axiom,(
% 3.95/1.06    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 3.95/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.06  
% 3.95/1.06  fof(f34,plain,(
% 3.95/1.06    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 3.95/1.06    inference(cnf_transformation,[],[f10])).
% 3.95/1.06  
% 3.95/1.06  fof(f39,plain,(
% 3.95/1.06    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 3.95/1.06    inference(definition_unfolding,[],[f34,f33])).
% 3.95/1.06  
% 3.95/1.06  fof(f7,axiom,(
% 3.95/1.06    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.95/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.95/1.06  
% 3.95/1.06  fof(f31,plain,(
% 3.95/1.06    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.95/1.06    inference(cnf_transformation,[],[f7])).
% 3.95/1.06  
% 3.95/1.06  fof(f25,plain,(
% 3.95/1.06    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.95/1.06    inference(cnf_transformation,[],[f18])).
% 3.95/1.06  
% 3.95/1.06  fof(f37,plain,(
% 3.95/1.06    ~r2_xboole_0(sK0,sK2)),
% 3.95/1.06    inference(cnf_transformation,[],[f21])).
% 3.95/1.06  
% 3.95/1.06  cnf(c_3,plain,
% 3.95/1.06      ( r1_tarski(X0,X1) | ~ r2_xboole_0(X0,X1) ),
% 3.95/1.06      inference(cnf_transformation,[],[f23]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_14,negated_conjecture,
% 3.95/1.06      ( r2_xboole_0(sK0,sK1) ),
% 3.95/1.06      inference(cnf_transformation,[],[f35]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_160,plain,
% 3.95/1.06      ( r1_tarski(X0,X1) | sK1 != X1 | sK0 != X0 ),
% 3.95/1.06      inference(resolution_lifted,[status(thm)],[c_3,c_14]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_161,plain,
% 3.95/1.06      ( r1_tarski(sK0,sK1) ),
% 3.95/1.06      inference(unflattening,[status(thm)],[c_160]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_623,plain,
% 3.95/1.06      ( r1_tarski(sK0,sK1) = iProver_top ),
% 3.95/1.06      inference(predicate_to_equality,[status(thm)],[c_161]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_5,plain,
% 3.95/1.06      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.95/1.06      inference(cnf_transformation,[],[f28]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_629,plain,
% 3.95/1.06      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.95/1.06      | r1_tarski(X0,X1) != iProver_top ),
% 3.95/1.06      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_2680,plain,
% 3.95/1.06      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 3.95/1.06      inference(superposition,[status(thm)],[c_623,c_629]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_13,negated_conjecture,
% 3.95/1.06      ( r1_tarski(sK1,sK2) ),
% 3.95/1.06      inference(cnf_transformation,[],[f36]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_625,plain,
% 3.95/1.06      ( r1_tarski(sK1,sK2) = iProver_top ),
% 3.95/1.06      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_7,plain,
% 3.95/1.06      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 3.95/1.06      inference(cnf_transformation,[],[f29]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_627,plain,
% 3.95/1.06      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 3.95/1.06      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_1311,plain,
% 3.95/1.06      ( k2_xboole_0(sK1,sK2) = sK2 ),
% 3.95/1.06      inference(superposition,[status(thm)],[c_625,c_627]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_0,plain,
% 3.95/1.06      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 3.95/1.06      inference(cnf_transformation,[],[f22]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_1524,plain,
% 3.95/1.06      ( k2_xboole_0(sK2,sK1) = sK2 ),
% 3.95/1.06      inference(superposition,[status(thm)],[c_1311,c_0]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_8,plain,
% 3.95/1.06      ( r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2)) ),
% 3.95/1.06      inference(cnf_transformation,[],[f38]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_626,plain,
% 3.95/1.06      ( r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))),k2_xboole_0(X1,X2)) = iProver_top ),
% 3.95/1.06      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_1668,plain,
% 3.95/1.06      ( r1_tarski(k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,sK2)),k4_xboole_0(X0,k4_xboole_0(X0,sK1))),sK2) = iProver_top ),
% 3.95/1.06      inference(superposition,[status(thm)],[c_1524,c_626]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_2996,plain,
% 3.95/1.06      ( r1_tarski(k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK0,k1_xboole_0)),sK2) = iProver_top ),
% 3.95/1.06      inference(superposition,[status(thm)],[c_2680,c_1668]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_10,plain,
% 3.95/1.06      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.95/1.06      inference(cnf_transformation,[],[f32]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_11,plain,
% 3.95/1.06      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 3.95/1.06      inference(cnf_transformation,[],[f39]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_861,plain,
% 3.95/1.06      ( r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,X1),X1)) = iProver_top ),
% 3.95/1.06      inference(superposition,[status(thm)],[c_11,c_626]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_1047,plain,
% 3.95/1.06      ( r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = iProver_top ),
% 3.95/1.06      inference(superposition,[status(thm)],[c_0,c_861]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_9,plain,
% 3.95/1.06      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 3.95/1.06      inference(cnf_transformation,[],[f31]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_1052,plain,
% 3.95/1.06      ( r1_tarski(X0,k2_xboole_0(X1,X0)) = iProver_top ),
% 3.95/1.06      inference(demodulation,[status(thm)],[c_1047,c_9]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_1172,plain,
% 3.95/1.06      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.95/1.06      inference(superposition,[status(thm)],[c_11,c_1052]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_1317,plain,
% 3.95/1.06      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 3.95/1.06      inference(superposition,[status(thm)],[c_1172,c_627]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_3001,plain,
% 3.95/1.06      ( r1_tarski(sK0,sK2) = iProver_top ),
% 3.95/1.06      inference(demodulation,[status(thm)],[c_2996,c_10,c_1317]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_1,plain,
% 3.95/1.06      ( ~ r1_tarski(X0,X1) | r2_xboole_0(X0,X1) | X1 = X0 ),
% 3.95/1.06      inference(cnf_transformation,[],[f25]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_12,negated_conjecture,
% 3.95/1.06      ( ~ r2_xboole_0(sK0,sK2) ),
% 3.95/1.06      inference(cnf_transformation,[],[f37]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_150,plain,
% 3.95/1.06      ( ~ r1_tarski(X0,X1) | X1 = X0 | sK2 != X1 | sK0 != X0 ),
% 3.95/1.06      inference(resolution_lifted,[status(thm)],[c_1,c_12]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_151,plain,
% 3.95/1.06      ( ~ r1_tarski(sK0,sK2) | sK2 = sK0 ),
% 3.95/1.06      inference(unflattening,[status(thm)],[c_150]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_624,plain,
% 3.95/1.06      ( sK2 = sK0 | r1_tarski(sK0,sK2) != iProver_top ),
% 3.95/1.06      inference(predicate_to_equality,[status(thm)],[c_151]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_3442,plain,
% 3.95/1.06      ( sK2 = sK0 ),
% 3.95/1.06      inference(superposition,[status(thm)],[c_3001,c_624]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_3763,plain,
% 3.95/1.06      ( k2_xboole_0(sK0,sK1) = sK0 ),
% 3.95/1.06      inference(demodulation,[status(thm)],[c_3442,c_1524]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_1313,plain,
% 3.95/1.06      ( k2_xboole_0(sK0,sK1) = sK1 ),
% 3.95/1.06      inference(superposition,[status(thm)],[c_623,c_627]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_4342,plain,
% 3.95/1.06      ( sK1 = sK0 ),
% 3.95/1.06      inference(demodulation,[status(thm)],[c_3763,c_1313]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_172,plain,
% 3.95/1.06      ( sK1 != sK2 | sK0 != sK0 ),
% 3.95/1.06      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_283,plain,
% 3.95/1.06      ( sK1 != sK2 ),
% 3.95/1.06      inference(equality_resolution_simp,[status(thm)],[c_172]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(c_3765,plain,
% 3.95/1.06      ( sK1 != sK0 ),
% 3.95/1.06      inference(demodulation,[status(thm)],[c_3442,c_283]) ).
% 3.95/1.06  
% 3.95/1.06  cnf(contradiction,plain,
% 3.95/1.06      ( $false ),
% 3.95/1.06      inference(minisat,[status(thm)],[c_4342,c_3765]) ).
% 3.95/1.06  
% 3.95/1.06  
% 3.95/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 3.95/1.06  
% 3.95/1.06  ------                               Statistics
% 3.95/1.06  
% 3.95/1.06  ------ General
% 3.95/1.06  
% 3.95/1.06  abstr_ref_over_cycles:                  0
% 3.95/1.06  abstr_ref_under_cycles:                 0
% 3.95/1.06  gc_basic_clause_elim:                   0
% 3.95/1.06  forced_gc_time:                         0
% 3.95/1.06  parsing_time:                           0.032
% 3.95/1.06  unif_index_cands_time:                  0.
% 3.95/1.06  unif_index_add_time:                    0.
% 3.95/1.06  orderings_time:                         0.
% 3.95/1.06  out_proof_time:                         0.007
% 3.95/1.06  total_time:                             0.21
% 3.95/1.06  num_of_symbols:                         39
% 3.95/1.06  num_of_terms:                           5277
% 3.95/1.06  
% 3.95/1.06  ------ Preprocessing
% 3.95/1.06  
% 3.95/1.06  num_of_splits:                          0
% 3.95/1.06  num_of_split_atoms:                     0
% 3.95/1.06  num_of_reused_defs:                     0
% 3.95/1.06  num_eq_ax_congr_red:                    3
% 3.95/1.06  num_of_sem_filtered_clauses:            1
% 3.95/1.06  num_of_subtypes:                        0
% 3.95/1.06  monotx_restored_types:                  0
% 3.95/1.06  sat_num_of_epr_types:                   0
% 3.95/1.06  sat_num_of_non_cyclic_types:            0
% 3.95/1.06  sat_guarded_non_collapsed_types:        0
% 3.95/1.06  num_pure_diseq_elim:                    0
% 3.95/1.06  simp_replaced_by:                       0
% 3.95/1.06  res_preprocessed:                       64
% 3.95/1.06  prep_upred:                             0
% 3.95/1.06  prep_unflattend:                        35
% 3.95/1.06  smt_new_axioms:                         0
% 3.95/1.06  pred_elim_cands:                        1
% 3.95/1.06  pred_elim:                              1
% 3.95/1.06  pred_elim_cl:                           1
% 3.95/1.06  pred_elim_cycles:                       3
% 3.95/1.06  merged_defs:                            8
% 3.95/1.06  merged_defs_ncl:                        0
% 3.95/1.06  bin_hyper_res:                          8
% 3.95/1.06  prep_cycles:                            4
% 3.95/1.06  pred_elim_time:                         0.005
% 3.95/1.06  splitting_time:                         0.
% 3.95/1.06  sem_filter_time:                        0.
% 3.95/1.06  monotx_time:                            0.001
% 3.95/1.06  subtype_inf_time:                       0.
% 3.95/1.06  
% 3.95/1.06  ------ Problem properties
% 3.95/1.06  
% 3.95/1.06  clauses:                                13
% 3.95/1.06  conjectures:                            1
% 3.95/1.06  epr:                                    5
% 3.95/1.06  horn:                                   13
% 3.95/1.06  ground:                                 5
% 3.95/1.06  unary:                                  9
% 3.95/1.06  binary:                                 4
% 3.95/1.06  lits:                                   17
% 3.95/1.06  lits_eq:                                10
% 3.95/1.06  fd_pure:                                0
% 3.95/1.06  fd_pseudo:                              0
% 3.95/1.06  fd_cond:                                0
% 3.95/1.06  fd_pseudo_cond:                         0
% 3.95/1.06  ac_symbols:                             0
% 3.95/1.06  
% 3.95/1.06  ------ Propositional Solver
% 3.95/1.06  
% 3.95/1.06  prop_solver_calls:                      32
% 3.95/1.06  prop_fast_solver_calls:                 320
% 3.95/1.06  smt_solver_calls:                       0
% 3.95/1.06  smt_fast_solver_calls:                  0
% 3.95/1.06  prop_num_of_clauses:                    2169
% 3.95/1.06  prop_preprocess_simplified:             4767
% 3.95/1.06  prop_fo_subsumed:                       1
% 3.95/1.06  prop_solver_time:                       0.
% 3.95/1.06  smt_solver_time:                        0.
% 3.95/1.06  smt_fast_solver_time:                   0.
% 3.95/1.06  prop_fast_solver_time:                  0.
% 3.95/1.06  prop_unsat_core_time:                   0.
% 3.95/1.06  
% 3.95/1.06  ------ QBF
% 3.95/1.06  
% 3.95/1.06  qbf_q_res:                              0
% 3.95/1.06  qbf_num_tautologies:                    0
% 3.95/1.06  qbf_prep_cycles:                        0
% 3.95/1.06  
% 3.95/1.06  ------ BMC1
% 3.95/1.06  
% 3.95/1.06  bmc1_current_bound:                     -1
% 3.95/1.06  bmc1_last_solved_bound:                 -1
% 3.95/1.06  bmc1_unsat_core_size:                   -1
% 3.95/1.06  bmc1_unsat_core_parents_size:           -1
% 3.95/1.06  bmc1_merge_next_fun:                    0
% 3.95/1.06  bmc1_unsat_core_clauses_time:           0.
% 3.95/1.06  
% 3.95/1.06  ------ Instantiation
% 3.95/1.06  
% 3.95/1.06  inst_num_of_clauses:                    958
% 3.95/1.06  inst_num_in_passive:                    189
% 3.95/1.06  inst_num_in_active:                     326
% 3.95/1.06  inst_num_in_unprocessed:                443
% 3.95/1.06  inst_num_of_loops:                      350
% 3.95/1.06  inst_num_of_learning_restarts:          0
% 3.95/1.06  inst_num_moves_active_passive:          20
% 3.95/1.06  inst_lit_activity:                      0
% 3.95/1.06  inst_lit_activity_moves:                0
% 3.95/1.06  inst_num_tautologies:                   0
% 3.95/1.06  inst_num_prop_implied:                  0
% 3.95/1.06  inst_num_existing_simplified:           0
% 3.95/1.06  inst_num_eq_res_simplified:             0
% 3.95/1.06  inst_num_child_elim:                    0
% 3.95/1.06  inst_num_of_dismatching_blockings:      190
% 3.95/1.06  inst_num_of_non_proper_insts:           706
% 3.95/1.06  inst_num_of_duplicates:                 0
% 3.95/1.06  inst_inst_num_from_inst_to_res:         0
% 3.95/1.06  inst_dismatching_checking_time:         0.
% 3.95/1.06  
% 3.95/1.06  ------ Resolution
% 3.95/1.06  
% 3.95/1.06  res_num_of_clauses:                     0
% 3.95/1.06  res_num_in_passive:                     0
% 3.95/1.06  res_num_in_active:                      0
% 3.95/1.06  res_num_of_loops:                       68
% 3.95/1.06  res_forward_subset_subsumed:            125
% 3.95/1.06  res_backward_subset_subsumed:           0
% 3.95/1.06  res_forward_subsumed:                   1
% 3.95/1.06  res_backward_subsumed:                  0
% 3.95/1.06  res_forward_subsumption_resolution:     0
% 3.95/1.06  res_backward_subsumption_resolution:    0
% 3.95/1.06  res_clause_to_clause_subsumption:       942
% 3.95/1.06  res_orphan_elimination:                 0
% 3.95/1.06  res_tautology_del:                      89
% 3.95/1.06  res_num_eq_res_simplified:              1
% 3.95/1.06  res_num_sel_changes:                    0
% 3.95/1.06  res_moves_from_active_to_pass:          0
% 3.95/1.06  
% 3.95/1.06  ------ Superposition
% 3.95/1.06  
% 3.95/1.06  sup_time_total:                         0.
% 3.95/1.06  sup_time_generating:                    0.
% 3.95/1.06  sup_time_sim_full:                      0.
% 3.95/1.06  sup_time_sim_immed:                     0.
% 3.95/1.06  
% 3.95/1.06  sup_num_of_clauses:                     145
% 3.95/1.06  sup_num_in_active:                      40
% 3.95/1.06  sup_num_in_passive:                     105
% 3.95/1.06  sup_num_of_loops:                       69
% 3.95/1.06  sup_fw_superposition:                   158
% 3.95/1.06  sup_bw_superposition:                   269
% 3.95/1.06  sup_immediate_simplified:               128
% 3.95/1.06  sup_given_eliminated:                   1
% 3.95/1.06  comparisons_done:                       0
% 3.95/1.06  comparisons_avoided:                    0
% 3.95/1.06  
% 3.95/1.06  ------ Simplifications
% 3.95/1.06  
% 3.95/1.06  
% 3.95/1.06  sim_fw_subset_subsumed:                 0
% 3.95/1.06  sim_bw_subset_subsumed:                 1
% 3.95/1.06  sim_fw_subsumed:                        23
% 3.95/1.06  sim_bw_subsumed:                        3
% 3.95/1.06  sim_fw_subsumption_res:                 0
% 3.95/1.06  sim_bw_subsumption_res:                 0
% 3.95/1.06  sim_tautology_del:                      0
% 3.95/1.06  sim_eq_tautology_del:                   15
% 3.95/1.06  sim_eq_res_simp:                        0
% 3.95/1.06  sim_fw_demodulated:                     67
% 3.95/1.06  sim_bw_demodulated:                     30
% 3.95/1.06  sim_light_normalised:                   64
% 3.95/1.06  sim_joinable_taut:                      0
% 3.95/1.06  sim_joinable_simp:                      0
% 3.95/1.06  sim_ac_normalised:                      0
% 3.95/1.06  sim_smt_subsumption:                    0
% 3.95/1.06  
%------------------------------------------------------------------------------
