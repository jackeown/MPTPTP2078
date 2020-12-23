%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:43 EST 2020

% Result     : Theorem 6.23s
% Output     : CNFRefutation 6.23s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 122 expanded)
%              Number of clauses        :   33 (  48 expanded)
%              Number of leaves         :   11 (  28 expanded)
%              Depth                    :   13
%              Number of atoms          :  115 ( 206 expanded)
%              Number of equality atoms :   41 (  81 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f16,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f60,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f53,f42])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK2,sK4)
        | ~ r1_tarski(sK2,sK3) )
      & r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ~ r1_xboole_0(sK2,sK4)
      | ~ r1_tarski(sK2,sK3) )
    & r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f32])).

fof(f54,plain,(
    r1_tarski(sK2,k4_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
    inference(definition_unfolding,[],[f54,f42])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f48,f42])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,
    ( ~ r1_xboole_0(sK2,sK4)
    | ~ r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_18,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_660,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1308,plain,
    ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_660])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_671,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1936,plain,
    ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1308,c_671])).

cnf(c_20,negated_conjecture,
    ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_658,plain,
    ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_796,plain,
    ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1,c_658])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_666,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1827,plain,
    ( k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) = sK2 ),
    inference(superposition,[status(thm)],[c_796,c_666])).

cnf(c_13,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_961,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1))) = X1 ),
    inference(superposition,[status(thm)],[c_1,c_13])).

cnf(c_2101,plain,
    ( k2_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),sK2)) = k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)) ),
    inference(superposition,[status(thm)],[c_1827,c_961])).

cnf(c_16,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_662,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r1_xboole_0(X0,k2_xboole_0(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2608,plain,
    ( r1_xboole_0(X0,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) != iProver_top
    | r1_xboole_0(X0,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2101,c_662])).

cnf(c_23753,plain,
    ( r1_xboole_0(sK4,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1936,c_2608])).

cnf(c_2936,plain,
    ( ~ r1_xboole_0(X0,sK2)
    | r1_xboole_0(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_10514,plain,
    ( ~ r1_xboole_0(sK4,sK2)
    | r1_xboole_0(sK2,sK4) ),
    inference(instantiation,[status(thm)],[c_2936])).

cnf(c_10518,plain,
    ( r1_xboole_0(sK4,sK2) != iProver_top
    | r1_xboole_0(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10514])).

cnf(c_10,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_665,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1318,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_665])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_667,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3107,plain,
    ( r1_tarski(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),X0) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2101,c_667])).

cnf(c_4852,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1318,c_3107])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r1_xboole_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,plain,
    ( r1_tarski(sK2,sK3) != iProver_top
    | r1_xboole_0(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23753,c_10518,c_4852,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.23/1.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.23/1.49  
% 6.23/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.23/1.49  
% 6.23/1.49  ------  iProver source info
% 6.23/1.49  
% 6.23/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.23/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.23/1.49  git: non_committed_changes: false
% 6.23/1.49  git: last_make_outside_of_git: false
% 6.23/1.49  
% 6.23/1.49  ------ 
% 6.23/1.49  
% 6.23/1.49  ------ Input Options
% 6.23/1.49  
% 6.23/1.49  --out_options                           all
% 6.23/1.49  --tptp_safe_out                         true
% 6.23/1.49  --problem_path                          ""
% 6.23/1.49  --include_path                          ""
% 6.23/1.49  --clausifier                            res/vclausify_rel
% 6.23/1.49  --clausifier_options                    --mode clausify
% 6.23/1.49  --stdin                                 false
% 6.23/1.49  --stats_out                             all
% 6.23/1.49  
% 6.23/1.49  ------ General Options
% 6.23/1.49  
% 6.23/1.49  --fof                                   false
% 6.23/1.49  --time_out_real                         305.
% 6.23/1.49  --time_out_virtual                      -1.
% 6.23/1.49  --symbol_type_check                     false
% 6.23/1.49  --clausify_out                          false
% 6.23/1.49  --sig_cnt_out                           false
% 6.23/1.49  --trig_cnt_out                          false
% 6.23/1.49  --trig_cnt_out_tolerance                1.
% 6.23/1.49  --trig_cnt_out_sk_spl                   false
% 6.23/1.49  --abstr_cl_out                          false
% 6.23/1.49  
% 6.23/1.49  ------ Global Options
% 6.23/1.49  
% 6.23/1.49  --schedule                              default
% 6.23/1.49  --add_important_lit                     false
% 6.23/1.49  --prop_solver_per_cl                    1000
% 6.23/1.49  --min_unsat_core                        false
% 6.23/1.49  --soft_assumptions                      false
% 6.23/1.49  --soft_lemma_size                       3
% 6.23/1.49  --prop_impl_unit_size                   0
% 6.23/1.49  --prop_impl_unit                        []
% 6.23/1.49  --share_sel_clauses                     true
% 6.23/1.49  --reset_solvers                         false
% 6.23/1.49  --bc_imp_inh                            [conj_cone]
% 6.23/1.49  --conj_cone_tolerance                   3.
% 6.23/1.49  --extra_neg_conj                        none
% 6.23/1.49  --large_theory_mode                     true
% 6.23/1.49  --prolific_symb_bound                   200
% 6.23/1.49  --lt_threshold                          2000
% 6.23/1.49  --clause_weak_htbl                      true
% 6.23/1.49  --gc_record_bc_elim                     false
% 6.23/1.49  
% 6.23/1.49  ------ Preprocessing Options
% 6.23/1.49  
% 6.23/1.49  --preprocessing_flag                    true
% 6.23/1.49  --time_out_prep_mult                    0.1
% 6.23/1.49  --splitting_mode                        input
% 6.23/1.49  --splitting_grd                         true
% 6.23/1.49  --splitting_cvd                         false
% 6.23/1.49  --splitting_cvd_svl                     false
% 6.23/1.49  --splitting_nvd                         32
% 6.23/1.49  --sub_typing                            true
% 6.23/1.49  --prep_gs_sim                           true
% 6.23/1.49  --prep_unflatten                        true
% 6.23/1.49  --prep_res_sim                          true
% 6.23/1.49  --prep_upred                            true
% 6.23/1.49  --prep_sem_filter                       exhaustive
% 6.23/1.49  --prep_sem_filter_out                   false
% 6.23/1.49  --pred_elim                             true
% 6.23/1.49  --res_sim_input                         true
% 6.23/1.49  --eq_ax_congr_red                       true
% 6.23/1.49  --pure_diseq_elim                       true
% 6.23/1.49  --brand_transform                       false
% 6.23/1.49  --non_eq_to_eq                          false
% 6.23/1.49  --prep_def_merge                        true
% 6.23/1.49  --prep_def_merge_prop_impl              false
% 6.23/1.49  --prep_def_merge_mbd                    true
% 6.23/1.49  --prep_def_merge_tr_red                 false
% 6.23/1.49  --prep_def_merge_tr_cl                  false
% 6.23/1.49  --smt_preprocessing                     true
% 6.23/1.49  --smt_ac_axioms                         fast
% 6.23/1.49  --preprocessed_out                      false
% 6.23/1.49  --preprocessed_stats                    false
% 6.23/1.49  
% 6.23/1.49  ------ Abstraction refinement Options
% 6.23/1.49  
% 6.23/1.49  --abstr_ref                             []
% 6.23/1.49  --abstr_ref_prep                        false
% 6.23/1.49  --abstr_ref_until_sat                   false
% 6.23/1.49  --abstr_ref_sig_restrict                funpre
% 6.23/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.23/1.49  --abstr_ref_under                       []
% 6.23/1.49  
% 6.23/1.49  ------ SAT Options
% 6.23/1.49  
% 6.23/1.49  --sat_mode                              false
% 6.23/1.49  --sat_fm_restart_options                ""
% 6.23/1.49  --sat_gr_def                            false
% 6.23/1.49  --sat_epr_types                         true
% 6.23/1.49  --sat_non_cyclic_types                  false
% 6.23/1.49  --sat_finite_models                     false
% 6.23/1.49  --sat_fm_lemmas                         false
% 6.23/1.49  --sat_fm_prep                           false
% 6.23/1.49  --sat_fm_uc_incr                        true
% 6.23/1.49  --sat_out_model                         small
% 6.23/1.49  --sat_out_clauses                       false
% 6.23/1.49  
% 6.23/1.49  ------ QBF Options
% 6.23/1.49  
% 6.23/1.49  --qbf_mode                              false
% 6.23/1.49  --qbf_elim_univ                         false
% 6.23/1.49  --qbf_dom_inst                          none
% 6.23/1.49  --qbf_dom_pre_inst                      false
% 6.23/1.49  --qbf_sk_in                             false
% 6.23/1.49  --qbf_pred_elim                         true
% 6.23/1.49  --qbf_split                             512
% 6.23/1.49  
% 6.23/1.49  ------ BMC1 Options
% 6.23/1.49  
% 6.23/1.49  --bmc1_incremental                      false
% 6.23/1.49  --bmc1_axioms                           reachable_all
% 6.23/1.49  --bmc1_min_bound                        0
% 6.23/1.49  --bmc1_max_bound                        -1
% 6.23/1.49  --bmc1_max_bound_default                -1
% 6.23/1.49  --bmc1_symbol_reachability              true
% 6.23/1.49  --bmc1_property_lemmas                  false
% 6.23/1.49  --bmc1_k_induction                      false
% 6.23/1.49  --bmc1_non_equiv_states                 false
% 6.23/1.49  --bmc1_deadlock                         false
% 6.23/1.49  --bmc1_ucm                              false
% 6.23/1.49  --bmc1_add_unsat_core                   none
% 6.23/1.49  --bmc1_unsat_core_children              false
% 6.23/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.23/1.49  --bmc1_out_stat                         full
% 6.23/1.49  --bmc1_ground_init                      false
% 6.23/1.49  --bmc1_pre_inst_next_state              false
% 6.23/1.49  --bmc1_pre_inst_state                   false
% 6.23/1.49  --bmc1_pre_inst_reach_state             false
% 6.23/1.49  --bmc1_out_unsat_core                   false
% 6.23/1.49  --bmc1_aig_witness_out                  false
% 6.23/1.49  --bmc1_verbose                          false
% 6.23/1.49  --bmc1_dump_clauses_tptp                false
% 6.23/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.23/1.49  --bmc1_dump_file                        -
% 6.23/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.23/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.23/1.49  --bmc1_ucm_extend_mode                  1
% 6.23/1.49  --bmc1_ucm_init_mode                    2
% 6.23/1.49  --bmc1_ucm_cone_mode                    none
% 6.23/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.23/1.49  --bmc1_ucm_relax_model                  4
% 6.23/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.23/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.23/1.49  --bmc1_ucm_layered_model                none
% 6.23/1.49  --bmc1_ucm_max_lemma_size               10
% 6.23/1.49  
% 6.23/1.49  ------ AIG Options
% 6.23/1.49  
% 6.23/1.49  --aig_mode                              false
% 6.23/1.49  
% 6.23/1.49  ------ Instantiation Options
% 6.23/1.49  
% 6.23/1.49  --instantiation_flag                    true
% 6.23/1.49  --inst_sos_flag                         false
% 6.23/1.49  --inst_sos_phase                        true
% 6.23/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.23/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.23/1.49  --inst_lit_sel_side                     num_symb
% 6.23/1.49  --inst_solver_per_active                1400
% 6.23/1.49  --inst_solver_calls_frac                1.
% 6.23/1.49  --inst_passive_queue_type               priority_queues
% 6.23/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.23/1.49  --inst_passive_queues_freq              [25;2]
% 6.23/1.49  --inst_dismatching                      true
% 6.23/1.49  --inst_eager_unprocessed_to_passive     true
% 6.23/1.49  --inst_prop_sim_given                   true
% 6.23/1.49  --inst_prop_sim_new                     false
% 6.23/1.49  --inst_subs_new                         false
% 6.23/1.49  --inst_eq_res_simp                      false
% 6.23/1.49  --inst_subs_given                       false
% 6.23/1.49  --inst_orphan_elimination               true
% 6.23/1.49  --inst_learning_loop_flag               true
% 6.23/1.49  --inst_learning_start                   3000
% 6.23/1.49  --inst_learning_factor                  2
% 6.23/1.49  --inst_start_prop_sim_after_learn       3
% 6.23/1.49  --inst_sel_renew                        solver
% 6.23/1.49  --inst_lit_activity_flag                true
% 6.23/1.49  --inst_restr_to_given                   false
% 6.23/1.49  --inst_activity_threshold               500
% 6.23/1.49  --inst_out_proof                        true
% 6.23/1.49  
% 6.23/1.49  ------ Resolution Options
% 6.23/1.49  
% 6.23/1.49  --resolution_flag                       true
% 6.23/1.49  --res_lit_sel                           adaptive
% 6.23/1.49  --res_lit_sel_side                      none
% 6.23/1.49  --res_ordering                          kbo
% 6.23/1.49  --res_to_prop_solver                    active
% 6.23/1.49  --res_prop_simpl_new                    false
% 6.23/1.49  --res_prop_simpl_given                  true
% 6.23/1.49  --res_passive_queue_type                priority_queues
% 6.23/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.23/1.49  --res_passive_queues_freq               [15;5]
% 6.23/1.49  --res_forward_subs                      full
% 6.23/1.49  --res_backward_subs                     full
% 6.23/1.49  --res_forward_subs_resolution           true
% 6.23/1.49  --res_backward_subs_resolution          true
% 6.23/1.49  --res_orphan_elimination                true
% 6.23/1.49  --res_time_limit                        2.
% 6.23/1.49  --res_out_proof                         true
% 6.23/1.49  
% 6.23/1.49  ------ Superposition Options
% 6.23/1.49  
% 6.23/1.49  --superposition_flag                    true
% 6.23/1.49  --sup_passive_queue_type                priority_queues
% 6.23/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.23/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.23/1.49  --demod_completeness_check              fast
% 6.23/1.49  --demod_use_ground                      true
% 6.23/1.49  --sup_to_prop_solver                    passive
% 6.23/1.49  --sup_prop_simpl_new                    true
% 6.23/1.49  --sup_prop_simpl_given                  true
% 6.23/1.49  --sup_fun_splitting                     false
% 6.23/1.49  --sup_smt_interval                      50000
% 6.23/1.49  
% 6.23/1.49  ------ Superposition Simplification Setup
% 6.23/1.49  
% 6.23/1.49  --sup_indices_passive                   []
% 6.23/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.23/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.23/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.23/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.23/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.23/1.49  --sup_full_bw                           [BwDemod]
% 6.23/1.49  --sup_immed_triv                        [TrivRules]
% 6.23/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.23/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.23/1.49  --sup_immed_bw_main                     []
% 6.23/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.23/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.23/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.23/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.23/1.49  
% 6.23/1.49  ------ Combination Options
% 6.23/1.49  
% 6.23/1.49  --comb_res_mult                         3
% 6.23/1.49  --comb_sup_mult                         2
% 6.23/1.49  --comb_inst_mult                        10
% 6.23/1.49  
% 6.23/1.49  ------ Debug Options
% 6.23/1.49  
% 6.23/1.49  --dbg_backtrace                         false
% 6.23/1.49  --dbg_dump_prop_clauses                 false
% 6.23/1.49  --dbg_dump_prop_clauses_file            -
% 6.23/1.49  --dbg_out_stat                          false
% 6.23/1.49  ------ Parsing...
% 6.23/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.23/1.49  
% 6.23/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.23/1.49  
% 6.23/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.23/1.49  
% 6.23/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.23/1.49  ------ Proving...
% 6.23/1.49  ------ Problem Properties 
% 6.23/1.49  
% 6.23/1.49  
% 6.23/1.49  clauses                                 21
% 6.23/1.49  conjectures                             2
% 6.23/1.49  EPR                                     3
% 6.23/1.49  Horn                                    19
% 6.23/1.49  unary                                   9
% 6.23/1.49  binary                                  11
% 6.23/1.49  lits                                    34
% 6.23/1.49  lits eq                                 9
% 6.23/1.49  fd_pure                                 0
% 6.23/1.49  fd_pseudo                               0
% 6.23/1.49  fd_cond                                 1
% 6.23/1.49  fd_pseudo_cond                          0
% 6.23/1.49  AC symbols                              0
% 6.23/1.49  
% 6.23/1.49  ------ Schedule dynamic 5 is on 
% 6.23/1.49  
% 6.23/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.23/1.49  
% 6.23/1.49  
% 6.23/1.49  ------ 
% 6.23/1.49  Current options:
% 6.23/1.49  ------ 
% 6.23/1.49  
% 6.23/1.49  ------ Input Options
% 6.23/1.49  
% 6.23/1.49  --out_options                           all
% 6.23/1.49  --tptp_safe_out                         true
% 6.23/1.49  --problem_path                          ""
% 6.23/1.49  --include_path                          ""
% 6.23/1.49  --clausifier                            res/vclausify_rel
% 6.23/1.49  --clausifier_options                    --mode clausify
% 6.23/1.49  --stdin                                 false
% 6.23/1.49  --stats_out                             all
% 6.23/1.49  
% 6.23/1.49  ------ General Options
% 6.23/1.49  
% 6.23/1.49  --fof                                   false
% 6.23/1.49  --time_out_real                         305.
% 6.23/1.49  --time_out_virtual                      -1.
% 6.23/1.49  --symbol_type_check                     false
% 6.23/1.49  --clausify_out                          false
% 6.23/1.49  --sig_cnt_out                           false
% 6.23/1.49  --trig_cnt_out                          false
% 6.23/1.49  --trig_cnt_out_tolerance                1.
% 6.23/1.49  --trig_cnt_out_sk_spl                   false
% 6.23/1.49  --abstr_cl_out                          false
% 6.23/1.49  
% 6.23/1.49  ------ Global Options
% 6.23/1.49  
% 6.23/1.49  --schedule                              default
% 6.23/1.49  --add_important_lit                     false
% 6.23/1.49  --prop_solver_per_cl                    1000
% 6.23/1.49  --min_unsat_core                        false
% 6.23/1.49  --soft_assumptions                      false
% 6.23/1.49  --soft_lemma_size                       3
% 6.23/1.49  --prop_impl_unit_size                   0
% 6.23/1.49  --prop_impl_unit                        []
% 6.23/1.49  --share_sel_clauses                     true
% 6.23/1.49  --reset_solvers                         false
% 6.23/1.49  --bc_imp_inh                            [conj_cone]
% 6.23/1.49  --conj_cone_tolerance                   3.
% 6.23/1.49  --extra_neg_conj                        none
% 6.23/1.49  --large_theory_mode                     true
% 6.23/1.49  --prolific_symb_bound                   200
% 6.23/1.49  --lt_threshold                          2000
% 6.23/1.49  --clause_weak_htbl                      true
% 6.23/1.49  --gc_record_bc_elim                     false
% 6.23/1.49  
% 6.23/1.49  ------ Preprocessing Options
% 6.23/1.49  
% 6.23/1.49  --preprocessing_flag                    true
% 6.23/1.49  --time_out_prep_mult                    0.1
% 6.23/1.49  --splitting_mode                        input
% 6.23/1.49  --splitting_grd                         true
% 6.23/1.49  --splitting_cvd                         false
% 6.23/1.49  --splitting_cvd_svl                     false
% 6.23/1.49  --splitting_nvd                         32
% 6.23/1.49  --sub_typing                            true
% 6.23/1.49  --prep_gs_sim                           true
% 6.23/1.49  --prep_unflatten                        true
% 6.23/1.49  --prep_res_sim                          true
% 6.23/1.49  --prep_upred                            true
% 6.23/1.49  --prep_sem_filter                       exhaustive
% 6.23/1.49  --prep_sem_filter_out                   false
% 6.23/1.49  --pred_elim                             true
% 6.23/1.49  --res_sim_input                         true
% 6.23/1.49  --eq_ax_congr_red                       true
% 6.23/1.49  --pure_diseq_elim                       true
% 6.23/1.49  --brand_transform                       false
% 6.23/1.49  --non_eq_to_eq                          false
% 6.23/1.49  --prep_def_merge                        true
% 6.23/1.49  --prep_def_merge_prop_impl              false
% 6.23/1.49  --prep_def_merge_mbd                    true
% 6.23/1.49  --prep_def_merge_tr_red                 false
% 6.23/1.49  --prep_def_merge_tr_cl                  false
% 6.23/1.49  --smt_preprocessing                     true
% 6.23/1.49  --smt_ac_axioms                         fast
% 6.23/1.49  --preprocessed_out                      false
% 6.23/1.49  --preprocessed_stats                    false
% 6.23/1.49  
% 6.23/1.49  ------ Abstraction refinement Options
% 6.23/1.49  
% 6.23/1.49  --abstr_ref                             []
% 6.23/1.49  --abstr_ref_prep                        false
% 6.23/1.49  --abstr_ref_until_sat                   false
% 6.23/1.49  --abstr_ref_sig_restrict                funpre
% 6.23/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.23/1.49  --abstr_ref_under                       []
% 6.23/1.49  
% 6.23/1.49  ------ SAT Options
% 6.23/1.49  
% 6.23/1.49  --sat_mode                              false
% 6.23/1.49  --sat_fm_restart_options                ""
% 6.23/1.49  --sat_gr_def                            false
% 6.23/1.49  --sat_epr_types                         true
% 6.23/1.49  --sat_non_cyclic_types                  false
% 6.23/1.49  --sat_finite_models                     false
% 6.23/1.49  --sat_fm_lemmas                         false
% 6.23/1.49  --sat_fm_prep                           false
% 6.23/1.49  --sat_fm_uc_incr                        true
% 6.23/1.49  --sat_out_model                         small
% 6.23/1.49  --sat_out_clauses                       false
% 6.23/1.49  
% 6.23/1.49  ------ QBF Options
% 6.23/1.49  
% 6.23/1.49  --qbf_mode                              false
% 6.23/1.49  --qbf_elim_univ                         false
% 6.23/1.49  --qbf_dom_inst                          none
% 6.23/1.49  --qbf_dom_pre_inst                      false
% 6.23/1.49  --qbf_sk_in                             false
% 6.23/1.49  --qbf_pred_elim                         true
% 6.23/1.49  --qbf_split                             512
% 6.23/1.49  
% 6.23/1.49  ------ BMC1 Options
% 6.23/1.49  
% 6.23/1.49  --bmc1_incremental                      false
% 6.23/1.49  --bmc1_axioms                           reachable_all
% 6.23/1.49  --bmc1_min_bound                        0
% 6.23/1.49  --bmc1_max_bound                        -1
% 6.23/1.49  --bmc1_max_bound_default                -1
% 6.23/1.49  --bmc1_symbol_reachability              true
% 6.23/1.49  --bmc1_property_lemmas                  false
% 6.23/1.49  --bmc1_k_induction                      false
% 6.23/1.49  --bmc1_non_equiv_states                 false
% 6.23/1.49  --bmc1_deadlock                         false
% 6.23/1.49  --bmc1_ucm                              false
% 6.23/1.49  --bmc1_add_unsat_core                   none
% 6.23/1.49  --bmc1_unsat_core_children              false
% 6.23/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.23/1.49  --bmc1_out_stat                         full
% 6.23/1.49  --bmc1_ground_init                      false
% 6.23/1.49  --bmc1_pre_inst_next_state              false
% 6.23/1.49  --bmc1_pre_inst_state                   false
% 6.23/1.49  --bmc1_pre_inst_reach_state             false
% 6.23/1.49  --bmc1_out_unsat_core                   false
% 6.23/1.49  --bmc1_aig_witness_out                  false
% 6.23/1.49  --bmc1_verbose                          false
% 6.23/1.49  --bmc1_dump_clauses_tptp                false
% 6.23/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.23/1.49  --bmc1_dump_file                        -
% 6.23/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.23/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.23/1.49  --bmc1_ucm_extend_mode                  1
% 6.23/1.49  --bmc1_ucm_init_mode                    2
% 6.23/1.49  --bmc1_ucm_cone_mode                    none
% 6.23/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.23/1.49  --bmc1_ucm_relax_model                  4
% 6.23/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.23/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.23/1.49  --bmc1_ucm_layered_model                none
% 6.23/1.49  --bmc1_ucm_max_lemma_size               10
% 6.23/1.49  
% 6.23/1.49  ------ AIG Options
% 6.23/1.49  
% 6.23/1.49  --aig_mode                              false
% 6.23/1.49  
% 6.23/1.49  ------ Instantiation Options
% 6.23/1.49  
% 6.23/1.49  --instantiation_flag                    true
% 6.23/1.49  --inst_sos_flag                         false
% 6.23/1.49  --inst_sos_phase                        true
% 6.23/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.23/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.23/1.49  --inst_lit_sel_side                     none
% 6.23/1.49  --inst_solver_per_active                1400
% 6.23/1.49  --inst_solver_calls_frac                1.
% 6.23/1.49  --inst_passive_queue_type               priority_queues
% 6.23/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.23/1.49  --inst_passive_queues_freq              [25;2]
% 6.23/1.49  --inst_dismatching                      true
% 6.23/1.49  --inst_eager_unprocessed_to_passive     true
% 6.23/1.49  --inst_prop_sim_given                   true
% 6.23/1.49  --inst_prop_sim_new                     false
% 6.23/1.49  --inst_subs_new                         false
% 6.23/1.49  --inst_eq_res_simp                      false
% 6.23/1.49  --inst_subs_given                       false
% 6.23/1.49  --inst_orphan_elimination               true
% 6.23/1.49  --inst_learning_loop_flag               true
% 6.23/1.49  --inst_learning_start                   3000
% 6.23/1.49  --inst_learning_factor                  2
% 6.23/1.49  --inst_start_prop_sim_after_learn       3
% 6.23/1.49  --inst_sel_renew                        solver
% 6.23/1.49  --inst_lit_activity_flag                true
% 6.23/1.49  --inst_restr_to_given                   false
% 6.23/1.49  --inst_activity_threshold               500
% 6.23/1.49  --inst_out_proof                        true
% 6.23/1.49  
% 6.23/1.49  ------ Resolution Options
% 6.23/1.49  
% 6.23/1.49  --resolution_flag                       false
% 6.23/1.49  --res_lit_sel                           adaptive
% 6.23/1.49  --res_lit_sel_side                      none
% 6.23/1.49  --res_ordering                          kbo
% 6.23/1.49  --res_to_prop_solver                    active
% 6.23/1.49  --res_prop_simpl_new                    false
% 6.23/1.49  --res_prop_simpl_given                  true
% 6.23/1.49  --res_passive_queue_type                priority_queues
% 6.23/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.23/1.49  --res_passive_queues_freq               [15;5]
% 6.23/1.49  --res_forward_subs                      full
% 6.23/1.49  --res_backward_subs                     full
% 6.23/1.49  --res_forward_subs_resolution           true
% 6.23/1.49  --res_backward_subs_resolution          true
% 6.23/1.49  --res_orphan_elimination                true
% 6.23/1.49  --res_time_limit                        2.
% 6.23/1.49  --res_out_proof                         true
% 6.23/1.49  
% 6.23/1.49  ------ Superposition Options
% 6.23/1.49  
% 6.23/1.49  --superposition_flag                    true
% 6.23/1.49  --sup_passive_queue_type                priority_queues
% 6.23/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.23/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.23/1.49  --demod_completeness_check              fast
% 6.23/1.49  --demod_use_ground                      true
% 6.23/1.49  --sup_to_prop_solver                    passive
% 6.23/1.49  --sup_prop_simpl_new                    true
% 6.23/1.49  --sup_prop_simpl_given                  true
% 6.23/1.49  --sup_fun_splitting                     false
% 6.23/1.49  --sup_smt_interval                      50000
% 6.23/1.49  
% 6.23/1.49  ------ Superposition Simplification Setup
% 6.23/1.49  
% 6.23/1.49  --sup_indices_passive                   []
% 6.23/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.23/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.23/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.23/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.23/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.23/1.49  --sup_full_bw                           [BwDemod]
% 6.23/1.49  --sup_immed_triv                        [TrivRules]
% 6.23/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.23/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.23/1.49  --sup_immed_bw_main                     []
% 6.23/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.23/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.23/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.23/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.23/1.49  
% 6.23/1.49  ------ Combination Options
% 6.23/1.49  
% 6.23/1.49  --comb_res_mult                         3
% 6.23/1.49  --comb_sup_mult                         2
% 6.23/1.49  --comb_inst_mult                        10
% 6.23/1.49  
% 6.23/1.49  ------ Debug Options
% 6.23/1.49  
% 6.23/1.49  --dbg_backtrace                         false
% 6.23/1.49  --dbg_dump_prop_clauses                 false
% 6.23/1.49  --dbg_dump_prop_clauses_file            -
% 6.23/1.49  --dbg_out_stat                          false
% 6.23/1.49  
% 6.23/1.49  
% 6.23/1.49  
% 6.23/1.49  
% 6.23/1.49  ------ Proving...
% 6.23/1.49  
% 6.23/1.49  
% 6.23/1.49  % SZS status Theorem for theBenchmark.p
% 6.23/1.49  
% 6.23/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.23/1.49  
% 6.23/1.49  fof(f2,axiom,(
% 6.23/1.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.23/1.49  
% 6.23/1.49  fof(f35,plain,(
% 6.23/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.23/1.49    inference(cnf_transformation,[],[f2])).
% 6.23/1.49  
% 6.23/1.49  fof(f16,axiom,(
% 6.23/1.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 6.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.23/1.49  
% 6.23/1.49  fof(f53,plain,(
% 6.23/1.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 6.23/1.49    inference(cnf_transformation,[],[f16])).
% 6.23/1.49  
% 6.23/1.49  fof(f7,axiom,(
% 6.23/1.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.23/1.49  
% 6.23/1.49  fof(f42,plain,(
% 6.23/1.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.23/1.49    inference(cnf_transformation,[],[f7])).
% 6.23/1.49  
% 6.23/1.49  fof(f60,plain,(
% 6.23/1.49    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 6.23/1.49    inference(definition_unfolding,[],[f53,f42])).
% 6.23/1.49  
% 6.23/1.49  fof(f4,axiom,(
% 6.23/1.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 6.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.23/1.49  
% 6.23/1.49  fof(f20,plain,(
% 6.23/1.49    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 6.23/1.49    inference(ennf_transformation,[],[f4])).
% 6.23/1.49  
% 6.23/1.49  fof(f38,plain,(
% 6.23/1.49    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 6.23/1.49    inference(cnf_transformation,[],[f20])).
% 6.23/1.49  
% 6.23/1.49  fof(f17,conjecture,(
% 6.23/1.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 6.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.23/1.49  
% 6.23/1.49  fof(f18,negated_conjecture,(
% 6.23/1.49    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 6.23/1.49    inference(negated_conjecture,[],[f17])).
% 6.23/1.49  
% 6.23/1.49  fof(f26,plain,(
% 6.23/1.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 6.23/1.49    inference(ennf_transformation,[],[f18])).
% 6.23/1.49  
% 6.23/1.49  fof(f32,plain,(
% 6.23/1.49    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK2,sK4) | ~r1_tarski(sK2,sK3)) & r1_tarski(sK2,k4_xboole_0(sK3,sK4)))),
% 6.23/1.49    introduced(choice_axiom,[])).
% 6.23/1.49  
% 6.23/1.49  fof(f33,plain,(
% 6.23/1.49    (~r1_xboole_0(sK2,sK4) | ~r1_tarski(sK2,sK3)) & r1_tarski(sK2,k4_xboole_0(sK3,sK4))),
% 6.23/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f26,f32])).
% 6.23/1.49  
% 6.23/1.49  fof(f54,plain,(
% 6.23/1.49    r1_tarski(sK2,k4_xboole_0(sK3,sK4))),
% 6.23/1.49    inference(cnf_transformation,[],[f33])).
% 6.23/1.49  
% 6.23/1.49  fof(f61,plain,(
% 6.23/1.49    r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4)))),
% 6.23/1.49    inference(definition_unfolding,[],[f54,f42])).
% 6.23/1.49  
% 6.23/1.49  fof(f9,axiom,(
% 6.23/1.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.23/1.49  
% 6.23/1.49  fof(f24,plain,(
% 6.23/1.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.23/1.49    inference(ennf_transformation,[],[f9])).
% 6.23/1.49  
% 6.23/1.49  fof(f44,plain,(
% 6.23/1.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 6.23/1.49    inference(cnf_transformation,[],[f24])).
% 6.23/1.49  
% 6.23/1.49  fof(f13,axiom,(
% 6.23/1.49    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 6.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.23/1.49  
% 6.23/1.49  fof(f48,plain,(
% 6.23/1.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 6.23/1.49    inference(cnf_transformation,[],[f13])).
% 6.23/1.49  
% 6.23/1.49  fof(f59,plain,(
% 6.23/1.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = X0) )),
% 6.23/1.49    inference(definition_unfolding,[],[f48,f42])).
% 6.23/1.49  
% 6.23/1.49  fof(f15,axiom,(
% 6.23/1.49    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 6.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.23/1.49  
% 6.23/1.49  fof(f25,plain,(
% 6.23/1.49    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 6.23/1.49    inference(ennf_transformation,[],[f15])).
% 6.23/1.49  
% 6.23/1.49  fof(f51,plain,(
% 6.23/1.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 6.23/1.49    inference(cnf_transformation,[],[f25])).
% 6.23/1.49  
% 6.23/1.49  fof(f10,axiom,(
% 6.23/1.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 6.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.23/1.49  
% 6.23/1.49  fof(f45,plain,(
% 6.23/1.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.23/1.49    inference(cnf_transformation,[],[f10])).
% 6.23/1.49  
% 6.23/1.49  fof(f56,plain,(
% 6.23/1.49    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 6.23/1.49    inference(definition_unfolding,[],[f45,f42])).
% 6.23/1.49  
% 6.23/1.49  fof(f8,axiom,(
% 6.23/1.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 6.23/1.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 6.23/1.49  
% 6.23/1.49  fof(f23,plain,(
% 6.23/1.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 6.23/1.49    inference(ennf_transformation,[],[f8])).
% 6.23/1.49  
% 6.23/1.49  fof(f43,plain,(
% 6.23/1.49    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 6.23/1.49    inference(cnf_transformation,[],[f23])).
% 6.23/1.49  
% 6.23/1.49  fof(f55,plain,(
% 6.23/1.49    ~r1_xboole_0(sK2,sK4) | ~r1_tarski(sK2,sK3)),
% 6.23/1.49    inference(cnf_transformation,[],[f33])).
% 6.23/1.49  
% 6.23/1.49  cnf(c_1,plain,
% 6.23/1.49      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 6.23/1.49      inference(cnf_transformation,[],[f35]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_18,plain,
% 6.23/1.49      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
% 6.23/1.49      inference(cnf_transformation,[],[f60]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_660,plain,
% 6.23/1.49      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) = iProver_top ),
% 6.23/1.49      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_1308,plain,
% 6.23/1.49      ( r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X1) = iProver_top ),
% 6.23/1.49      inference(superposition,[status(thm)],[c_1,c_660]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_4,plain,
% 6.23/1.49      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 6.23/1.49      inference(cnf_transformation,[],[f38]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_671,plain,
% 6.23/1.49      ( r1_xboole_0(X0,X1) != iProver_top
% 6.23/1.49      | r1_xboole_0(X1,X0) = iProver_top ),
% 6.23/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_1936,plain,
% 6.23/1.49      ( r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) = iProver_top ),
% 6.23/1.49      inference(superposition,[status(thm)],[c_1308,c_671]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_20,negated_conjecture,
% 6.23/1.49      ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) ),
% 6.23/1.49      inference(cnf_transformation,[],[f61]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_658,plain,
% 6.23/1.49      ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK3,sK4))) = iProver_top ),
% 6.23/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_796,plain,
% 6.23/1.49      ( r1_tarski(sK2,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) = iProver_top ),
% 6.23/1.49      inference(demodulation,[status(thm)],[c_1,c_658]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_9,plain,
% 6.23/1.49      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 6.23/1.49      inference(cnf_transformation,[],[f44]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_666,plain,
% 6.23/1.49      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 6.23/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_1827,plain,
% 6.23/1.49      ( k3_xboole_0(sK2,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) = sK2 ),
% 6.23/1.49      inference(superposition,[status(thm)],[c_796,c_666]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_13,plain,
% 6.23/1.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = X0 ),
% 6.23/1.49      inference(cnf_transformation,[],[f59]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_961,plain,
% 6.23/1.49      ( k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X1,k3_xboole_0(X0,X1))) = X1 ),
% 6.23/1.49      inference(superposition,[status(thm)],[c_1,c_13]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_2101,plain,
% 6.23/1.49      ( k2_xboole_0(sK2,k5_xboole_0(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),sK2)) = k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)) ),
% 6.23/1.49      inference(superposition,[status(thm)],[c_1827,c_961]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_16,plain,
% 6.23/1.49      ( r1_xboole_0(X0,X1) | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 6.23/1.49      inference(cnf_transformation,[],[f51]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_662,plain,
% 6.23/1.49      ( r1_xboole_0(X0,X1) = iProver_top
% 6.23/1.49      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) != iProver_top ),
% 6.23/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_2608,plain,
% 6.23/1.49      ( r1_xboole_0(X0,k5_xboole_0(sK3,k3_xboole_0(sK4,sK3))) != iProver_top
% 6.23/1.49      | r1_xboole_0(X0,sK2) = iProver_top ),
% 6.23/1.49      inference(superposition,[status(thm)],[c_2101,c_662]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_23753,plain,
% 6.23/1.49      ( r1_xboole_0(sK4,sK2) = iProver_top ),
% 6.23/1.49      inference(superposition,[status(thm)],[c_1936,c_2608]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_2936,plain,
% 6.23/1.49      ( ~ r1_xboole_0(X0,sK2) | r1_xboole_0(sK2,X0) ),
% 6.23/1.49      inference(instantiation,[status(thm)],[c_4]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_10514,plain,
% 6.23/1.49      ( ~ r1_xboole_0(sK4,sK2) | r1_xboole_0(sK2,sK4) ),
% 6.23/1.49      inference(instantiation,[status(thm)],[c_2936]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_10518,plain,
% 6.23/1.49      ( r1_xboole_0(sK4,sK2) != iProver_top
% 6.23/1.49      | r1_xboole_0(sK2,sK4) = iProver_top ),
% 6.23/1.49      inference(predicate_to_equality,[status(thm)],[c_10514]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_10,plain,
% 6.23/1.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 6.23/1.49      inference(cnf_transformation,[],[f56]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_665,plain,
% 6.23/1.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 6.23/1.49      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_1318,plain,
% 6.23/1.49      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) = iProver_top ),
% 6.23/1.49      inference(superposition,[status(thm)],[c_1,c_665]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_8,plain,
% 6.23/1.49      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 6.23/1.49      inference(cnf_transformation,[],[f43]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_667,plain,
% 6.23/1.49      ( r1_tarski(X0,X1) = iProver_top
% 6.23/1.49      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 6.23/1.49      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_3107,plain,
% 6.23/1.49      ( r1_tarski(k5_xboole_0(sK3,k3_xboole_0(sK4,sK3)),X0) != iProver_top
% 6.23/1.49      | r1_tarski(sK2,X0) = iProver_top ),
% 6.23/1.49      inference(superposition,[status(thm)],[c_2101,c_667]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_4852,plain,
% 6.23/1.49      ( r1_tarski(sK2,sK3) = iProver_top ),
% 6.23/1.49      inference(superposition,[status(thm)],[c_1318,c_3107]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_19,negated_conjecture,
% 6.23/1.49      ( ~ r1_tarski(sK2,sK3) | ~ r1_xboole_0(sK2,sK4) ),
% 6.23/1.49      inference(cnf_transformation,[],[f55]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(c_22,plain,
% 6.23/1.49      ( r1_tarski(sK2,sK3) != iProver_top
% 6.23/1.49      | r1_xboole_0(sK2,sK4) != iProver_top ),
% 6.23/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 6.23/1.49  
% 6.23/1.49  cnf(contradiction,plain,
% 6.23/1.49      ( $false ),
% 6.23/1.49      inference(minisat,[status(thm)],[c_23753,c_10518,c_4852,c_22]) ).
% 6.23/1.49  
% 6.23/1.49  
% 6.23/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 6.23/1.49  
% 6.23/1.49  ------                               Statistics
% 6.23/1.49  
% 6.23/1.49  ------ General
% 6.23/1.49  
% 6.23/1.49  abstr_ref_over_cycles:                  0
% 6.23/1.49  abstr_ref_under_cycles:                 0
% 6.23/1.49  gc_basic_clause_elim:                   0
% 6.23/1.49  forced_gc_time:                         0
% 6.23/1.49  parsing_time:                           0.009
% 6.23/1.49  unif_index_cands_time:                  0.
% 6.23/1.49  unif_index_add_time:                    0.
% 6.23/1.49  orderings_time:                         0.
% 6.23/1.49  out_proof_time:                         0.006
% 6.23/1.49  total_time:                             0.614
% 6.23/1.49  num_of_symbols:                         43
% 6.23/1.49  num_of_terms:                           16003
% 6.23/1.49  
% 6.23/1.49  ------ Preprocessing
% 6.23/1.49  
% 6.23/1.49  num_of_splits:                          0
% 6.23/1.49  num_of_split_atoms:                     0
% 6.23/1.49  num_of_reused_defs:                     0
% 6.23/1.49  num_eq_ax_congr_red:                    6
% 6.23/1.49  num_of_sem_filtered_clauses:            1
% 6.23/1.49  num_of_subtypes:                        0
% 6.23/1.49  monotx_restored_types:                  0
% 6.23/1.49  sat_num_of_epr_types:                   0
% 6.23/1.49  sat_num_of_non_cyclic_types:            0
% 6.23/1.49  sat_guarded_non_collapsed_types:        0
% 6.23/1.49  num_pure_diseq_elim:                    0
% 6.23/1.49  simp_replaced_by:                       0
% 6.23/1.49  res_preprocessed:                       80
% 6.23/1.49  prep_upred:                             0
% 6.23/1.49  prep_unflattend:                        3
% 6.23/1.49  smt_new_axioms:                         0
% 6.23/1.49  pred_elim_cands:                        3
% 6.23/1.49  pred_elim:                              0
% 6.23/1.49  pred_elim_cl:                           0
% 6.23/1.49  pred_elim_cycles:                       1
% 6.23/1.49  merged_defs:                            6
% 6.23/1.49  merged_defs_ncl:                        0
% 6.23/1.49  bin_hyper_res:                          6
% 6.23/1.49  prep_cycles:                            3
% 6.23/1.49  pred_elim_time:                         0.
% 6.23/1.49  splitting_time:                         0.
% 6.23/1.49  sem_filter_time:                        0.
% 6.23/1.49  monotx_time:                            0.
% 6.23/1.49  subtype_inf_time:                       0.
% 6.23/1.49  
% 6.23/1.49  ------ Problem properties
% 6.23/1.49  
% 6.23/1.49  clauses:                                21
% 6.23/1.49  conjectures:                            2
% 6.23/1.49  epr:                                    3
% 6.23/1.49  horn:                                   19
% 6.23/1.49  ground:                                 2
% 6.23/1.49  unary:                                  9
% 6.23/1.49  binary:                                 11
% 6.23/1.49  lits:                                   34
% 6.23/1.49  lits_eq:                                9
% 6.23/1.49  fd_pure:                                0
% 6.23/1.49  fd_pseudo:                              0
% 6.23/1.49  fd_cond:                                1
% 6.23/1.49  fd_pseudo_cond:                         0
% 6.23/1.49  ac_symbols:                             0
% 6.23/1.49  
% 6.23/1.49  ------ Propositional Solver
% 6.23/1.49  
% 6.23/1.49  prop_solver_calls:                      27
% 6.23/1.49  prop_fast_solver_calls:                 615
% 6.23/1.49  smt_solver_calls:                       0
% 6.23/1.49  smt_fast_solver_calls:                  0
% 6.23/1.49  prop_num_of_clauses:                    8063
% 6.23/1.49  prop_preprocess_simplified:             15315
% 6.23/1.49  prop_fo_subsumed:                       4
% 6.23/1.49  prop_solver_time:                       0.
% 6.23/1.49  smt_solver_time:                        0.
% 6.23/1.49  smt_fast_solver_time:                   0.
% 6.23/1.49  prop_fast_solver_time:                  0.
% 6.23/1.49  prop_unsat_core_time:                   0.001
% 6.23/1.49  
% 6.23/1.49  ------ QBF
% 6.23/1.49  
% 6.23/1.49  qbf_q_res:                              0
% 6.23/1.49  qbf_num_tautologies:                    0
% 6.23/1.49  qbf_prep_cycles:                        0
% 6.23/1.49  
% 6.23/1.49  ------ BMC1
% 6.23/1.49  
% 6.23/1.49  bmc1_current_bound:                     -1
% 6.23/1.49  bmc1_last_solved_bound:                 -1
% 6.23/1.49  bmc1_unsat_core_size:                   -1
% 6.23/1.49  bmc1_unsat_core_parents_size:           -1
% 6.23/1.49  bmc1_merge_next_fun:                    0
% 6.23/1.49  bmc1_unsat_core_clauses_time:           0.
% 6.23/1.49  
% 6.23/1.49  ------ Instantiation
% 6.23/1.49  
% 6.23/1.49  inst_num_of_clauses:                    2298
% 6.23/1.49  inst_num_in_passive:                    1389
% 6.23/1.49  inst_num_in_active:                     762
% 6.23/1.49  inst_num_in_unprocessed:                149
% 6.23/1.49  inst_num_of_loops:                      930
% 6.23/1.49  inst_num_of_learning_restarts:          0
% 6.23/1.49  inst_num_moves_active_passive:          163
% 6.23/1.49  inst_lit_activity:                      0
% 6.23/1.49  inst_lit_activity_moves:                0
% 6.23/1.49  inst_num_tautologies:                   0
% 6.23/1.49  inst_num_prop_implied:                  0
% 6.23/1.49  inst_num_existing_simplified:           0
% 6.23/1.49  inst_num_eq_res_simplified:             0
% 6.23/1.49  inst_num_child_elim:                    0
% 6.23/1.49  inst_num_of_dismatching_blockings:      1213
% 6.23/1.49  inst_num_of_non_proper_insts:           2342
% 6.23/1.49  inst_num_of_duplicates:                 0
% 6.23/1.49  inst_inst_num_from_inst_to_res:         0
% 6.23/1.49  inst_dismatching_checking_time:         0.
% 6.23/1.49  
% 6.23/1.49  ------ Resolution
% 6.23/1.49  
% 6.23/1.49  res_num_of_clauses:                     0
% 6.23/1.49  res_num_in_passive:                     0
% 6.23/1.49  res_num_in_active:                      0
% 6.23/1.49  res_num_of_loops:                       83
% 6.23/1.49  res_forward_subset_subsumed:            160
% 6.23/1.49  res_backward_subset_subsumed:           14
% 6.23/1.49  res_forward_subsumed:                   0
% 6.23/1.49  res_backward_subsumed:                  0
% 6.23/1.49  res_forward_subsumption_resolution:     0
% 6.23/1.49  res_backward_subsumption_resolution:    0
% 6.23/1.49  res_clause_to_clause_subsumption:       4864
% 6.23/1.49  res_orphan_elimination:                 0
% 6.23/1.49  res_tautology_del:                      165
% 6.23/1.49  res_num_eq_res_simplified:              0
% 6.23/1.49  res_num_sel_changes:                    0
% 6.23/1.49  res_moves_from_active_to_pass:          0
% 6.23/1.49  
% 6.23/1.49  ------ Superposition
% 6.23/1.49  
% 6.23/1.49  sup_time_total:                         0.
% 6.23/1.49  sup_time_generating:                    0.
% 6.23/1.49  sup_time_sim_full:                      0.
% 6.23/1.49  sup_time_sim_immed:                     0.
% 6.23/1.49  
% 6.23/1.49  sup_num_of_clauses:                     728
% 6.23/1.49  sup_num_in_active:                      159
% 6.23/1.49  sup_num_in_passive:                     569
% 6.23/1.49  sup_num_of_loops:                       184
% 6.23/1.49  sup_fw_superposition:                   1134
% 6.23/1.49  sup_bw_superposition:                   1113
% 6.23/1.49  sup_immediate_simplified:               615
% 6.23/1.49  sup_given_eliminated:                   0
% 6.23/1.49  comparisons_done:                       0
% 6.23/1.49  comparisons_avoided:                    0
% 6.23/1.49  
% 6.23/1.49  ------ Simplifications
% 6.23/1.49  
% 6.23/1.49  
% 6.23/1.49  sim_fw_subset_subsumed:                 32
% 6.23/1.49  sim_bw_subset_subsumed:                 10
% 6.23/1.49  sim_fw_subsumed:                        52
% 6.23/1.49  sim_bw_subsumed:                        14
% 6.23/1.49  sim_fw_subsumption_res:                 2
% 6.23/1.49  sim_bw_subsumption_res:                 3
% 6.23/1.49  sim_tautology_del:                      131
% 6.23/1.49  sim_eq_tautology_del:                   39
% 6.23/1.49  sim_eq_res_simp:                        0
% 6.23/1.49  sim_fw_demodulated:                     159
% 6.23/1.49  sim_bw_demodulated:                     60
% 6.23/1.49  sim_light_normalised:                   350
% 6.23/1.49  sim_joinable_taut:                      0
% 6.23/1.49  sim_joinable_simp:                      0
% 6.23/1.49  sim_ac_normalised:                      0
% 6.23/1.49  sim_smt_subsumption:                    0
% 6.23/1.49  
%------------------------------------------------------------------------------
