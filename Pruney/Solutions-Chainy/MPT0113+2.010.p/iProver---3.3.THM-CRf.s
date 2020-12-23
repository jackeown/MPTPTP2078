%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:25:44 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 109 expanded)
%              Number of clauses        :   36 (  42 expanded)
%              Number of leaves         :   14 (  26 expanded)
%              Depth                    :   15
%              Number of atoms          :  118 ( 179 expanded)
%              Number of equality atoms :   52 (  75 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).

fof(f37,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f34])).

fof(f7,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(definition_unfolding,[],[f30,f34])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f13,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_7,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_241,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_13,negated_conjecture,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_237,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_242,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1002,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = sK0 ),
    inference(superposition,[status(thm)],[c_237,c_242])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1018,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[status(thm)],[c_1002,c_0])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_9,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_254,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_6,c_9])).

cnf(c_650,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_254,c_0])).

cnf(c_656,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_650,c_9,c_254])).

cnf(c_1020,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1018,c_656])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1082,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1020,c_8])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_1084,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) = k4_xboole_0(sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_1082,c_4])).

cnf(c_1136,plain,
    ( k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_1,c_1084])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_243,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1201,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),X0) != iProver_top
    | r1_tarski(sK0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1136,c_243])).

cnf(c_1351,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_241,c_1201])).

cnf(c_11,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_437,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_438,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_437])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X2,X1)
    | ~ r1_tarski(X2,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_303,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(k4_xboole_0(X2,X1),X1)
    | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_371,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2)
    | r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_303])).

cnf(c_372,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) != iProver_top
    | r1_xboole_0(sK0,sK2) = iProver_top
    | r1_tarski(sK0,k4_xboole_0(sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_12,negated_conjecture,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_15,plain,
    ( r1_xboole_0(sK0,sK2) != iProver_top
    | r1_tarski(sK0,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1351,c_438,c_372,c_15,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:46:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.19/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.00  
% 2.19/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.19/1.00  
% 2.19/1.00  ------  iProver source info
% 2.19/1.00  
% 2.19/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.19/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.19/1.00  git: non_committed_changes: false
% 2.19/1.00  git: last_make_outside_of_git: false
% 2.19/1.00  
% 2.19/1.00  ------ 
% 2.19/1.00  
% 2.19/1.00  ------ Input Options
% 2.19/1.00  
% 2.19/1.00  --out_options                           all
% 2.19/1.00  --tptp_safe_out                         true
% 2.19/1.00  --problem_path                          ""
% 2.19/1.00  --include_path                          ""
% 2.19/1.00  --clausifier                            res/vclausify_rel
% 2.19/1.00  --clausifier_options                    --mode clausify
% 2.19/1.00  --stdin                                 false
% 2.19/1.00  --stats_out                             all
% 2.19/1.00  
% 2.19/1.00  ------ General Options
% 2.19/1.00  
% 2.19/1.00  --fof                                   false
% 2.19/1.00  --time_out_real                         305.
% 2.19/1.00  --time_out_virtual                      -1.
% 2.19/1.00  --symbol_type_check                     false
% 2.19/1.00  --clausify_out                          false
% 2.19/1.00  --sig_cnt_out                           false
% 2.19/1.00  --trig_cnt_out                          false
% 2.19/1.00  --trig_cnt_out_tolerance                1.
% 2.19/1.00  --trig_cnt_out_sk_spl                   false
% 2.19/1.00  --abstr_cl_out                          false
% 2.19/1.00  
% 2.19/1.00  ------ Global Options
% 2.19/1.00  
% 2.19/1.00  --schedule                              default
% 2.19/1.00  --add_important_lit                     false
% 2.19/1.00  --prop_solver_per_cl                    1000
% 2.19/1.00  --min_unsat_core                        false
% 2.19/1.00  --soft_assumptions                      false
% 2.19/1.00  --soft_lemma_size                       3
% 2.19/1.00  --prop_impl_unit_size                   0
% 2.19/1.00  --prop_impl_unit                        []
% 2.19/1.00  --share_sel_clauses                     true
% 2.19/1.00  --reset_solvers                         false
% 2.19/1.00  --bc_imp_inh                            [conj_cone]
% 2.19/1.00  --conj_cone_tolerance                   3.
% 2.19/1.00  --extra_neg_conj                        none
% 2.19/1.00  --large_theory_mode                     true
% 2.19/1.00  --prolific_symb_bound                   200
% 2.19/1.00  --lt_threshold                          2000
% 2.19/1.00  --clause_weak_htbl                      true
% 2.19/1.00  --gc_record_bc_elim                     false
% 2.19/1.00  
% 2.19/1.00  ------ Preprocessing Options
% 2.19/1.00  
% 2.19/1.00  --preprocessing_flag                    true
% 2.19/1.00  --time_out_prep_mult                    0.1
% 2.19/1.00  --splitting_mode                        input
% 2.19/1.00  --splitting_grd                         true
% 2.19/1.00  --splitting_cvd                         false
% 2.19/1.00  --splitting_cvd_svl                     false
% 2.19/1.00  --splitting_nvd                         32
% 2.19/1.00  --sub_typing                            true
% 2.19/1.00  --prep_gs_sim                           true
% 2.19/1.00  --prep_unflatten                        true
% 2.19/1.00  --prep_res_sim                          true
% 2.19/1.00  --prep_upred                            true
% 2.19/1.00  --prep_sem_filter                       exhaustive
% 2.19/1.00  --prep_sem_filter_out                   false
% 2.19/1.00  --pred_elim                             true
% 2.19/1.00  --res_sim_input                         true
% 2.19/1.00  --eq_ax_congr_red                       true
% 2.19/1.00  --pure_diseq_elim                       true
% 2.19/1.00  --brand_transform                       false
% 2.19/1.00  --non_eq_to_eq                          false
% 2.19/1.00  --prep_def_merge                        true
% 2.19/1.00  --prep_def_merge_prop_impl              false
% 2.19/1.00  --prep_def_merge_mbd                    true
% 2.19/1.00  --prep_def_merge_tr_red                 false
% 2.19/1.00  --prep_def_merge_tr_cl                  false
% 2.19/1.00  --smt_preprocessing                     true
% 2.19/1.00  --smt_ac_axioms                         fast
% 2.19/1.00  --preprocessed_out                      false
% 2.19/1.00  --preprocessed_stats                    false
% 2.19/1.00  
% 2.19/1.00  ------ Abstraction refinement Options
% 2.19/1.00  
% 2.19/1.00  --abstr_ref                             []
% 2.19/1.00  --abstr_ref_prep                        false
% 2.19/1.00  --abstr_ref_until_sat                   false
% 2.19/1.00  --abstr_ref_sig_restrict                funpre
% 2.19/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/1.00  --abstr_ref_under                       []
% 2.19/1.00  
% 2.19/1.00  ------ SAT Options
% 2.19/1.00  
% 2.19/1.00  --sat_mode                              false
% 2.19/1.00  --sat_fm_restart_options                ""
% 2.19/1.00  --sat_gr_def                            false
% 2.19/1.00  --sat_epr_types                         true
% 2.19/1.00  --sat_non_cyclic_types                  false
% 2.19/1.00  --sat_finite_models                     false
% 2.19/1.00  --sat_fm_lemmas                         false
% 2.19/1.00  --sat_fm_prep                           false
% 2.19/1.00  --sat_fm_uc_incr                        true
% 2.19/1.00  --sat_out_model                         small
% 2.19/1.00  --sat_out_clauses                       false
% 2.19/1.00  
% 2.19/1.00  ------ QBF Options
% 2.19/1.00  
% 2.19/1.00  --qbf_mode                              false
% 2.19/1.00  --qbf_elim_univ                         false
% 2.19/1.00  --qbf_dom_inst                          none
% 2.19/1.00  --qbf_dom_pre_inst                      false
% 2.19/1.00  --qbf_sk_in                             false
% 2.19/1.00  --qbf_pred_elim                         true
% 2.19/1.00  --qbf_split                             512
% 2.19/1.00  
% 2.19/1.00  ------ BMC1 Options
% 2.19/1.00  
% 2.19/1.00  --bmc1_incremental                      false
% 2.19/1.00  --bmc1_axioms                           reachable_all
% 2.19/1.00  --bmc1_min_bound                        0
% 2.19/1.00  --bmc1_max_bound                        -1
% 2.19/1.00  --bmc1_max_bound_default                -1
% 2.19/1.00  --bmc1_symbol_reachability              true
% 2.19/1.00  --bmc1_property_lemmas                  false
% 2.19/1.00  --bmc1_k_induction                      false
% 2.19/1.00  --bmc1_non_equiv_states                 false
% 2.19/1.00  --bmc1_deadlock                         false
% 2.19/1.00  --bmc1_ucm                              false
% 2.19/1.00  --bmc1_add_unsat_core                   none
% 2.19/1.00  --bmc1_unsat_core_children              false
% 2.19/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/1.00  --bmc1_out_stat                         full
% 2.19/1.00  --bmc1_ground_init                      false
% 2.19/1.00  --bmc1_pre_inst_next_state              false
% 2.19/1.00  --bmc1_pre_inst_state                   false
% 2.19/1.00  --bmc1_pre_inst_reach_state             false
% 2.19/1.00  --bmc1_out_unsat_core                   false
% 2.19/1.00  --bmc1_aig_witness_out                  false
% 2.19/1.00  --bmc1_verbose                          false
% 2.19/1.00  --bmc1_dump_clauses_tptp                false
% 2.19/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.19/1.00  --bmc1_dump_file                        -
% 2.19/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.19/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.19/1.00  --bmc1_ucm_extend_mode                  1
% 2.19/1.00  --bmc1_ucm_init_mode                    2
% 2.19/1.00  --bmc1_ucm_cone_mode                    none
% 2.19/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.19/1.00  --bmc1_ucm_relax_model                  4
% 2.19/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.19/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/1.00  --bmc1_ucm_layered_model                none
% 2.19/1.00  --bmc1_ucm_max_lemma_size               10
% 2.19/1.00  
% 2.19/1.00  ------ AIG Options
% 2.19/1.00  
% 2.19/1.00  --aig_mode                              false
% 2.19/1.00  
% 2.19/1.00  ------ Instantiation Options
% 2.19/1.00  
% 2.19/1.00  --instantiation_flag                    true
% 2.19/1.00  --inst_sos_flag                         false
% 2.19/1.00  --inst_sos_phase                        true
% 2.19/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/1.00  --inst_lit_sel_side                     num_symb
% 2.19/1.00  --inst_solver_per_active                1400
% 2.19/1.00  --inst_solver_calls_frac                1.
% 2.19/1.00  --inst_passive_queue_type               priority_queues
% 2.19/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/1.00  --inst_passive_queues_freq              [25;2]
% 2.19/1.00  --inst_dismatching                      true
% 2.19/1.00  --inst_eager_unprocessed_to_passive     true
% 2.19/1.00  --inst_prop_sim_given                   true
% 2.19/1.00  --inst_prop_sim_new                     false
% 2.19/1.00  --inst_subs_new                         false
% 2.19/1.00  --inst_eq_res_simp                      false
% 2.19/1.00  --inst_subs_given                       false
% 2.19/1.00  --inst_orphan_elimination               true
% 2.19/1.00  --inst_learning_loop_flag               true
% 2.19/1.00  --inst_learning_start                   3000
% 2.19/1.00  --inst_learning_factor                  2
% 2.19/1.00  --inst_start_prop_sim_after_learn       3
% 2.19/1.00  --inst_sel_renew                        solver
% 2.19/1.00  --inst_lit_activity_flag                true
% 2.19/1.00  --inst_restr_to_given                   false
% 2.19/1.00  --inst_activity_threshold               500
% 2.19/1.00  --inst_out_proof                        true
% 2.19/1.00  
% 2.19/1.00  ------ Resolution Options
% 2.19/1.00  
% 2.19/1.00  --resolution_flag                       true
% 2.19/1.00  --res_lit_sel                           adaptive
% 2.19/1.00  --res_lit_sel_side                      none
% 2.19/1.00  --res_ordering                          kbo
% 2.19/1.00  --res_to_prop_solver                    active
% 2.19/1.00  --res_prop_simpl_new                    false
% 2.19/1.00  --res_prop_simpl_given                  true
% 2.19/1.00  --res_passive_queue_type                priority_queues
% 2.19/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/1.00  --res_passive_queues_freq               [15;5]
% 2.19/1.00  --res_forward_subs                      full
% 2.19/1.00  --res_backward_subs                     full
% 2.19/1.00  --res_forward_subs_resolution           true
% 2.19/1.00  --res_backward_subs_resolution          true
% 2.19/1.00  --res_orphan_elimination                true
% 2.19/1.00  --res_time_limit                        2.
% 2.19/1.00  --res_out_proof                         true
% 2.19/1.00  
% 2.19/1.00  ------ Superposition Options
% 2.19/1.00  
% 2.19/1.00  --superposition_flag                    true
% 2.19/1.00  --sup_passive_queue_type                priority_queues
% 2.19/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.19/1.00  --demod_completeness_check              fast
% 2.19/1.00  --demod_use_ground                      true
% 2.19/1.00  --sup_to_prop_solver                    passive
% 2.19/1.00  --sup_prop_simpl_new                    true
% 2.19/1.00  --sup_prop_simpl_given                  true
% 2.19/1.00  --sup_fun_splitting                     false
% 2.19/1.00  --sup_smt_interval                      50000
% 2.19/1.00  
% 2.19/1.00  ------ Superposition Simplification Setup
% 2.19/1.00  
% 2.19/1.00  --sup_indices_passive                   []
% 2.19/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.00  --sup_full_bw                           [BwDemod]
% 2.19/1.00  --sup_immed_triv                        [TrivRules]
% 2.19/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.00  --sup_immed_bw_main                     []
% 2.19/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.00  
% 2.19/1.00  ------ Combination Options
% 2.19/1.00  
% 2.19/1.00  --comb_res_mult                         3
% 2.19/1.00  --comb_sup_mult                         2
% 2.19/1.00  --comb_inst_mult                        10
% 2.19/1.00  
% 2.19/1.00  ------ Debug Options
% 2.19/1.00  
% 2.19/1.00  --dbg_backtrace                         false
% 2.19/1.00  --dbg_dump_prop_clauses                 false
% 2.19/1.00  --dbg_dump_prop_clauses_file            -
% 2.19/1.00  --dbg_out_stat                          false
% 2.19/1.00  ------ Parsing...
% 2.19/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.19/1.00  
% 2.19/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.19/1.00  
% 2.19/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.19/1.00  
% 2.19/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.19/1.00  ------ Proving...
% 2.19/1.00  ------ Problem Properties 
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  clauses                                 14
% 2.19/1.00  conjectures                             2
% 2.19/1.00  EPR                                     2
% 2.19/1.00  Horn                                    14
% 2.19/1.00  unary                                   10
% 2.19/1.00  binary                                  3
% 2.19/1.00  lits                                    19
% 2.19/1.00  lits eq                                 8
% 2.19/1.00  fd_pure                                 0
% 2.19/1.00  fd_pseudo                               0
% 2.19/1.00  fd_cond                                 0
% 2.19/1.00  fd_pseudo_cond                          0
% 2.19/1.00  AC symbols                              0
% 2.19/1.00  
% 2.19/1.00  ------ Schedule dynamic 5 is on 
% 2.19/1.00  
% 2.19/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  ------ 
% 2.19/1.00  Current options:
% 2.19/1.00  ------ 
% 2.19/1.00  
% 2.19/1.00  ------ Input Options
% 2.19/1.00  
% 2.19/1.00  --out_options                           all
% 2.19/1.00  --tptp_safe_out                         true
% 2.19/1.00  --problem_path                          ""
% 2.19/1.00  --include_path                          ""
% 2.19/1.00  --clausifier                            res/vclausify_rel
% 2.19/1.00  --clausifier_options                    --mode clausify
% 2.19/1.00  --stdin                                 false
% 2.19/1.00  --stats_out                             all
% 2.19/1.00  
% 2.19/1.00  ------ General Options
% 2.19/1.00  
% 2.19/1.00  --fof                                   false
% 2.19/1.00  --time_out_real                         305.
% 2.19/1.00  --time_out_virtual                      -1.
% 2.19/1.00  --symbol_type_check                     false
% 2.19/1.00  --clausify_out                          false
% 2.19/1.00  --sig_cnt_out                           false
% 2.19/1.00  --trig_cnt_out                          false
% 2.19/1.00  --trig_cnt_out_tolerance                1.
% 2.19/1.00  --trig_cnt_out_sk_spl                   false
% 2.19/1.00  --abstr_cl_out                          false
% 2.19/1.00  
% 2.19/1.00  ------ Global Options
% 2.19/1.00  
% 2.19/1.00  --schedule                              default
% 2.19/1.00  --add_important_lit                     false
% 2.19/1.00  --prop_solver_per_cl                    1000
% 2.19/1.00  --min_unsat_core                        false
% 2.19/1.00  --soft_assumptions                      false
% 2.19/1.00  --soft_lemma_size                       3
% 2.19/1.00  --prop_impl_unit_size                   0
% 2.19/1.00  --prop_impl_unit                        []
% 2.19/1.00  --share_sel_clauses                     true
% 2.19/1.00  --reset_solvers                         false
% 2.19/1.00  --bc_imp_inh                            [conj_cone]
% 2.19/1.00  --conj_cone_tolerance                   3.
% 2.19/1.00  --extra_neg_conj                        none
% 2.19/1.00  --large_theory_mode                     true
% 2.19/1.00  --prolific_symb_bound                   200
% 2.19/1.00  --lt_threshold                          2000
% 2.19/1.00  --clause_weak_htbl                      true
% 2.19/1.00  --gc_record_bc_elim                     false
% 2.19/1.00  
% 2.19/1.00  ------ Preprocessing Options
% 2.19/1.00  
% 2.19/1.00  --preprocessing_flag                    true
% 2.19/1.00  --time_out_prep_mult                    0.1
% 2.19/1.00  --splitting_mode                        input
% 2.19/1.00  --splitting_grd                         true
% 2.19/1.00  --splitting_cvd                         false
% 2.19/1.00  --splitting_cvd_svl                     false
% 2.19/1.00  --splitting_nvd                         32
% 2.19/1.00  --sub_typing                            true
% 2.19/1.00  --prep_gs_sim                           true
% 2.19/1.00  --prep_unflatten                        true
% 2.19/1.00  --prep_res_sim                          true
% 2.19/1.00  --prep_upred                            true
% 2.19/1.00  --prep_sem_filter                       exhaustive
% 2.19/1.00  --prep_sem_filter_out                   false
% 2.19/1.00  --pred_elim                             true
% 2.19/1.00  --res_sim_input                         true
% 2.19/1.00  --eq_ax_congr_red                       true
% 2.19/1.00  --pure_diseq_elim                       true
% 2.19/1.00  --brand_transform                       false
% 2.19/1.00  --non_eq_to_eq                          false
% 2.19/1.00  --prep_def_merge                        true
% 2.19/1.00  --prep_def_merge_prop_impl              false
% 2.19/1.00  --prep_def_merge_mbd                    true
% 2.19/1.00  --prep_def_merge_tr_red                 false
% 2.19/1.00  --prep_def_merge_tr_cl                  false
% 2.19/1.00  --smt_preprocessing                     true
% 2.19/1.00  --smt_ac_axioms                         fast
% 2.19/1.00  --preprocessed_out                      false
% 2.19/1.00  --preprocessed_stats                    false
% 2.19/1.00  
% 2.19/1.00  ------ Abstraction refinement Options
% 2.19/1.00  
% 2.19/1.00  --abstr_ref                             []
% 2.19/1.00  --abstr_ref_prep                        false
% 2.19/1.00  --abstr_ref_until_sat                   false
% 2.19/1.00  --abstr_ref_sig_restrict                funpre
% 2.19/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/1.00  --abstr_ref_under                       []
% 2.19/1.00  
% 2.19/1.00  ------ SAT Options
% 2.19/1.00  
% 2.19/1.00  --sat_mode                              false
% 2.19/1.00  --sat_fm_restart_options                ""
% 2.19/1.00  --sat_gr_def                            false
% 2.19/1.00  --sat_epr_types                         true
% 2.19/1.00  --sat_non_cyclic_types                  false
% 2.19/1.00  --sat_finite_models                     false
% 2.19/1.00  --sat_fm_lemmas                         false
% 2.19/1.00  --sat_fm_prep                           false
% 2.19/1.00  --sat_fm_uc_incr                        true
% 2.19/1.00  --sat_out_model                         small
% 2.19/1.00  --sat_out_clauses                       false
% 2.19/1.00  
% 2.19/1.00  ------ QBF Options
% 2.19/1.00  
% 2.19/1.00  --qbf_mode                              false
% 2.19/1.00  --qbf_elim_univ                         false
% 2.19/1.00  --qbf_dom_inst                          none
% 2.19/1.00  --qbf_dom_pre_inst                      false
% 2.19/1.00  --qbf_sk_in                             false
% 2.19/1.00  --qbf_pred_elim                         true
% 2.19/1.00  --qbf_split                             512
% 2.19/1.00  
% 2.19/1.00  ------ BMC1 Options
% 2.19/1.00  
% 2.19/1.00  --bmc1_incremental                      false
% 2.19/1.00  --bmc1_axioms                           reachable_all
% 2.19/1.00  --bmc1_min_bound                        0
% 2.19/1.00  --bmc1_max_bound                        -1
% 2.19/1.00  --bmc1_max_bound_default                -1
% 2.19/1.00  --bmc1_symbol_reachability              true
% 2.19/1.00  --bmc1_property_lemmas                  false
% 2.19/1.00  --bmc1_k_induction                      false
% 2.19/1.00  --bmc1_non_equiv_states                 false
% 2.19/1.00  --bmc1_deadlock                         false
% 2.19/1.00  --bmc1_ucm                              false
% 2.19/1.00  --bmc1_add_unsat_core                   none
% 2.19/1.00  --bmc1_unsat_core_children              false
% 2.19/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/1.00  --bmc1_out_stat                         full
% 2.19/1.00  --bmc1_ground_init                      false
% 2.19/1.00  --bmc1_pre_inst_next_state              false
% 2.19/1.00  --bmc1_pre_inst_state                   false
% 2.19/1.00  --bmc1_pre_inst_reach_state             false
% 2.19/1.00  --bmc1_out_unsat_core                   false
% 2.19/1.00  --bmc1_aig_witness_out                  false
% 2.19/1.00  --bmc1_verbose                          false
% 2.19/1.00  --bmc1_dump_clauses_tptp                false
% 2.19/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.19/1.00  --bmc1_dump_file                        -
% 2.19/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.19/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.19/1.00  --bmc1_ucm_extend_mode                  1
% 2.19/1.00  --bmc1_ucm_init_mode                    2
% 2.19/1.00  --bmc1_ucm_cone_mode                    none
% 2.19/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.19/1.00  --bmc1_ucm_relax_model                  4
% 2.19/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.19/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/1.00  --bmc1_ucm_layered_model                none
% 2.19/1.00  --bmc1_ucm_max_lemma_size               10
% 2.19/1.00  
% 2.19/1.00  ------ AIG Options
% 2.19/1.00  
% 2.19/1.00  --aig_mode                              false
% 2.19/1.00  
% 2.19/1.00  ------ Instantiation Options
% 2.19/1.00  
% 2.19/1.00  --instantiation_flag                    true
% 2.19/1.00  --inst_sos_flag                         false
% 2.19/1.00  --inst_sos_phase                        true
% 2.19/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/1.00  --inst_lit_sel_side                     none
% 2.19/1.00  --inst_solver_per_active                1400
% 2.19/1.00  --inst_solver_calls_frac                1.
% 2.19/1.00  --inst_passive_queue_type               priority_queues
% 2.19/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/1.00  --inst_passive_queues_freq              [25;2]
% 2.19/1.00  --inst_dismatching                      true
% 2.19/1.00  --inst_eager_unprocessed_to_passive     true
% 2.19/1.00  --inst_prop_sim_given                   true
% 2.19/1.00  --inst_prop_sim_new                     false
% 2.19/1.00  --inst_subs_new                         false
% 2.19/1.00  --inst_eq_res_simp                      false
% 2.19/1.00  --inst_subs_given                       false
% 2.19/1.00  --inst_orphan_elimination               true
% 2.19/1.00  --inst_learning_loop_flag               true
% 2.19/1.00  --inst_learning_start                   3000
% 2.19/1.00  --inst_learning_factor                  2
% 2.19/1.00  --inst_start_prop_sim_after_learn       3
% 2.19/1.00  --inst_sel_renew                        solver
% 2.19/1.00  --inst_lit_activity_flag                true
% 2.19/1.00  --inst_restr_to_given                   false
% 2.19/1.00  --inst_activity_threshold               500
% 2.19/1.00  --inst_out_proof                        true
% 2.19/1.00  
% 2.19/1.00  ------ Resolution Options
% 2.19/1.00  
% 2.19/1.00  --resolution_flag                       false
% 2.19/1.00  --res_lit_sel                           adaptive
% 2.19/1.00  --res_lit_sel_side                      none
% 2.19/1.00  --res_ordering                          kbo
% 2.19/1.00  --res_to_prop_solver                    active
% 2.19/1.00  --res_prop_simpl_new                    false
% 2.19/1.00  --res_prop_simpl_given                  true
% 2.19/1.00  --res_passive_queue_type                priority_queues
% 2.19/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/1.00  --res_passive_queues_freq               [15;5]
% 2.19/1.00  --res_forward_subs                      full
% 2.19/1.00  --res_backward_subs                     full
% 2.19/1.00  --res_forward_subs_resolution           true
% 2.19/1.00  --res_backward_subs_resolution          true
% 2.19/1.00  --res_orphan_elimination                true
% 2.19/1.00  --res_time_limit                        2.
% 2.19/1.00  --res_out_proof                         true
% 2.19/1.00  
% 2.19/1.00  ------ Superposition Options
% 2.19/1.00  
% 2.19/1.00  --superposition_flag                    true
% 2.19/1.00  --sup_passive_queue_type                priority_queues
% 2.19/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.19/1.00  --demod_completeness_check              fast
% 2.19/1.00  --demod_use_ground                      true
% 2.19/1.00  --sup_to_prop_solver                    passive
% 2.19/1.00  --sup_prop_simpl_new                    true
% 2.19/1.00  --sup_prop_simpl_given                  true
% 2.19/1.00  --sup_fun_splitting                     false
% 2.19/1.00  --sup_smt_interval                      50000
% 2.19/1.00  
% 2.19/1.00  ------ Superposition Simplification Setup
% 2.19/1.00  
% 2.19/1.00  --sup_indices_passive                   []
% 2.19/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.00  --sup_full_bw                           [BwDemod]
% 2.19/1.00  --sup_immed_triv                        [TrivRules]
% 2.19/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.00  --sup_immed_bw_main                     []
% 2.19/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/1.00  
% 2.19/1.00  ------ Combination Options
% 2.19/1.00  
% 2.19/1.00  --comb_res_mult                         3
% 2.19/1.00  --comb_sup_mult                         2
% 2.19/1.00  --comb_inst_mult                        10
% 2.19/1.00  
% 2.19/1.00  ------ Debug Options
% 2.19/1.00  
% 2.19/1.00  --dbg_backtrace                         false
% 2.19/1.00  --dbg_dump_prop_clauses                 false
% 2.19/1.00  --dbg_dump_prop_clauses_file            -
% 2.19/1.00  --dbg_out_stat                          false
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  ------ Proving...
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  % SZS status Theorem for theBenchmark.p
% 2.19/1.00  
% 2.19/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.19/1.00  
% 2.19/1.00  fof(f8,axiom,(
% 2.19/1.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f31,plain,(
% 2.19/1.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f8])).
% 2.19/1.00  
% 2.19/1.00  fof(f1,axiom,(
% 2.19/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f24,plain,(
% 2.19/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f1])).
% 2.19/1.00  
% 2.19/1.00  fof(f14,conjecture,(
% 2.19/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f15,negated_conjecture,(
% 2.19/1.00    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.19/1.00    inference(negated_conjecture,[],[f14])).
% 2.19/1.00  
% 2.19/1.00  fof(f21,plain,(
% 2.19/1.00    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.19/1.00    inference(ennf_transformation,[],[f15])).
% 2.19/1.00  
% 2.19/1.00  fof(f22,plain,(
% 2.19/1.00    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 2.19/1.00    introduced(choice_axiom,[])).
% 2.19/1.00  
% 2.19/1.00  fof(f23,plain,(
% 2.19/1.00    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 2.19/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f22])).
% 2.19/1.00  
% 2.19/1.00  fof(f37,plain,(
% 2.19/1.00    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 2.19/1.00    inference(cnf_transformation,[],[f23])).
% 2.19/1.00  
% 2.19/1.00  fof(f6,axiom,(
% 2.19/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f18,plain,(
% 2.19/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.19/1.00    inference(ennf_transformation,[],[f6])).
% 2.19/1.00  
% 2.19/1.00  fof(f29,plain,(
% 2.19/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f18])).
% 2.19/1.00  
% 2.19/1.00  fof(f11,axiom,(
% 2.19/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f34,plain,(
% 2.19/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.19/1.00    inference(cnf_transformation,[],[f11])).
% 2.19/1.00  
% 2.19/1.00  fof(f41,plain,(
% 2.19/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.19/1.00    inference(definition_unfolding,[],[f29,f34])).
% 2.19/1.00  
% 2.19/1.00  fof(f3,axiom,(
% 2.19/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f26,plain,(
% 2.19/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.19/1.00    inference(cnf_transformation,[],[f3])).
% 2.19/1.00  
% 2.19/1.00  fof(f39,plain,(
% 2.19/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.19/1.00    inference(definition_unfolding,[],[f26,f34])).
% 2.19/1.00  
% 2.19/1.00  fof(f7,axiom,(
% 2.19/1.00    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f30,plain,(
% 2.19/1.00    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0) )),
% 2.19/1.00    inference(cnf_transformation,[],[f7])).
% 2.19/1.00  
% 2.19/1.00  fof(f42,plain,(
% 2.19/1.00    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0) )),
% 2.19/1.00    inference(definition_unfolding,[],[f30,f34])).
% 2.19/1.00  
% 2.19/1.00  fof(f10,axiom,(
% 2.19/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f33,plain,(
% 2.19/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.19/1.00    inference(cnf_transformation,[],[f10])).
% 2.19/1.00  
% 2.19/1.00  fof(f9,axiom,(
% 2.19/1.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f32,plain,(
% 2.19/1.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.19/1.00    inference(cnf_transformation,[],[f9])).
% 2.19/1.00  
% 2.19/1.00  fof(f5,axiom,(
% 2.19/1.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f28,plain,(
% 2.19/1.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.19/1.00    inference(cnf_transformation,[],[f5])).
% 2.19/1.00  
% 2.19/1.00  fof(f4,axiom,(
% 2.19/1.00    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f17,plain,(
% 2.19/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 2.19/1.00    inference(ennf_transformation,[],[f4])).
% 2.19/1.00  
% 2.19/1.00  fof(f27,plain,(
% 2.19/1.00    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f17])).
% 2.19/1.00  
% 2.19/1.00  fof(f13,axiom,(
% 2.19/1.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f36,plain,(
% 2.19/1.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f13])).
% 2.19/1.00  
% 2.19/1.00  fof(f12,axiom,(
% 2.19/1.00    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.19/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.19/1.00  
% 2.19/1.00  fof(f19,plain,(
% 2.19/1.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.19/1.00    inference(ennf_transformation,[],[f12])).
% 2.19/1.00  
% 2.19/1.00  fof(f20,plain,(
% 2.19/1.00    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.19/1.00    inference(flattening,[],[f19])).
% 2.19/1.00  
% 2.19/1.00  fof(f35,plain,(
% 2.19/1.00    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 2.19/1.00    inference(cnf_transformation,[],[f20])).
% 2.19/1.00  
% 2.19/1.00  fof(f38,plain,(
% 2.19/1.00    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 2.19/1.00    inference(cnf_transformation,[],[f23])).
% 2.19/1.00  
% 2.19/1.00  cnf(c_7,plain,
% 2.19/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 2.19/1.00      inference(cnf_transformation,[],[f31]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_241,plain,
% 2.19/1.00      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1,plain,
% 2.19/1.00      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 2.19/1.00      inference(cnf_transformation,[],[f24]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_13,negated_conjecture,
% 2.19/1.00      ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
% 2.19/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_237,plain,
% 2.19/1.00      ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_5,plain,
% 2.19/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 2.19/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_242,plain,
% 2.19/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 2.19/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1002,plain,
% 2.19/1.00      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = sK0 ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_237,c_242]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_0,plain,
% 2.19/1.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 2.19/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1018,plain,
% 2.19/1.00      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0) ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_1002,c_0]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_6,plain,
% 2.19/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.19/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_9,plain,
% 2.19/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.19/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_254,plain,
% 2.19/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.19/1.00      inference(light_normalisation,[status(thm)],[c_6,c_9]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_650,plain,
% 2.19/1.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k4_xboole_0(X0,X0) ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_254,c_0]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_656,plain,
% 2.19/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.19/1.00      inference(light_normalisation,[status(thm)],[c_650,c_9,c_254]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1020,plain,
% 2.19/1.00      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k1_xboole_0 ),
% 2.19/1.00      inference(demodulation,[status(thm)],[c_1018,c_656]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_8,plain,
% 2.19/1.00      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 2.19/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1082,plain,
% 2.19/1.00      ( k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_1020,c_8]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_4,plain,
% 2.19/1.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.19/1.00      inference(cnf_transformation,[],[f28]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1084,plain,
% 2.19/1.00      ( k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) = k4_xboole_0(sK1,sK2) ),
% 2.19/1.00      inference(demodulation,[status(thm)],[c_1082,c_4]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1136,plain,
% 2.19/1.00      ( k2_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,sK2) ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_1,c_1084]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_3,plain,
% 2.19/1.00      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 2.19/1.00      inference(cnf_transformation,[],[f27]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_243,plain,
% 2.19/1.00      ( r1_tarski(X0,X1) = iProver_top
% 2.19/1.00      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1201,plain,
% 2.19/1.00      ( r1_tarski(k4_xboole_0(sK1,sK2),X0) != iProver_top
% 2.19/1.00      | r1_tarski(sK0,X0) = iProver_top ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_1136,c_243]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_1351,plain,
% 2.19/1.00      ( r1_tarski(sK0,sK1) = iProver_top ),
% 2.19/1.00      inference(superposition,[status(thm)],[c_241,c_1201]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_11,plain,
% 2.19/1.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 2.19/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_437,plain,
% 2.19/1.00      ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
% 2.19/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_438,plain,
% 2.19/1.00      ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) = iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_437]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_10,plain,
% 2.19/1.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X2,X1) | ~ r1_tarski(X2,X0) ),
% 2.19/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_303,plain,
% 2.19/1.00      ( r1_xboole_0(X0,X1)
% 2.19/1.00      | ~ r1_xboole_0(k4_xboole_0(X2,X1),X1)
% 2.19/1.00      | ~ r1_tarski(X0,k4_xboole_0(X2,X1)) ),
% 2.19/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_371,plain,
% 2.19/1.00      ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2)
% 2.19/1.00      | r1_xboole_0(sK0,sK2)
% 2.19/1.00      | ~ r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
% 2.19/1.00      inference(instantiation,[status(thm)],[c_303]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_372,plain,
% 2.19/1.00      ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) != iProver_top
% 2.19/1.00      | r1_xboole_0(sK0,sK2) = iProver_top
% 2.19/1.00      | r1_tarski(sK0,k4_xboole_0(sK1,sK2)) != iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_12,negated_conjecture,
% 2.19/1.00      ( ~ r1_xboole_0(sK0,sK2) | ~ r1_tarski(sK0,sK1) ),
% 2.19/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_15,plain,
% 2.19/1.00      ( r1_xboole_0(sK0,sK2) != iProver_top
% 2.19/1.00      | r1_tarski(sK0,sK1) != iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(c_14,plain,
% 2.19/1.00      ( r1_tarski(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
% 2.19/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.19/1.00  
% 2.19/1.00  cnf(contradiction,plain,
% 2.19/1.00      ( $false ),
% 2.19/1.00      inference(minisat,[status(thm)],[c_1351,c_438,c_372,c_15,c_14]) ).
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.19/1.00  
% 2.19/1.00  ------                               Statistics
% 2.19/1.00  
% 2.19/1.00  ------ General
% 2.19/1.00  
% 2.19/1.00  abstr_ref_over_cycles:                  0
% 2.19/1.00  abstr_ref_under_cycles:                 0
% 2.19/1.00  gc_basic_clause_elim:                   0
% 2.19/1.00  forced_gc_time:                         0
% 2.19/1.00  parsing_time:                           0.011
% 2.19/1.00  unif_index_cands_time:                  0.
% 2.19/1.00  unif_index_add_time:                    0.
% 2.19/1.00  orderings_time:                         0.
% 2.19/1.00  out_proof_time:                         0.011
% 2.19/1.00  total_time:                             0.083
% 2.19/1.00  num_of_symbols:                         40
% 2.19/1.00  num_of_terms:                           1532
% 2.19/1.00  
% 2.19/1.00  ------ Preprocessing
% 2.19/1.00  
% 2.19/1.00  num_of_splits:                          0
% 2.19/1.00  num_of_split_atoms:                     0
% 2.19/1.00  num_of_reused_defs:                     0
% 2.19/1.00  num_eq_ax_congr_red:                    4
% 2.19/1.00  num_of_sem_filtered_clauses:            1
% 2.19/1.00  num_of_subtypes:                        0
% 2.19/1.00  monotx_restored_types:                  0
% 2.19/1.00  sat_num_of_epr_types:                   0
% 2.19/1.00  sat_num_of_non_cyclic_types:            0
% 2.19/1.00  sat_guarded_non_collapsed_types:        0
% 2.19/1.00  num_pure_diseq_elim:                    0
% 2.19/1.00  simp_replaced_by:                       0
% 2.19/1.00  res_preprocessed:                       57
% 2.19/1.00  prep_upred:                             0
% 2.19/1.00  prep_unflattend:                        0
% 2.19/1.00  smt_new_axioms:                         0
% 2.19/1.00  pred_elim_cands:                        2
% 2.19/1.00  pred_elim:                              0
% 2.19/1.00  pred_elim_cl:                           0
% 2.19/1.00  pred_elim_cycles:                       1
% 2.19/1.00  merged_defs:                            0
% 2.19/1.00  merged_defs_ncl:                        0
% 2.19/1.00  bin_hyper_res:                          0
% 2.19/1.00  prep_cycles:                            3
% 2.19/1.00  pred_elim_time:                         0.
% 2.19/1.00  splitting_time:                         0.
% 2.19/1.00  sem_filter_time:                        0.
% 2.19/1.00  monotx_time:                            0.001
% 2.19/1.00  subtype_inf_time:                       0.
% 2.19/1.00  
% 2.19/1.00  ------ Problem properties
% 2.19/1.00  
% 2.19/1.00  clauses:                                14
% 2.19/1.00  conjectures:                            2
% 2.19/1.00  epr:                                    2
% 2.19/1.00  horn:                                   14
% 2.19/1.00  ground:                                 2
% 2.19/1.00  unary:                                  10
% 2.19/1.00  binary:                                 3
% 2.19/1.00  lits:                                   19
% 2.19/1.00  lits_eq:                                8
% 2.19/1.00  fd_pure:                                0
% 2.19/1.00  fd_pseudo:                              0
% 2.19/1.00  fd_cond:                                0
% 2.19/1.00  fd_pseudo_cond:                         0
% 2.19/1.00  ac_symbols:                             0
% 2.19/1.00  
% 2.19/1.00  ------ Propositional Solver
% 2.19/1.00  
% 2.19/1.00  prop_solver_calls:                      23
% 2.19/1.00  prop_fast_solver_calls:                 226
% 2.19/1.00  smt_solver_calls:                       0
% 2.19/1.00  smt_fast_solver_calls:                  0
% 2.19/1.00  prop_num_of_clauses:                    559
% 2.19/1.00  prop_preprocess_simplified:             1897
% 2.19/1.00  prop_fo_subsumed:                       0
% 2.19/1.00  prop_solver_time:                       0.
% 2.19/1.00  smt_solver_time:                        0.
% 2.19/1.00  smt_fast_solver_time:                   0.
% 2.19/1.00  prop_fast_solver_time:                  0.
% 2.19/1.00  prop_unsat_core_time:                   0.
% 2.19/1.00  
% 2.19/1.00  ------ QBF
% 2.19/1.00  
% 2.19/1.00  qbf_q_res:                              0
% 2.19/1.00  qbf_num_tautologies:                    0
% 2.19/1.00  qbf_prep_cycles:                        0
% 2.19/1.00  
% 2.19/1.00  ------ BMC1
% 2.19/1.00  
% 2.19/1.00  bmc1_current_bound:                     -1
% 2.19/1.00  bmc1_last_solved_bound:                 -1
% 2.19/1.00  bmc1_unsat_core_size:                   -1
% 2.19/1.00  bmc1_unsat_core_parents_size:           -1
% 2.19/1.00  bmc1_merge_next_fun:                    0
% 2.19/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.19/1.00  
% 2.19/1.00  ------ Instantiation
% 2.19/1.00  
% 2.19/1.00  inst_num_of_clauses:                    194
% 2.19/1.00  inst_num_in_passive:                    27
% 2.19/1.00  inst_num_in_active:                     129
% 2.19/1.00  inst_num_in_unprocessed:                38
% 2.19/1.00  inst_num_of_loops:                      140
% 2.19/1.00  inst_num_of_learning_restarts:          0
% 2.19/1.00  inst_num_moves_active_passive:          8
% 2.19/1.00  inst_lit_activity:                      0
% 2.19/1.00  inst_lit_activity_moves:                0
% 2.19/1.00  inst_num_tautologies:                   0
% 2.19/1.00  inst_num_prop_implied:                  0
% 2.19/1.00  inst_num_existing_simplified:           0
% 2.19/1.00  inst_num_eq_res_simplified:             0
% 2.19/1.00  inst_num_child_elim:                    0
% 2.19/1.00  inst_num_of_dismatching_blockings:      56
% 2.19/1.00  inst_num_of_non_proper_insts:           130
% 2.19/1.00  inst_num_of_duplicates:                 0
% 2.19/1.00  inst_inst_num_from_inst_to_res:         0
% 2.19/1.00  inst_dismatching_checking_time:         0.
% 2.19/1.00  
% 2.19/1.00  ------ Resolution
% 2.19/1.00  
% 2.19/1.00  res_num_of_clauses:                     0
% 2.19/1.00  res_num_in_passive:                     0
% 2.19/1.00  res_num_in_active:                      0
% 2.19/1.00  res_num_of_loops:                       60
% 2.19/1.00  res_forward_subset_subsumed:            6
% 2.19/1.00  res_backward_subset_subsumed:           0
% 2.19/1.00  res_forward_subsumed:                   0
% 2.19/1.00  res_backward_subsumed:                  0
% 2.19/1.00  res_forward_subsumption_resolution:     0
% 2.19/1.00  res_backward_subsumption_resolution:    0
% 2.19/1.00  res_clause_to_clause_subsumption:       97
% 2.19/1.00  res_orphan_elimination:                 0
% 2.19/1.00  res_tautology_del:                      5
% 2.19/1.00  res_num_eq_res_simplified:              0
% 2.19/1.00  res_num_sel_changes:                    0
% 2.19/1.00  res_moves_from_active_to_pass:          0
% 2.19/1.00  
% 2.19/1.00  ------ Superposition
% 2.19/1.00  
% 2.19/1.00  sup_time_total:                         0.
% 2.19/1.00  sup_time_generating:                    0.
% 2.19/1.00  sup_time_sim_full:                      0.
% 2.19/1.00  sup_time_sim_immed:                     0.
% 2.19/1.00  
% 2.19/1.00  sup_num_of_clauses:                     34
% 2.19/1.00  sup_num_in_active:                      26
% 2.19/1.00  sup_num_in_passive:                     8
% 2.19/1.00  sup_num_of_loops:                       26
% 2.19/1.00  sup_fw_superposition:                   41
% 2.19/1.00  sup_bw_superposition:                   15
% 2.19/1.00  sup_immediate_simplified:               20
% 2.19/1.00  sup_given_eliminated:                   1
% 2.19/1.00  comparisons_done:                       0
% 2.19/1.00  comparisons_avoided:                    0
% 2.19/1.00  
% 2.19/1.00  ------ Simplifications
% 2.19/1.00  
% 2.19/1.00  
% 2.19/1.00  sim_fw_subset_subsumed:                 1
% 2.19/1.00  sim_bw_subset_subsumed:                 0
% 2.19/1.00  sim_fw_subsumed:                        7
% 2.19/1.00  sim_bw_subsumed:                        0
% 2.19/1.00  sim_fw_subsumption_res:                 0
% 2.19/1.00  sim_bw_subsumption_res:                 0
% 2.19/1.00  sim_tautology_del:                      5
% 2.19/1.00  sim_eq_tautology_del:                   5
% 2.19/1.00  sim_eq_res_simp:                        0
% 2.19/1.00  sim_fw_demodulated:                     4
% 2.19/1.00  sim_bw_demodulated:                     1
% 2.19/1.00  sim_light_normalised:                   11
% 2.19/1.00  sim_joinable_taut:                      0
% 2.19/1.00  sim_joinable_simp:                      0
% 2.19/1.00  sim_ac_normalised:                      0
% 2.19/1.00  sim_smt_subsumption:                    0
% 2.19/1.00  
%------------------------------------------------------------------------------
