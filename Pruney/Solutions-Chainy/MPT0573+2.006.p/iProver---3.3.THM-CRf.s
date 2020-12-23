%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:46 EST 2020

% Result     : Theorem 11.38s
% Output     : CNFRefutation 11.38s
% Verified   : 
% Statistics : Number of formulae       :   62 (  99 expanded)
%              Number of clauses        :   28 (  35 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  109 ( 165 expanded)
%              Number of equality atoms :   47 (  73 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    6 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f16])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f28,f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f26,f23])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).

fof(f30,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f31,plain,(
    ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_429,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_427,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_452,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_427,c_7])).

cnf(c_870,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,k6_subset_1(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_429,c_452])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_426,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_441,plain,
    ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_426,c_7])).

cnf(c_1301,plain,
    ( k2_xboole_0(X0,k6_subset_1(k2_xboole_0(X1,k6_subset_1(X0,X1)),X0)) = k2_xboole_0(X1,k6_subset_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_870,c_441])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_422,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_424,plain,
    ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1042,plain,
    ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_422,c_424])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_425,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1992,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_425])).

cnf(c_2903,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X1,k6_subset_1(X0,X1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_1992])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_428,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_457,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_428,c_7])).

cnf(c_1989,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,k2_xboole_0(X1,X2))) != iProver_top
    | r1_tarski(k6_subset_1(X0,k10_relat_1(sK2,X1)),k10_relat_1(sK2,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_457])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_423,plain,
    ( r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6253,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1989,c_423])).

cnf(c_36650,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2903,c_6253])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.38/2.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.38/2.03  
% 11.38/2.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.38/2.03  
% 11.38/2.03  ------  iProver source info
% 11.38/2.03  
% 11.38/2.03  git: date: 2020-06-30 10:37:57 +0100
% 11.38/2.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.38/2.03  git: non_committed_changes: false
% 11.38/2.03  git: last_make_outside_of_git: false
% 11.38/2.03  
% 11.38/2.03  ------ 
% 11.38/2.03  
% 11.38/2.03  ------ Input Options
% 11.38/2.03  
% 11.38/2.03  --out_options                           all
% 11.38/2.03  --tptp_safe_out                         true
% 11.38/2.03  --problem_path                          ""
% 11.38/2.03  --include_path                          ""
% 11.38/2.03  --clausifier                            res/vclausify_rel
% 11.38/2.03  --clausifier_options                    --mode clausify
% 11.38/2.03  --stdin                                 false
% 11.38/2.03  --stats_out                             sel
% 11.38/2.03  
% 11.38/2.03  ------ General Options
% 11.38/2.03  
% 11.38/2.03  --fof                                   false
% 11.38/2.03  --time_out_real                         604.99
% 11.38/2.03  --time_out_virtual                      -1.
% 11.38/2.03  --symbol_type_check                     false
% 11.38/2.03  --clausify_out                          false
% 11.38/2.03  --sig_cnt_out                           false
% 11.38/2.03  --trig_cnt_out                          false
% 11.38/2.03  --trig_cnt_out_tolerance                1.
% 11.38/2.03  --trig_cnt_out_sk_spl                   false
% 11.38/2.03  --abstr_cl_out                          false
% 11.38/2.03  
% 11.38/2.03  ------ Global Options
% 11.38/2.03  
% 11.38/2.03  --schedule                              none
% 11.38/2.03  --add_important_lit                     false
% 11.38/2.03  --prop_solver_per_cl                    1000
% 11.38/2.03  --min_unsat_core                        false
% 11.38/2.03  --soft_assumptions                      false
% 11.38/2.03  --soft_lemma_size                       3
% 11.38/2.03  --prop_impl_unit_size                   0
% 11.38/2.03  --prop_impl_unit                        []
% 11.38/2.03  --share_sel_clauses                     true
% 11.38/2.03  --reset_solvers                         false
% 11.38/2.03  --bc_imp_inh                            [conj_cone]
% 11.38/2.03  --conj_cone_tolerance                   3.
% 11.38/2.03  --extra_neg_conj                        none
% 11.38/2.03  --large_theory_mode                     true
% 11.38/2.03  --prolific_symb_bound                   200
% 11.38/2.03  --lt_threshold                          2000
% 11.38/2.03  --clause_weak_htbl                      true
% 11.38/2.03  --gc_record_bc_elim                     false
% 11.38/2.03  
% 11.38/2.03  ------ Preprocessing Options
% 11.38/2.03  
% 11.38/2.03  --preprocessing_flag                    true
% 11.38/2.03  --time_out_prep_mult                    0.1
% 11.38/2.03  --splitting_mode                        input
% 11.38/2.03  --splitting_grd                         true
% 11.38/2.03  --splitting_cvd                         false
% 11.38/2.03  --splitting_cvd_svl                     false
% 11.38/2.03  --splitting_nvd                         32
% 11.38/2.03  --sub_typing                            true
% 11.38/2.03  --prep_gs_sim                           false
% 11.38/2.03  --prep_unflatten                        true
% 11.38/2.03  --prep_res_sim                          true
% 11.38/2.03  --prep_upred                            true
% 11.38/2.03  --prep_sem_filter                       exhaustive
% 11.38/2.03  --prep_sem_filter_out                   false
% 11.38/2.03  --pred_elim                             false
% 11.38/2.03  --res_sim_input                         true
% 11.38/2.03  --eq_ax_congr_red                       true
% 11.38/2.03  --pure_diseq_elim                       true
% 11.38/2.03  --brand_transform                       false
% 11.38/2.03  --non_eq_to_eq                          false
% 11.38/2.03  --prep_def_merge                        true
% 11.38/2.03  --prep_def_merge_prop_impl              false
% 11.38/2.03  --prep_def_merge_mbd                    true
% 11.38/2.03  --prep_def_merge_tr_red                 false
% 11.38/2.03  --prep_def_merge_tr_cl                  false
% 11.38/2.03  --smt_preprocessing                     true
% 11.38/2.03  --smt_ac_axioms                         fast
% 11.38/2.03  --preprocessed_out                      false
% 11.38/2.03  --preprocessed_stats                    false
% 11.38/2.03  
% 11.38/2.03  ------ Abstraction refinement Options
% 11.38/2.03  
% 11.38/2.03  --abstr_ref                             []
% 11.38/2.03  --abstr_ref_prep                        false
% 11.38/2.03  --abstr_ref_until_sat                   false
% 11.38/2.03  --abstr_ref_sig_restrict                funpre
% 11.38/2.03  --abstr_ref_af_restrict_to_split_sk     false
% 11.38/2.03  --abstr_ref_under                       []
% 11.38/2.03  
% 11.38/2.03  ------ SAT Options
% 11.38/2.03  
% 11.38/2.03  --sat_mode                              false
% 11.38/2.03  --sat_fm_restart_options                ""
% 11.38/2.03  --sat_gr_def                            false
% 11.38/2.03  --sat_epr_types                         true
% 11.38/2.03  --sat_non_cyclic_types                  false
% 11.38/2.03  --sat_finite_models                     false
% 11.38/2.03  --sat_fm_lemmas                         false
% 11.38/2.03  --sat_fm_prep                           false
% 11.38/2.03  --sat_fm_uc_incr                        true
% 11.38/2.03  --sat_out_model                         small
% 11.38/2.03  --sat_out_clauses                       false
% 11.38/2.03  
% 11.38/2.03  ------ QBF Options
% 11.38/2.03  
% 11.38/2.03  --qbf_mode                              false
% 11.38/2.03  --qbf_elim_univ                         false
% 11.38/2.03  --qbf_dom_inst                          none
% 11.38/2.03  --qbf_dom_pre_inst                      false
% 11.38/2.03  --qbf_sk_in                             false
% 11.38/2.03  --qbf_pred_elim                         true
% 11.38/2.03  --qbf_split                             512
% 11.38/2.03  
% 11.38/2.03  ------ BMC1 Options
% 11.38/2.03  
% 11.38/2.03  --bmc1_incremental                      false
% 11.38/2.03  --bmc1_axioms                           reachable_all
% 11.38/2.03  --bmc1_min_bound                        0
% 11.38/2.03  --bmc1_max_bound                        -1
% 11.38/2.03  --bmc1_max_bound_default                -1
% 11.38/2.03  --bmc1_symbol_reachability              true
% 11.38/2.03  --bmc1_property_lemmas                  false
% 11.38/2.03  --bmc1_k_induction                      false
% 11.38/2.03  --bmc1_non_equiv_states                 false
% 11.38/2.03  --bmc1_deadlock                         false
% 11.38/2.03  --bmc1_ucm                              false
% 11.38/2.03  --bmc1_add_unsat_core                   none
% 11.38/2.03  --bmc1_unsat_core_children              false
% 11.38/2.03  --bmc1_unsat_core_extrapolate_axioms    false
% 11.38/2.03  --bmc1_out_stat                         full
% 11.38/2.03  --bmc1_ground_init                      false
% 11.38/2.03  --bmc1_pre_inst_next_state              false
% 11.38/2.03  --bmc1_pre_inst_state                   false
% 11.38/2.03  --bmc1_pre_inst_reach_state             false
% 11.38/2.03  --bmc1_out_unsat_core                   false
% 11.38/2.03  --bmc1_aig_witness_out                  false
% 11.38/2.03  --bmc1_verbose                          false
% 11.38/2.03  --bmc1_dump_clauses_tptp                false
% 11.38/2.03  --bmc1_dump_unsat_core_tptp             false
% 11.38/2.03  --bmc1_dump_file                        -
% 11.38/2.03  --bmc1_ucm_expand_uc_limit              128
% 11.38/2.03  --bmc1_ucm_n_expand_iterations          6
% 11.38/2.03  --bmc1_ucm_extend_mode                  1
% 11.38/2.03  --bmc1_ucm_init_mode                    2
% 11.38/2.03  --bmc1_ucm_cone_mode                    none
% 11.38/2.03  --bmc1_ucm_reduced_relation_type        0
% 11.38/2.03  --bmc1_ucm_relax_model                  4
% 11.38/2.03  --bmc1_ucm_full_tr_after_sat            true
% 11.38/2.03  --bmc1_ucm_expand_neg_assumptions       false
% 11.38/2.03  --bmc1_ucm_layered_model                none
% 11.38/2.03  --bmc1_ucm_max_lemma_size               10
% 11.38/2.03  
% 11.38/2.03  ------ AIG Options
% 11.38/2.03  
% 11.38/2.03  --aig_mode                              false
% 11.38/2.03  
% 11.38/2.03  ------ Instantiation Options
% 11.38/2.03  
% 11.38/2.03  --instantiation_flag                    true
% 11.38/2.03  --inst_sos_flag                         false
% 11.38/2.03  --inst_sos_phase                        true
% 11.38/2.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.38/2.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.38/2.03  --inst_lit_sel_side                     num_symb
% 11.38/2.03  --inst_solver_per_active                1400
% 11.38/2.03  --inst_solver_calls_frac                1.
% 11.38/2.03  --inst_passive_queue_type               priority_queues
% 11.38/2.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.38/2.03  --inst_passive_queues_freq              [25;2]
% 11.38/2.03  --inst_dismatching                      true
% 11.38/2.03  --inst_eager_unprocessed_to_passive     true
% 11.38/2.03  --inst_prop_sim_given                   true
% 11.38/2.03  --inst_prop_sim_new                     false
% 11.38/2.03  --inst_subs_new                         false
% 11.38/2.03  --inst_eq_res_simp                      false
% 11.38/2.03  --inst_subs_given                       false
% 11.38/2.03  --inst_orphan_elimination               true
% 11.38/2.03  --inst_learning_loop_flag               true
% 11.38/2.03  --inst_learning_start                   3000
% 11.38/2.03  --inst_learning_factor                  2
% 11.38/2.03  --inst_start_prop_sim_after_learn       3
% 11.38/2.03  --inst_sel_renew                        solver
% 11.38/2.03  --inst_lit_activity_flag                true
% 11.38/2.03  --inst_restr_to_given                   false
% 11.38/2.03  --inst_activity_threshold               500
% 11.38/2.03  --inst_out_proof                        true
% 11.38/2.03  
% 11.38/2.03  ------ Resolution Options
% 11.38/2.03  
% 11.38/2.03  --resolution_flag                       true
% 11.38/2.03  --res_lit_sel                           adaptive
% 11.38/2.03  --res_lit_sel_side                      none
% 11.38/2.03  --res_ordering                          kbo
% 11.38/2.03  --res_to_prop_solver                    active
% 11.38/2.03  --res_prop_simpl_new                    false
% 11.38/2.03  --res_prop_simpl_given                  true
% 11.38/2.03  --res_passive_queue_type                priority_queues
% 11.38/2.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.38/2.03  --res_passive_queues_freq               [15;5]
% 11.38/2.03  --res_forward_subs                      full
% 11.38/2.03  --res_backward_subs                     full
% 11.38/2.03  --res_forward_subs_resolution           true
% 11.38/2.03  --res_backward_subs_resolution          true
% 11.38/2.03  --res_orphan_elimination                true
% 11.38/2.03  --res_time_limit                        2.
% 11.38/2.03  --res_out_proof                         true
% 11.38/2.03  
% 11.38/2.03  ------ Superposition Options
% 11.38/2.03  
% 11.38/2.03  --superposition_flag                    true
% 11.38/2.03  --sup_passive_queue_type                priority_queues
% 11.38/2.03  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.38/2.03  --sup_passive_queues_freq               [1;4]
% 11.38/2.03  --demod_completeness_check              fast
% 11.38/2.03  --demod_use_ground                      true
% 11.38/2.03  --sup_to_prop_solver                    passive
% 11.38/2.03  --sup_prop_simpl_new                    true
% 11.38/2.03  --sup_prop_simpl_given                  true
% 11.38/2.03  --sup_fun_splitting                     false
% 11.38/2.03  --sup_smt_interval                      50000
% 11.38/2.03  
% 11.38/2.03  ------ Superposition Simplification Setup
% 11.38/2.03  
% 11.38/2.03  --sup_indices_passive                   []
% 11.38/2.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.38/2.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.38/2.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.38/2.03  --sup_full_triv                         [TrivRules;PropSubs]
% 11.38/2.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.38/2.03  --sup_full_bw                           [BwDemod]
% 11.38/2.03  --sup_immed_triv                        [TrivRules]
% 11.38/2.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.38/2.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.38/2.03  --sup_immed_bw_main                     []
% 11.38/2.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.38/2.03  --sup_input_triv                        [Unflattening;TrivRules]
% 11.38/2.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.38/2.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.38/2.03  
% 11.38/2.03  ------ Combination Options
% 11.38/2.03  
% 11.38/2.03  --comb_res_mult                         3
% 11.38/2.03  --comb_sup_mult                         2
% 11.38/2.03  --comb_inst_mult                        10
% 11.38/2.03  
% 11.38/2.03  ------ Debug Options
% 11.38/2.03  
% 11.38/2.03  --dbg_backtrace                         false
% 11.38/2.03  --dbg_dump_prop_clauses                 false
% 11.38/2.03  --dbg_dump_prop_clauses_file            -
% 11.38/2.03  --dbg_out_stat                          false
% 11.38/2.03  ------ Parsing...
% 11.38/2.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.38/2.03  
% 11.38/2.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.38/2.03  
% 11.38/2.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.38/2.03  
% 11.38/2.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.38/2.03  ------ Proving...
% 11.38/2.03  ------ Problem Properties 
% 11.38/2.03  
% 11.38/2.03  
% 11.38/2.03  clauses                                 10
% 11.38/2.03  conjectures                             2
% 11.38/2.03  EPR                                     3
% 11.38/2.03  Horn                                    10
% 11.38/2.03  unary                                   5
% 11.38/2.03  binary                                  4
% 11.38/2.03  lits                                    16
% 11.38/2.03  lits eq                                 4
% 11.38/2.03  fd_pure                                 0
% 11.38/2.03  fd_pseudo                               0
% 11.38/2.03  fd_cond                                 0
% 11.38/2.03  fd_pseudo_cond                          1
% 11.38/2.03  AC symbols                              0
% 11.38/2.03  
% 11.38/2.03  ------ Input Options Time Limit: Unbounded
% 11.38/2.03  
% 11.38/2.03  
% 11.38/2.03  ------ 
% 11.38/2.03  Current options:
% 11.38/2.03  ------ 
% 11.38/2.03  
% 11.38/2.03  ------ Input Options
% 11.38/2.03  
% 11.38/2.03  --out_options                           all
% 11.38/2.03  --tptp_safe_out                         true
% 11.38/2.03  --problem_path                          ""
% 11.38/2.03  --include_path                          ""
% 11.38/2.03  --clausifier                            res/vclausify_rel
% 11.38/2.03  --clausifier_options                    --mode clausify
% 11.38/2.03  --stdin                                 false
% 11.38/2.03  --stats_out                             sel
% 11.38/2.03  
% 11.38/2.03  ------ General Options
% 11.38/2.03  
% 11.38/2.03  --fof                                   false
% 11.38/2.03  --time_out_real                         604.99
% 11.38/2.03  --time_out_virtual                      -1.
% 11.38/2.03  --symbol_type_check                     false
% 11.38/2.03  --clausify_out                          false
% 11.38/2.03  --sig_cnt_out                           false
% 11.38/2.03  --trig_cnt_out                          false
% 11.38/2.03  --trig_cnt_out_tolerance                1.
% 11.38/2.03  --trig_cnt_out_sk_spl                   false
% 11.38/2.03  --abstr_cl_out                          false
% 11.38/2.03  
% 11.38/2.03  ------ Global Options
% 11.38/2.03  
% 11.38/2.03  --schedule                              none
% 11.38/2.03  --add_important_lit                     false
% 11.38/2.03  --prop_solver_per_cl                    1000
% 11.38/2.03  --min_unsat_core                        false
% 11.38/2.03  --soft_assumptions                      false
% 11.38/2.03  --soft_lemma_size                       3
% 11.38/2.03  --prop_impl_unit_size                   0
% 11.38/2.03  --prop_impl_unit                        []
% 11.38/2.03  --share_sel_clauses                     true
% 11.38/2.03  --reset_solvers                         false
% 11.38/2.03  --bc_imp_inh                            [conj_cone]
% 11.38/2.03  --conj_cone_tolerance                   3.
% 11.38/2.03  --extra_neg_conj                        none
% 11.38/2.03  --large_theory_mode                     true
% 11.38/2.03  --prolific_symb_bound                   200
% 11.38/2.03  --lt_threshold                          2000
% 11.38/2.03  --clause_weak_htbl                      true
% 11.38/2.03  --gc_record_bc_elim                     false
% 11.38/2.03  
% 11.38/2.03  ------ Preprocessing Options
% 11.38/2.03  
% 11.38/2.03  --preprocessing_flag                    true
% 11.38/2.03  --time_out_prep_mult                    0.1
% 11.38/2.03  --splitting_mode                        input
% 11.38/2.03  --splitting_grd                         true
% 11.38/2.03  --splitting_cvd                         false
% 11.38/2.03  --splitting_cvd_svl                     false
% 11.38/2.03  --splitting_nvd                         32
% 11.38/2.03  --sub_typing                            true
% 11.38/2.03  --prep_gs_sim                           false
% 11.38/2.03  --prep_unflatten                        true
% 11.38/2.03  --prep_res_sim                          true
% 11.38/2.03  --prep_upred                            true
% 11.38/2.03  --prep_sem_filter                       exhaustive
% 11.38/2.03  --prep_sem_filter_out                   false
% 11.38/2.03  --pred_elim                             false
% 11.38/2.03  --res_sim_input                         true
% 11.38/2.03  --eq_ax_congr_red                       true
% 11.38/2.03  --pure_diseq_elim                       true
% 11.38/2.03  --brand_transform                       false
% 11.38/2.03  --non_eq_to_eq                          false
% 11.38/2.03  --prep_def_merge                        true
% 11.38/2.03  --prep_def_merge_prop_impl              false
% 11.38/2.03  --prep_def_merge_mbd                    true
% 11.38/2.03  --prep_def_merge_tr_red                 false
% 11.38/2.03  --prep_def_merge_tr_cl                  false
% 11.38/2.03  --smt_preprocessing                     true
% 11.38/2.03  --smt_ac_axioms                         fast
% 11.38/2.03  --preprocessed_out                      false
% 11.38/2.03  --preprocessed_stats                    false
% 11.38/2.03  
% 11.38/2.03  ------ Abstraction refinement Options
% 11.38/2.03  
% 11.38/2.03  --abstr_ref                             []
% 11.38/2.03  --abstr_ref_prep                        false
% 11.38/2.03  --abstr_ref_until_sat                   false
% 11.38/2.03  --abstr_ref_sig_restrict                funpre
% 11.38/2.03  --abstr_ref_af_restrict_to_split_sk     false
% 11.38/2.03  --abstr_ref_under                       []
% 11.38/2.03  
% 11.38/2.03  ------ SAT Options
% 11.38/2.03  
% 11.38/2.03  --sat_mode                              false
% 11.38/2.03  --sat_fm_restart_options                ""
% 11.38/2.03  --sat_gr_def                            false
% 11.38/2.03  --sat_epr_types                         true
% 11.38/2.03  --sat_non_cyclic_types                  false
% 11.38/2.03  --sat_finite_models                     false
% 11.38/2.03  --sat_fm_lemmas                         false
% 11.38/2.03  --sat_fm_prep                           false
% 11.38/2.03  --sat_fm_uc_incr                        true
% 11.38/2.03  --sat_out_model                         small
% 11.38/2.03  --sat_out_clauses                       false
% 11.38/2.03  
% 11.38/2.03  ------ QBF Options
% 11.38/2.03  
% 11.38/2.03  --qbf_mode                              false
% 11.38/2.03  --qbf_elim_univ                         false
% 11.38/2.03  --qbf_dom_inst                          none
% 11.38/2.03  --qbf_dom_pre_inst                      false
% 11.38/2.03  --qbf_sk_in                             false
% 11.38/2.03  --qbf_pred_elim                         true
% 11.38/2.03  --qbf_split                             512
% 11.38/2.03  
% 11.38/2.03  ------ BMC1 Options
% 11.38/2.03  
% 11.38/2.03  --bmc1_incremental                      false
% 11.38/2.03  --bmc1_axioms                           reachable_all
% 11.38/2.03  --bmc1_min_bound                        0
% 11.38/2.03  --bmc1_max_bound                        -1
% 11.38/2.03  --bmc1_max_bound_default                -1
% 11.38/2.03  --bmc1_symbol_reachability              true
% 11.38/2.03  --bmc1_property_lemmas                  false
% 11.38/2.03  --bmc1_k_induction                      false
% 11.38/2.03  --bmc1_non_equiv_states                 false
% 11.38/2.03  --bmc1_deadlock                         false
% 11.38/2.03  --bmc1_ucm                              false
% 11.38/2.03  --bmc1_add_unsat_core                   none
% 11.38/2.03  --bmc1_unsat_core_children              false
% 11.38/2.03  --bmc1_unsat_core_extrapolate_axioms    false
% 11.38/2.03  --bmc1_out_stat                         full
% 11.38/2.03  --bmc1_ground_init                      false
% 11.38/2.03  --bmc1_pre_inst_next_state              false
% 11.38/2.03  --bmc1_pre_inst_state                   false
% 11.38/2.03  --bmc1_pre_inst_reach_state             false
% 11.38/2.03  --bmc1_out_unsat_core                   false
% 11.38/2.03  --bmc1_aig_witness_out                  false
% 11.38/2.03  --bmc1_verbose                          false
% 11.38/2.03  --bmc1_dump_clauses_tptp                false
% 11.38/2.03  --bmc1_dump_unsat_core_tptp             false
% 11.38/2.03  --bmc1_dump_file                        -
% 11.38/2.03  --bmc1_ucm_expand_uc_limit              128
% 11.38/2.03  --bmc1_ucm_n_expand_iterations          6
% 11.38/2.03  --bmc1_ucm_extend_mode                  1
% 11.38/2.03  --bmc1_ucm_init_mode                    2
% 11.38/2.03  --bmc1_ucm_cone_mode                    none
% 11.38/2.03  --bmc1_ucm_reduced_relation_type        0
% 11.38/2.03  --bmc1_ucm_relax_model                  4
% 11.38/2.03  --bmc1_ucm_full_tr_after_sat            true
% 11.38/2.03  --bmc1_ucm_expand_neg_assumptions       false
% 11.38/2.03  --bmc1_ucm_layered_model                none
% 11.38/2.03  --bmc1_ucm_max_lemma_size               10
% 11.38/2.03  
% 11.38/2.03  ------ AIG Options
% 11.38/2.03  
% 11.38/2.03  --aig_mode                              false
% 11.38/2.03  
% 11.38/2.03  ------ Instantiation Options
% 11.38/2.03  
% 11.38/2.03  --instantiation_flag                    true
% 11.38/2.03  --inst_sos_flag                         false
% 11.38/2.03  --inst_sos_phase                        true
% 11.38/2.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.38/2.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.38/2.03  --inst_lit_sel_side                     num_symb
% 11.38/2.03  --inst_solver_per_active                1400
% 11.38/2.03  --inst_solver_calls_frac                1.
% 11.38/2.03  --inst_passive_queue_type               priority_queues
% 11.38/2.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.38/2.03  --inst_passive_queues_freq              [25;2]
% 11.38/2.03  --inst_dismatching                      true
% 11.38/2.03  --inst_eager_unprocessed_to_passive     true
% 11.38/2.03  --inst_prop_sim_given                   true
% 11.38/2.03  --inst_prop_sim_new                     false
% 11.38/2.03  --inst_subs_new                         false
% 11.38/2.03  --inst_eq_res_simp                      false
% 11.38/2.03  --inst_subs_given                       false
% 11.38/2.03  --inst_orphan_elimination               true
% 11.38/2.03  --inst_learning_loop_flag               true
% 11.38/2.03  --inst_learning_start                   3000
% 11.38/2.03  --inst_learning_factor                  2
% 11.38/2.03  --inst_start_prop_sim_after_learn       3
% 11.38/2.03  --inst_sel_renew                        solver
% 11.38/2.03  --inst_lit_activity_flag                true
% 11.38/2.03  --inst_restr_to_given                   false
% 11.38/2.03  --inst_activity_threshold               500
% 11.38/2.03  --inst_out_proof                        true
% 11.38/2.03  
% 11.38/2.03  ------ Resolution Options
% 11.38/2.03  
% 11.38/2.03  --resolution_flag                       true
% 11.38/2.03  --res_lit_sel                           adaptive
% 11.38/2.03  --res_lit_sel_side                      none
% 11.38/2.03  --res_ordering                          kbo
% 11.38/2.03  --res_to_prop_solver                    active
% 11.38/2.03  --res_prop_simpl_new                    false
% 11.38/2.03  --res_prop_simpl_given                  true
% 11.38/2.03  --res_passive_queue_type                priority_queues
% 11.38/2.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.38/2.03  --res_passive_queues_freq               [15;5]
% 11.38/2.03  --res_forward_subs                      full
% 11.38/2.03  --res_backward_subs                     full
% 11.38/2.03  --res_forward_subs_resolution           true
% 11.38/2.03  --res_backward_subs_resolution          true
% 11.38/2.03  --res_orphan_elimination                true
% 11.38/2.03  --res_time_limit                        2.
% 11.38/2.03  --res_out_proof                         true
% 11.38/2.03  
% 11.38/2.03  ------ Superposition Options
% 11.38/2.03  
% 11.38/2.03  --superposition_flag                    true
% 11.38/2.03  --sup_passive_queue_type                priority_queues
% 11.38/2.03  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.38/2.03  --sup_passive_queues_freq               [1;4]
% 11.38/2.03  --demod_completeness_check              fast
% 11.38/2.03  --demod_use_ground                      true
% 11.38/2.03  --sup_to_prop_solver                    passive
% 11.38/2.03  --sup_prop_simpl_new                    true
% 11.38/2.03  --sup_prop_simpl_given                  true
% 11.38/2.03  --sup_fun_splitting                     false
% 11.38/2.03  --sup_smt_interval                      50000
% 11.38/2.03  
% 11.38/2.03  ------ Superposition Simplification Setup
% 11.38/2.03  
% 11.38/2.03  --sup_indices_passive                   []
% 11.38/2.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.38/2.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.38/2.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.38/2.03  --sup_full_triv                         [TrivRules;PropSubs]
% 11.38/2.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.38/2.03  --sup_full_bw                           [BwDemod]
% 11.38/2.03  --sup_immed_triv                        [TrivRules]
% 11.38/2.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.38/2.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.38/2.03  --sup_immed_bw_main                     []
% 11.38/2.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.38/2.03  --sup_input_triv                        [Unflattening;TrivRules]
% 11.38/2.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.38/2.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.38/2.03  
% 11.38/2.03  ------ Combination Options
% 11.38/2.03  
% 11.38/2.03  --comb_res_mult                         3
% 11.38/2.03  --comb_sup_mult                         2
% 11.38/2.03  --comb_inst_mult                        10
% 11.38/2.03  
% 11.38/2.03  ------ Debug Options
% 11.38/2.03  
% 11.38/2.03  --dbg_backtrace                         false
% 11.38/2.03  --dbg_dump_prop_clauses                 false
% 11.38/2.03  --dbg_dump_prop_clauses_file            -
% 11.38/2.03  --dbg_out_stat                          false
% 11.38/2.03  
% 11.38/2.03  
% 11.38/2.03  
% 11.38/2.03  
% 11.38/2.03  ------ Proving...
% 11.38/2.03  
% 11.38/2.03  
% 11.38/2.03  % SZS status Theorem for theBenchmark.p
% 11.38/2.03  
% 11.38/2.03   Resolution empty clause
% 11.38/2.03  
% 11.38/2.03  % SZS output start CNFRefutation for theBenchmark.p
% 11.38/2.03  
% 11.38/2.03  fof(f1,axiom,(
% 11.38/2.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.38/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/2.03  
% 11.38/2.03  fof(f16,plain,(
% 11.38/2.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.38/2.03    inference(nnf_transformation,[],[f1])).
% 11.38/2.03  
% 11.38/2.03  fof(f17,plain,(
% 11.38/2.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.38/2.03    inference(flattening,[],[f16])).
% 11.38/2.03  
% 11.38/2.03  fof(f21,plain,(
% 11.38/2.03    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.38/2.03    inference(cnf_transformation,[],[f17])).
% 11.38/2.03  
% 11.38/2.03  fof(f36,plain,(
% 11.38/2.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.38/2.03    inference(equality_resolution,[],[f21])).
% 11.38/2.03  
% 11.38/2.03  fof(f4,axiom,(
% 11.38/2.03    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.38/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/2.03  
% 11.38/2.03  fof(f12,plain,(
% 11.38/2.03    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 11.38/2.03    inference(ennf_transformation,[],[f4])).
% 11.38/2.03  
% 11.38/2.03  fof(f25,plain,(
% 11.38/2.03    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 11.38/2.03    inference(cnf_transformation,[],[f12])).
% 11.38/2.03  
% 11.38/2.03  fof(f2,axiom,(
% 11.38/2.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.38/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/2.03  
% 11.38/2.03  fof(f23,plain,(
% 11.38/2.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.38/2.03    inference(cnf_transformation,[],[f2])).
% 11.38/2.03  
% 11.38/2.03  fof(f33,plain,(
% 11.38/2.03    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) )),
% 11.38/2.03    inference(definition_unfolding,[],[f25,f23])).
% 11.38/2.03  
% 11.38/2.03  fof(f7,axiom,(
% 11.38/2.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 11.38/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/2.03  
% 11.38/2.03  fof(f28,plain,(
% 11.38/2.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 11.38/2.03    inference(cnf_transformation,[],[f7])).
% 11.38/2.03  
% 11.38/2.03  fof(f35,plain,(
% 11.38/2.03    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1)) )),
% 11.38/2.03    inference(definition_unfolding,[],[f28,f23])).
% 11.38/2.03  
% 11.38/2.03  fof(f5,axiom,(
% 11.38/2.03    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 11.38/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/2.03  
% 11.38/2.03  fof(f13,plain,(
% 11.38/2.03    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 11.38/2.03    inference(ennf_transformation,[],[f5])).
% 11.38/2.03  
% 11.38/2.03  fof(f26,plain,(
% 11.38/2.03    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 11.38/2.03    inference(cnf_transformation,[],[f13])).
% 11.38/2.03  
% 11.38/2.03  fof(f34,plain,(
% 11.38/2.03    ( ! [X0,X1] : (k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 | ~r1_tarski(X0,X1)) )),
% 11.38/2.03    inference(definition_unfolding,[],[f26,f23])).
% 11.38/2.03  
% 11.38/2.03  fof(f9,conjecture,(
% 11.38/2.03    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))))),
% 11.38/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/2.03  
% 11.38/2.03  fof(f10,negated_conjecture,(
% 11.38/2.03    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))))),
% 11.38/2.03    inference(negated_conjecture,[],[f9])).
% 11.38/2.03  
% 11.38/2.03  fof(f15,plain,(
% 11.38/2.03    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2))),
% 11.38/2.03    inference(ennf_transformation,[],[f10])).
% 11.38/2.03  
% 11.38/2.03  fof(f18,plain,(
% 11.38/2.03    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2)) => (~r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) & v1_relat_1(sK2))),
% 11.38/2.03    introduced(choice_axiom,[])).
% 11.38/2.03  
% 11.38/2.03  fof(f19,plain,(
% 11.38/2.03    ~r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) & v1_relat_1(sK2)),
% 11.38/2.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f18])).
% 11.38/2.03  
% 11.38/2.03  fof(f30,plain,(
% 11.38/2.03    v1_relat_1(sK2)),
% 11.38/2.03    inference(cnf_transformation,[],[f19])).
% 11.38/2.03  
% 11.38/2.03  fof(f8,axiom,(
% 11.38/2.03    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)))),
% 11.38/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/2.03  
% 11.38/2.03  fof(f14,plain,(
% 11.38/2.03    ! [X0,X1,X2] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 11.38/2.03    inference(ennf_transformation,[],[f8])).
% 11.38/2.03  
% 11.38/2.03  fof(f29,plain,(
% 11.38/2.03    ( ! [X2,X0,X1] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 11.38/2.03    inference(cnf_transformation,[],[f14])).
% 11.38/2.03  
% 11.38/2.03  fof(f6,axiom,(
% 11.38/2.03    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 11.38/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/2.03  
% 11.38/2.03  fof(f27,plain,(
% 11.38/2.03    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 11.38/2.03    inference(cnf_transformation,[],[f6])).
% 11.38/2.03  
% 11.38/2.03  fof(f3,axiom,(
% 11.38/2.03    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 11.38/2.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/2.03  
% 11.38/2.03  fof(f11,plain,(
% 11.38/2.03    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.38/2.03    inference(ennf_transformation,[],[f3])).
% 11.38/2.03  
% 11.38/2.03  fof(f24,plain,(
% 11.38/2.03    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 11.38/2.03    inference(cnf_transformation,[],[f11])).
% 11.38/2.03  
% 11.38/2.03  fof(f32,plain,(
% 11.38/2.03    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 11.38/2.03    inference(definition_unfolding,[],[f24,f23])).
% 11.38/2.03  
% 11.38/2.03  fof(f31,plain,(
% 11.38/2.03    ~r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 11.38/2.03    inference(cnf_transformation,[],[f19])).
% 11.38/2.03  
% 11.38/2.03  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f36]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_429,plain,
% 11.38/2.03      ( r1_tarski(X0,X0) = iProver_top ),
% 11.38/2.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_4,plain,
% 11.38/2.03      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 11.38/2.03      | ~ r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
% 11.38/2.03      inference(cnf_transformation,[],[f33]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_427,plain,
% 11.38/2.03      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 11.38/2.03      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) != iProver_top ),
% 11.38/2.03      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_7,plain,
% 11.38/2.03      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
% 11.38/2.03      inference(cnf_transformation,[],[f35]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_452,plain,
% 11.38/2.03      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 11.38/2.03      | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
% 11.38/2.03      inference(light_normalisation,[status(thm)],[c_427,c_7]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_870,plain,
% 11.38/2.03      ( r1_tarski(X0,k2_xboole_0(X1,k6_subset_1(X0,X1))) = iProver_top ),
% 11.38/2.03      inference(superposition,[status(thm)],[c_429,c_452]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_5,plain,
% 11.38/2.03      ( ~ r1_tarski(X0,X1)
% 11.38/2.03      | k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ),
% 11.38/2.03      inference(cnf_transformation,[],[f34]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_426,plain,
% 11.38/2.03      ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1
% 11.38/2.03      | r1_tarski(X0,X1) != iProver_top ),
% 11.38/2.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_441,plain,
% 11.38/2.03      ( k2_xboole_0(X0,k6_subset_1(X1,X0)) = X1
% 11.38/2.03      | r1_tarski(X0,X1) != iProver_top ),
% 11.38/2.03      inference(demodulation,[status(thm)],[c_426,c_7]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_1301,plain,
% 11.38/2.03      ( k2_xboole_0(X0,k6_subset_1(k2_xboole_0(X1,k6_subset_1(X0,X1)),X0)) = k2_xboole_0(X1,k6_subset_1(X0,X1)) ),
% 11.38/2.03      inference(superposition,[status(thm)],[c_870,c_441]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_10,negated_conjecture,
% 11.38/2.03      ( v1_relat_1(sK2) ),
% 11.38/2.03      inference(cnf_transformation,[],[f30]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_422,plain,
% 11.38/2.03      ( v1_relat_1(sK2) = iProver_top ),
% 11.38/2.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_8,plain,
% 11.38/2.03      ( ~ v1_relat_1(X0)
% 11.38/2.03      | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 11.38/2.03      inference(cnf_transformation,[],[f29]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_424,plain,
% 11.38/2.03      ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
% 11.38/2.03      | v1_relat_1(X0) != iProver_top ),
% 11.38/2.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_1042,plain,
% 11.38/2.03      ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_xboole_0(X0,X1)) ),
% 11.38/2.03      inference(superposition,[status(thm)],[c_422,c_424]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_6,plain,
% 11.38/2.03      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 11.38/2.03      inference(cnf_transformation,[],[f27]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_425,plain,
% 11.38/2.03      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 11.38/2.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_1992,plain,
% 11.38/2.03      ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X0,X1))) = iProver_top ),
% 11.38/2.03      inference(superposition,[status(thm)],[c_1042,c_425]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_2903,plain,
% 11.38/2.03      ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X1,k6_subset_1(X0,X1)))) = iProver_top ),
% 11.38/2.03      inference(superposition,[status(thm)],[c_1301,c_1992]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_3,plain,
% 11.38/2.03      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 11.38/2.03      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
% 11.38/2.03      inference(cnf_transformation,[],[f32]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_428,plain,
% 11.38/2.03      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 11.38/2.03      | r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = iProver_top ),
% 11.38/2.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_457,plain,
% 11.38/2.03      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 11.38/2.03      | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
% 11.38/2.03      inference(light_normalisation,[status(thm)],[c_428,c_7]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_1989,plain,
% 11.38/2.03      ( r1_tarski(X0,k10_relat_1(sK2,k2_xboole_0(X1,X2))) != iProver_top
% 11.38/2.03      | r1_tarski(k6_subset_1(X0,k10_relat_1(sK2,X1)),k10_relat_1(sK2,X2)) = iProver_top ),
% 11.38/2.03      inference(superposition,[status(thm)],[c_1042,c_457]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_9,negated_conjecture,
% 11.38/2.03      ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
% 11.38/2.03      inference(cnf_transformation,[],[f31]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_423,plain,
% 11.38/2.03      ( r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) != iProver_top ),
% 11.38/2.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_6253,plain,
% 11.38/2.03      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) != iProver_top ),
% 11.38/2.03      inference(superposition,[status(thm)],[c_1989,c_423]) ).
% 11.38/2.03  
% 11.38/2.03  cnf(c_36650,plain,
% 11.38/2.03      ( $false ),
% 11.38/2.03      inference(superposition,[status(thm)],[c_2903,c_6253]) ).
% 11.38/2.03  
% 11.38/2.03  
% 11.38/2.03  % SZS output end CNFRefutation for theBenchmark.p
% 11.38/2.03  
% 11.38/2.03  ------                               Statistics
% 11.38/2.03  
% 11.38/2.03  ------ Selected
% 11.38/2.03  
% 11.38/2.03  total_time:                             1.099
% 11.38/2.03  
%------------------------------------------------------------------------------
