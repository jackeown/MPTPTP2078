%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:47:46 EST 2020

% Result     : Theorem 27.48s
% Output     : CNFRefutation 27.48s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 113 expanded)
%              Number of clauses        :   27 (  33 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  111 ( 177 expanded)
%              Number of equality atoms :   50 (  86 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f30])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f25,f36])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))),X2) ) ),
    inference(definition_unfolding,[],[f28,f37])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f31,f37])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1)))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1)))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f20])).

fof(f34,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f27,f37])).

fof(f35,plain,(
    ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_435,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2))
    | ~ r1_tarski(k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))),X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_432,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_461,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_432,c_7])).

cnf(c_846,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,k6_subset_1(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_435,c_461])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_434,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1120,plain,
    ( k2_xboole_0(X0,k2_xboole_0(X1,k6_subset_1(X0,X1))) = k2_xboole_0(X1,k6_subset_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_846,c_434])).

cnf(c_10,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_428,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_430,plain,
    ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1040,plain,
    ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_428,c_430])).

cnf(c_6,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_431,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2541,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_431])).

cnf(c_2926,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X1,k6_subset_1(X0,X1)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_2541])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
    | r1_tarski(k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))),X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_433,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_466,plain,
    ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
    | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_433,c_7])).

cnf(c_2542,plain,
    ( r1_tarski(X0,k10_relat_1(sK2,k2_xboole_0(X1,X2))) != iProver_top
    | r1_tarski(k6_subset_1(X0,k10_relat_1(sK2,X1)),k10_relat_1(sK2,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1040,c_466])).

cnf(c_9,negated_conjecture,
    ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_429,plain,
    ( r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_45915,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2542,c_429])).

cnf(c_81433,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_2926,c_45915])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:21:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 27.48/4.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.48/4.01  
% 27.48/4.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.48/4.01  
% 27.48/4.01  ------  iProver source info
% 27.48/4.01  
% 27.48/4.01  git: date: 2020-06-30 10:37:57 +0100
% 27.48/4.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.48/4.01  git: non_committed_changes: false
% 27.48/4.01  git: last_make_outside_of_git: false
% 27.48/4.01  
% 27.48/4.01  ------ 
% 27.48/4.01  
% 27.48/4.01  ------ Input Options
% 27.48/4.01  
% 27.48/4.01  --out_options                           all
% 27.48/4.01  --tptp_safe_out                         true
% 27.48/4.01  --problem_path                          ""
% 27.48/4.01  --include_path                          ""
% 27.48/4.01  --clausifier                            res/vclausify_rel
% 27.48/4.01  --clausifier_options                    --mode clausify
% 27.48/4.01  --stdin                                 false
% 27.48/4.01  --stats_out                             sel
% 27.48/4.01  
% 27.48/4.01  ------ General Options
% 27.48/4.01  
% 27.48/4.01  --fof                                   false
% 27.48/4.01  --time_out_real                         604.99
% 27.48/4.01  --time_out_virtual                      -1.
% 27.48/4.01  --symbol_type_check                     false
% 27.48/4.01  --clausify_out                          false
% 27.48/4.01  --sig_cnt_out                           false
% 27.48/4.01  --trig_cnt_out                          false
% 27.48/4.01  --trig_cnt_out_tolerance                1.
% 27.48/4.01  --trig_cnt_out_sk_spl                   false
% 27.48/4.01  --abstr_cl_out                          false
% 27.48/4.01  
% 27.48/4.01  ------ Global Options
% 27.48/4.01  
% 27.48/4.01  --schedule                              none
% 27.48/4.01  --add_important_lit                     false
% 27.48/4.01  --prop_solver_per_cl                    1000
% 27.48/4.01  --min_unsat_core                        false
% 27.48/4.01  --soft_assumptions                      false
% 27.48/4.01  --soft_lemma_size                       3
% 27.48/4.01  --prop_impl_unit_size                   0
% 27.48/4.01  --prop_impl_unit                        []
% 27.48/4.01  --share_sel_clauses                     true
% 27.48/4.01  --reset_solvers                         false
% 27.48/4.01  --bc_imp_inh                            [conj_cone]
% 27.48/4.01  --conj_cone_tolerance                   3.
% 27.48/4.01  --extra_neg_conj                        none
% 27.48/4.01  --large_theory_mode                     true
% 27.48/4.01  --prolific_symb_bound                   200
% 27.48/4.01  --lt_threshold                          2000
% 27.48/4.01  --clause_weak_htbl                      true
% 27.48/4.01  --gc_record_bc_elim                     false
% 27.48/4.01  
% 27.48/4.01  ------ Preprocessing Options
% 27.48/4.01  
% 27.48/4.01  --preprocessing_flag                    true
% 27.48/4.01  --time_out_prep_mult                    0.1
% 27.48/4.01  --splitting_mode                        input
% 27.48/4.01  --splitting_grd                         true
% 27.48/4.01  --splitting_cvd                         false
% 27.48/4.01  --splitting_cvd_svl                     false
% 27.48/4.01  --splitting_nvd                         32
% 27.48/4.01  --sub_typing                            true
% 27.48/4.01  --prep_gs_sim                           false
% 27.48/4.01  --prep_unflatten                        true
% 27.48/4.01  --prep_res_sim                          true
% 27.48/4.01  --prep_upred                            true
% 27.48/4.01  --prep_sem_filter                       exhaustive
% 27.48/4.01  --prep_sem_filter_out                   false
% 27.48/4.01  --pred_elim                             false
% 27.48/4.01  --res_sim_input                         true
% 27.48/4.01  --eq_ax_congr_red                       true
% 27.48/4.01  --pure_diseq_elim                       true
% 27.48/4.01  --brand_transform                       false
% 27.48/4.01  --non_eq_to_eq                          false
% 27.48/4.01  --prep_def_merge                        true
% 27.48/4.01  --prep_def_merge_prop_impl              false
% 27.48/4.01  --prep_def_merge_mbd                    true
% 27.48/4.01  --prep_def_merge_tr_red                 false
% 27.48/4.01  --prep_def_merge_tr_cl                  false
% 27.48/4.01  --smt_preprocessing                     true
% 27.48/4.01  --smt_ac_axioms                         fast
% 27.48/4.01  --preprocessed_out                      false
% 27.48/4.01  --preprocessed_stats                    false
% 27.48/4.01  
% 27.48/4.01  ------ Abstraction refinement Options
% 27.48/4.01  
% 27.48/4.01  --abstr_ref                             []
% 27.48/4.01  --abstr_ref_prep                        false
% 27.48/4.01  --abstr_ref_until_sat                   false
% 27.48/4.01  --abstr_ref_sig_restrict                funpre
% 27.48/4.01  --abstr_ref_af_restrict_to_split_sk     false
% 27.48/4.01  --abstr_ref_under                       []
% 27.48/4.01  
% 27.48/4.01  ------ SAT Options
% 27.48/4.01  
% 27.48/4.01  --sat_mode                              false
% 27.48/4.01  --sat_fm_restart_options                ""
% 27.48/4.01  --sat_gr_def                            false
% 27.48/4.01  --sat_epr_types                         true
% 27.48/4.01  --sat_non_cyclic_types                  false
% 27.48/4.01  --sat_finite_models                     false
% 27.48/4.01  --sat_fm_lemmas                         false
% 27.48/4.01  --sat_fm_prep                           false
% 27.48/4.01  --sat_fm_uc_incr                        true
% 27.48/4.01  --sat_out_model                         small
% 27.48/4.01  --sat_out_clauses                       false
% 27.48/4.01  
% 27.48/4.01  ------ QBF Options
% 27.48/4.01  
% 27.48/4.01  --qbf_mode                              false
% 27.48/4.01  --qbf_elim_univ                         false
% 27.48/4.01  --qbf_dom_inst                          none
% 27.48/4.01  --qbf_dom_pre_inst                      false
% 27.48/4.01  --qbf_sk_in                             false
% 27.48/4.01  --qbf_pred_elim                         true
% 27.48/4.01  --qbf_split                             512
% 27.48/4.01  
% 27.48/4.01  ------ BMC1 Options
% 27.48/4.01  
% 27.48/4.01  --bmc1_incremental                      false
% 27.48/4.01  --bmc1_axioms                           reachable_all
% 27.48/4.01  --bmc1_min_bound                        0
% 27.48/4.01  --bmc1_max_bound                        -1
% 27.48/4.01  --bmc1_max_bound_default                -1
% 27.48/4.01  --bmc1_symbol_reachability              true
% 27.48/4.01  --bmc1_property_lemmas                  false
% 27.48/4.01  --bmc1_k_induction                      false
% 27.48/4.01  --bmc1_non_equiv_states                 false
% 27.48/4.01  --bmc1_deadlock                         false
% 27.48/4.01  --bmc1_ucm                              false
% 27.48/4.01  --bmc1_add_unsat_core                   none
% 27.48/4.01  --bmc1_unsat_core_children              false
% 27.48/4.01  --bmc1_unsat_core_extrapolate_axioms    false
% 27.48/4.01  --bmc1_out_stat                         full
% 27.48/4.01  --bmc1_ground_init                      false
% 27.48/4.01  --bmc1_pre_inst_next_state              false
% 27.48/4.01  --bmc1_pre_inst_state                   false
% 27.48/4.01  --bmc1_pre_inst_reach_state             false
% 27.48/4.01  --bmc1_out_unsat_core                   false
% 27.48/4.01  --bmc1_aig_witness_out                  false
% 27.48/4.01  --bmc1_verbose                          false
% 27.48/4.01  --bmc1_dump_clauses_tptp                false
% 27.48/4.01  --bmc1_dump_unsat_core_tptp             false
% 27.48/4.01  --bmc1_dump_file                        -
% 27.48/4.01  --bmc1_ucm_expand_uc_limit              128
% 27.48/4.01  --bmc1_ucm_n_expand_iterations          6
% 27.48/4.01  --bmc1_ucm_extend_mode                  1
% 27.48/4.01  --bmc1_ucm_init_mode                    2
% 27.48/4.01  --bmc1_ucm_cone_mode                    none
% 27.48/4.01  --bmc1_ucm_reduced_relation_type        0
% 27.48/4.01  --bmc1_ucm_relax_model                  4
% 27.48/4.01  --bmc1_ucm_full_tr_after_sat            true
% 27.48/4.01  --bmc1_ucm_expand_neg_assumptions       false
% 27.48/4.01  --bmc1_ucm_layered_model                none
% 27.48/4.01  --bmc1_ucm_max_lemma_size               10
% 27.48/4.01  
% 27.48/4.01  ------ AIG Options
% 27.48/4.01  
% 27.48/4.01  --aig_mode                              false
% 27.48/4.01  
% 27.48/4.01  ------ Instantiation Options
% 27.48/4.01  
% 27.48/4.01  --instantiation_flag                    true
% 27.48/4.01  --inst_sos_flag                         false
% 27.48/4.01  --inst_sos_phase                        true
% 27.48/4.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.48/4.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.48/4.01  --inst_lit_sel_side                     num_symb
% 27.48/4.01  --inst_solver_per_active                1400
% 27.48/4.01  --inst_solver_calls_frac                1.
% 27.48/4.01  --inst_passive_queue_type               priority_queues
% 27.48/4.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.48/4.01  --inst_passive_queues_freq              [25;2]
% 27.48/4.01  --inst_dismatching                      true
% 27.48/4.01  --inst_eager_unprocessed_to_passive     true
% 27.48/4.01  --inst_prop_sim_given                   true
% 27.48/4.01  --inst_prop_sim_new                     false
% 27.48/4.01  --inst_subs_new                         false
% 27.48/4.01  --inst_eq_res_simp                      false
% 27.48/4.01  --inst_subs_given                       false
% 27.48/4.01  --inst_orphan_elimination               true
% 27.48/4.01  --inst_learning_loop_flag               true
% 27.48/4.01  --inst_learning_start                   3000
% 27.48/4.01  --inst_learning_factor                  2
% 27.48/4.01  --inst_start_prop_sim_after_learn       3
% 27.48/4.01  --inst_sel_renew                        solver
% 27.48/4.01  --inst_lit_activity_flag                true
% 27.48/4.01  --inst_restr_to_given                   false
% 27.48/4.01  --inst_activity_threshold               500
% 27.48/4.01  --inst_out_proof                        true
% 27.48/4.01  
% 27.48/4.01  ------ Resolution Options
% 27.48/4.01  
% 27.48/4.01  --resolution_flag                       true
% 27.48/4.01  --res_lit_sel                           adaptive
% 27.48/4.01  --res_lit_sel_side                      none
% 27.48/4.01  --res_ordering                          kbo
% 27.48/4.01  --res_to_prop_solver                    active
% 27.48/4.01  --res_prop_simpl_new                    false
% 27.48/4.01  --res_prop_simpl_given                  true
% 27.48/4.01  --res_passive_queue_type                priority_queues
% 27.48/4.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.48/4.01  --res_passive_queues_freq               [15;5]
% 27.48/4.01  --res_forward_subs                      full
% 27.48/4.01  --res_backward_subs                     full
% 27.48/4.01  --res_forward_subs_resolution           true
% 27.48/4.01  --res_backward_subs_resolution          true
% 27.48/4.01  --res_orphan_elimination                true
% 27.48/4.01  --res_time_limit                        2.
% 27.48/4.01  --res_out_proof                         true
% 27.48/4.01  
% 27.48/4.01  ------ Superposition Options
% 27.48/4.01  
% 27.48/4.01  --superposition_flag                    true
% 27.48/4.01  --sup_passive_queue_type                priority_queues
% 27.48/4.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.48/4.01  --sup_passive_queues_freq               [1;4]
% 27.48/4.01  --demod_completeness_check              fast
% 27.48/4.01  --demod_use_ground                      true
% 27.48/4.01  --sup_to_prop_solver                    passive
% 27.48/4.01  --sup_prop_simpl_new                    true
% 27.48/4.01  --sup_prop_simpl_given                  true
% 27.48/4.01  --sup_fun_splitting                     false
% 27.48/4.01  --sup_smt_interval                      50000
% 27.48/4.01  
% 27.48/4.01  ------ Superposition Simplification Setup
% 27.48/4.01  
% 27.48/4.01  --sup_indices_passive                   []
% 27.48/4.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.48/4.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.48/4.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.48/4.01  --sup_full_triv                         [TrivRules;PropSubs]
% 27.48/4.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.48/4.01  --sup_full_bw                           [BwDemod]
% 27.48/4.01  --sup_immed_triv                        [TrivRules]
% 27.48/4.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.48/4.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.48/4.01  --sup_immed_bw_main                     []
% 27.48/4.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.48/4.01  --sup_input_triv                        [Unflattening;TrivRules]
% 27.48/4.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.48/4.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.48/4.01  
% 27.48/4.01  ------ Combination Options
% 27.48/4.01  
% 27.48/4.01  --comb_res_mult                         3
% 27.48/4.01  --comb_sup_mult                         2
% 27.48/4.01  --comb_inst_mult                        10
% 27.48/4.01  
% 27.48/4.01  ------ Debug Options
% 27.48/4.01  
% 27.48/4.01  --dbg_backtrace                         false
% 27.48/4.01  --dbg_dump_prop_clauses                 false
% 27.48/4.01  --dbg_dump_prop_clauses_file            -
% 27.48/4.01  --dbg_out_stat                          false
% 27.48/4.01  ------ Parsing...
% 27.48/4.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.48/4.01  
% 27.48/4.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 27.48/4.01  
% 27.48/4.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.48/4.01  
% 27.48/4.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.48/4.01  ------ Proving...
% 27.48/4.01  ------ Problem Properties 
% 27.48/4.01  
% 27.48/4.01  
% 27.48/4.01  clauses                                 10
% 27.48/4.01  conjectures                             2
% 27.48/4.01  EPR                                     3
% 27.48/4.01  Horn                                    10
% 27.48/4.01  unary                                   5
% 27.48/4.01  binary                                  4
% 27.48/4.01  lits                                    16
% 27.48/4.01  lits eq                                 4
% 27.48/4.01  fd_pure                                 0
% 27.48/4.01  fd_pseudo                               0
% 27.48/4.01  fd_cond                                 0
% 27.48/4.01  fd_pseudo_cond                          1
% 27.48/4.01  AC symbols                              0
% 27.48/4.01  
% 27.48/4.01  ------ Input Options Time Limit: Unbounded
% 27.48/4.01  
% 27.48/4.01  
% 27.48/4.01  ------ 
% 27.48/4.01  Current options:
% 27.48/4.01  ------ 
% 27.48/4.01  
% 27.48/4.01  ------ Input Options
% 27.48/4.01  
% 27.48/4.01  --out_options                           all
% 27.48/4.01  --tptp_safe_out                         true
% 27.48/4.01  --problem_path                          ""
% 27.48/4.01  --include_path                          ""
% 27.48/4.01  --clausifier                            res/vclausify_rel
% 27.48/4.01  --clausifier_options                    --mode clausify
% 27.48/4.01  --stdin                                 false
% 27.48/4.01  --stats_out                             sel
% 27.48/4.01  
% 27.48/4.01  ------ General Options
% 27.48/4.01  
% 27.48/4.01  --fof                                   false
% 27.48/4.01  --time_out_real                         604.99
% 27.48/4.01  --time_out_virtual                      -1.
% 27.48/4.01  --symbol_type_check                     false
% 27.48/4.01  --clausify_out                          false
% 27.48/4.01  --sig_cnt_out                           false
% 27.48/4.01  --trig_cnt_out                          false
% 27.48/4.01  --trig_cnt_out_tolerance                1.
% 27.48/4.01  --trig_cnt_out_sk_spl                   false
% 27.48/4.01  --abstr_cl_out                          false
% 27.48/4.01  
% 27.48/4.01  ------ Global Options
% 27.48/4.01  
% 27.48/4.01  --schedule                              none
% 27.48/4.01  --add_important_lit                     false
% 27.48/4.01  --prop_solver_per_cl                    1000
% 27.48/4.01  --min_unsat_core                        false
% 27.48/4.01  --soft_assumptions                      false
% 27.48/4.01  --soft_lemma_size                       3
% 27.48/4.01  --prop_impl_unit_size                   0
% 27.48/4.01  --prop_impl_unit                        []
% 27.48/4.01  --share_sel_clauses                     true
% 27.48/4.01  --reset_solvers                         false
% 27.48/4.01  --bc_imp_inh                            [conj_cone]
% 27.48/4.01  --conj_cone_tolerance                   3.
% 27.48/4.01  --extra_neg_conj                        none
% 27.48/4.01  --large_theory_mode                     true
% 27.48/4.01  --prolific_symb_bound                   200
% 27.48/4.01  --lt_threshold                          2000
% 27.48/4.01  --clause_weak_htbl                      true
% 27.48/4.01  --gc_record_bc_elim                     false
% 27.48/4.01  
% 27.48/4.01  ------ Preprocessing Options
% 27.48/4.01  
% 27.48/4.01  --preprocessing_flag                    true
% 27.48/4.01  --time_out_prep_mult                    0.1
% 27.48/4.01  --splitting_mode                        input
% 27.48/4.01  --splitting_grd                         true
% 27.48/4.01  --splitting_cvd                         false
% 27.48/4.01  --splitting_cvd_svl                     false
% 27.48/4.01  --splitting_nvd                         32
% 27.48/4.01  --sub_typing                            true
% 27.48/4.01  --prep_gs_sim                           false
% 27.48/4.01  --prep_unflatten                        true
% 27.48/4.01  --prep_res_sim                          true
% 27.48/4.01  --prep_upred                            true
% 27.48/4.01  --prep_sem_filter                       exhaustive
% 27.48/4.01  --prep_sem_filter_out                   false
% 27.48/4.01  --pred_elim                             false
% 27.48/4.01  --res_sim_input                         true
% 27.48/4.01  --eq_ax_congr_red                       true
% 27.48/4.01  --pure_diseq_elim                       true
% 27.48/4.01  --brand_transform                       false
% 27.48/4.01  --non_eq_to_eq                          false
% 27.48/4.01  --prep_def_merge                        true
% 27.48/4.01  --prep_def_merge_prop_impl              false
% 27.48/4.01  --prep_def_merge_mbd                    true
% 27.48/4.01  --prep_def_merge_tr_red                 false
% 27.48/4.01  --prep_def_merge_tr_cl                  false
% 27.48/4.01  --smt_preprocessing                     true
% 27.48/4.01  --smt_ac_axioms                         fast
% 27.48/4.01  --preprocessed_out                      false
% 27.48/4.01  --preprocessed_stats                    false
% 27.48/4.01  
% 27.48/4.01  ------ Abstraction refinement Options
% 27.48/4.01  
% 27.48/4.01  --abstr_ref                             []
% 27.48/4.01  --abstr_ref_prep                        false
% 27.48/4.01  --abstr_ref_until_sat                   false
% 27.48/4.01  --abstr_ref_sig_restrict                funpre
% 27.48/4.01  --abstr_ref_af_restrict_to_split_sk     false
% 27.48/4.01  --abstr_ref_under                       []
% 27.48/4.01  
% 27.48/4.01  ------ SAT Options
% 27.48/4.01  
% 27.48/4.01  --sat_mode                              false
% 27.48/4.01  --sat_fm_restart_options                ""
% 27.48/4.01  --sat_gr_def                            false
% 27.48/4.01  --sat_epr_types                         true
% 27.48/4.01  --sat_non_cyclic_types                  false
% 27.48/4.01  --sat_finite_models                     false
% 27.48/4.01  --sat_fm_lemmas                         false
% 27.48/4.01  --sat_fm_prep                           false
% 27.48/4.01  --sat_fm_uc_incr                        true
% 27.48/4.01  --sat_out_model                         small
% 27.48/4.01  --sat_out_clauses                       false
% 27.48/4.01  
% 27.48/4.01  ------ QBF Options
% 27.48/4.01  
% 27.48/4.01  --qbf_mode                              false
% 27.48/4.01  --qbf_elim_univ                         false
% 27.48/4.01  --qbf_dom_inst                          none
% 27.48/4.01  --qbf_dom_pre_inst                      false
% 27.48/4.01  --qbf_sk_in                             false
% 27.48/4.01  --qbf_pred_elim                         true
% 27.48/4.01  --qbf_split                             512
% 27.48/4.01  
% 27.48/4.01  ------ BMC1 Options
% 27.48/4.01  
% 27.48/4.01  --bmc1_incremental                      false
% 27.48/4.01  --bmc1_axioms                           reachable_all
% 27.48/4.01  --bmc1_min_bound                        0
% 27.48/4.01  --bmc1_max_bound                        -1
% 27.48/4.01  --bmc1_max_bound_default                -1
% 27.48/4.01  --bmc1_symbol_reachability              true
% 27.48/4.01  --bmc1_property_lemmas                  false
% 27.48/4.01  --bmc1_k_induction                      false
% 27.48/4.01  --bmc1_non_equiv_states                 false
% 27.48/4.01  --bmc1_deadlock                         false
% 27.48/4.01  --bmc1_ucm                              false
% 27.48/4.01  --bmc1_add_unsat_core                   none
% 27.48/4.01  --bmc1_unsat_core_children              false
% 27.48/4.01  --bmc1_unsat_core_extrapolate_axioms    false
% 27.48/4.01  --bmc1_out_stat                         full
% 27.48/4.01  --bmc1_ground_init                      false
% 27.48/4.01  --bmc1_pre_inst_next_state              false
% 27.48/4.01  --bmc1_pre_inst_state                   false
% 27.48/4.01  --bmc1_pre_inst_reach_state             false
% 27.48/4.01  --bmc1_out_unsat_core                   false
% 27.48/4.01  --bmc1_aig_witness_out                  false
% 27.48/4.01  --bmc1_verbose                          false
% 27.48/4.01  --bmc1_dump_clauses_tptp                false
% 27.48/4.01  --bmc1_dump_unsat_core_tptp             false
% 27.48/4.01  --bmc1_dump_file                        -
% 27.48/4.01  --bmc1_ucm_expand_uc_limit              128
% 27.48/4.01  --bmc1_ucm_n_expand_iterations          6
% 27.48/4.01  --bmc1_ucm_extend_mode                  1
% 27.48/4.01  --bmc1_ucm_init_mode                    2
% 27.48/4.01  --bmc1_ucm_cone_mode                    none
% 27.48/4.01  --bmc1_ucm_reduced_relation_type        0
% 27.48/4.01  --bmc1_ucm_relax_model                  4
% 27.48/4.01  --bmc1_ucm_full_tr_after_sat            true
% 27.48/4.01  --bmc1_ucm_expand_neg_assumptions       false
% 27.48/4.01  --bmc1_ucm_layered_model                none
% 27.48/4.01  --bmc1_ucm_max_lemma_size               10
% 27.48/4.01  
% 27.48/4.01  ------ AIG Options
% 27.48/4.01  
% 27.48/4.01  --aig_mode                              false
% 27.48/4.01  
% 27.48/4.01  ------ Instantiation Options
% 27.48/4.01  
% 27.48/4.01  --instantiation_flag                    true
% 27.48/4.01  --inst_sos_flag                         false
% 27.48/4.01  --inst_sos_phase                        true
% 27.48/4.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.48/4.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.48/4.01  --inst_lit_sel_side                     num_symb
% 27.48/4.01  --inst_solver_per_active                1400
% 27.48/4.01  --inst_solver_calls_frac                1.
% 27.48/4.01  --inst_passive_queue_type               priority_queues
% 27.48/4.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.48/4.01  --inst_passive_queues_freq              [25;2]
% 27.48/4.01  --inst_dismatching                      true
% 27.48/4.01  --inst_eager_unprocessed_to_passive     true
% 27.48/4.01  --inst_prop_sim_given                   true
% 27.48/4.01  --inst_prop_sim_new                     false
% 27.48/4.01  --inst_subs_new                         false
% 27.48/4.01  --inst_eq_res_simp                      false
% 27.48/4.01  --inst_subs_given                       false
% 27.48/4.01  --inst_orphan_elimination               true
% 27.48/4.01  --inst_learning_loop_flag               true
% 27.48/4.01  --inst_learning_start                   3000
% 27.48/4.01  --inst_learning_factor                  2
% 27.48/4.01  --inst_start_prop_sim_after_learn       3
% 27.48/4.01  --inst_sel_renew                        solver
% 27.48/4.01  --inst_lit_activity_flag                true
% 27.48/4.01  --inst_restr_to_given                   false
% 27.48/4.01  --inst_activity_threshold               500
% 27.48/4.01  --inst_out_proof                        true
% 27.48/4.01  
% 27.48/4.01  ------ Resolution Options
% 27.48/4.01  
% 27.48/4.01  --resolution_flag                       true
% 27.48/4.01  --res_lit_sel                           adaptive
% 27.48/4.01  --res_lit_sel_side                      none
% 27.48/4.01  --res_ordering                          kbo
% 27.48/4.01  --res_to_prop_solver                    active
% 27.48/4.01  --res_prop_simpl_new                    false
% 27.48/4.01  --res_prop_simpl_given                  true
% 27.48/4.01  --res_passive_queue_type                priority_queues
% 27.48/4.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.48/4.01  --res_passive_queues_freq               [15;5]
% 27.48/4.01  --res_forward_subs                      full
% 27.48/4.01  --res_backward_subs                     full
% 27.48/4.01  --res_forward_subs_resolution           true
% 27.48/4.01  --res_backward_subs_resolution          true
% 27.48/4.01  --res_orphan_elimination                true
% 27.48/4.01  --res_time_limit                        2.
% 27.48/4.01  --res_out_proof                         true
% 27.48/4.01  
% 27.48/4.01  ------ Superposition Options
% 27.48/4.01  
% 27.48/4.01  --superposition_flag                    true
% 27.48/4.01  --sup_passive_queue_type                priority_queues
% 27.48/4.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.48/4.01  --sup_passive_queues_freq               [1;4]
% 27.48/4.01  --demod_completeness_check              fast
% 27.48/4.01  --demod_use_ground                      true
% 27.48/4.01  --sup_to_prop_solver                    passive
% 27.48/4.01  --sup_prop_simpl_new                    true
% 27.48/4.01  --sup_prop_simpl_given                  true
% 27.48/4.01  --sup_fun_splitting                     false
% 27.48/4.01  --sup_smt_interval                      50000
% 27.48/4.01  
% 27.48/4.01  ------ Superposition Simplification Setup
% 27.48/4.01  
% 27.48/4.01  --sup_indices_passive                   []
% 27.48/4.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.48/4.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.48/4.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.48/4.01  --sup_full_triv                         [TrivRules;PropSubs]
% 27.48/4.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.48/4.01  --sup_full_bw                           [BwDemod]
% 27.48/4.01  --sup_immed_triv                        [TrivRules]
% 27.48/4.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.48/4.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.48/4.01  --sup_immed_bw_main                     []
% 27.48/4.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.48/4.01  --sup_input_triv                        [Unflattening;TrivRules]
% 27.48/4.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.48/4.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.48/4.01  
% 27.48/4.01  ------ Combination Options
% 27.48/4.01  
% 27.48/4.01  --comb_res_mult                         3
% 27.48/4.01  --comb_sup_mult                         2
% 27.48/4.01  --comb_inst_mult                        10
% 27.48/4.01  
% 27.48/4.01  ------ Debug Options
% 27.48/4.01  
% 27.48/4.01  --dbg_backtrace                         false
% 27.48/4.01  --dbg_dump_prop_clauses                 false
% 27.48/4.01  --dbg_dump_prop_clauses_file            -
% 27.48/4.01  --dbg_out_stat                          false
% 27.48/4.01  
% 27.48/4.01  
% 27.48/4.01  
% 27.48/4.01  
% 27.48/4.01  ------ Proving...
% 27.48/4.01  
% 27.48/4.01  
% 27.48/4.01  % SZS status Theorem for theBenchmark.p
% 27.48/4.01  
% 27.48/4.01   Resolution empty clause
% 27.48/4.01  
% 27.48/4.01  % SZS output start CNFRefutation for theBenchmark.p
% 27.48/4.01  
% 27.48/4.01  fof(f1,axiom,(
% 27.48/4.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.48/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.48/4.01  
% 27.48/4.01  fof(f18,plain,(
% 27.48/4.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.48/4.01    inference(nnf_transformation,[],[f1])).
% 27.48/4.01  
% 27.48/4.01  fof(f19,plain,(
% 27.48/4.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.48/4.01    inference(flattening,[],[f18])).
% 27.48/4.01  
% 27.48/4.01  fof(f23,plain,(
% 27.48/4.01    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 27.48/4.01    inference(cnf_transformation,[],[f19])).
% 27.48/4.01  
% 27.48/4.01  fof(f41,plain,(
% 27.48/4.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 27.48/4.01    inference(equality_resolution,[],[f23])).
% 27.48/4.01  
% 27.48/4.01  fof(f5,axiom,(
% 27.48/4.01    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 27.48/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.48/4.01  
% 27.48/4.01  fof(f15,plain,(
% 27.48/4.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 27.48/4.01    inference(ennf_transformation,[],[f5])).
% 27.48/4.01  
% 27.48/4.01  fof(f28,plain,(
% 27.48/4.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 27.48/4.01    inference(cnf_transformation,[],[f15])).
% 27.48/4.01  
% 27.48/4.01  fof(f2,axiom,(
% 27.48/4.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 27.48/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.48/4.01  
% 27.48/4.01  fof(f25,plain,(
% 27.48/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 27.48/4.01    inference(cnf_transformation,[],[f2])).
% 27.48/4.01  
% 27.48/4.01  fof(f9,axiom,(
% 27.48/4.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 27.48/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.48/4.01  
% 27.48/4.01  fof(f32,plain,(
% 27.48/4.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 27.48/4.01    inference(cnf_transformation,[],[f9])).
% 27.48/4.01  
% 27.48/4.01  fof(f7,axiom,(
% 27.48/4.01    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 27.48/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.48/4.01  
% 27.48/4.01  fof(f30,plain,(
% 27.48/4.01    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 27.48/4.01    inference(cnf_transformation,[],[f7])).
% 27.48/4.01  
% 27.48/4.01  fof(f36,plain,(
% 27.48/4.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 27.48/4.01    inference(definition_unfolding,[],[f32,f30])).
% 27.48/4.01  
% 27.48/4.01  fof(f37,plain,(
% 27.48/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 27.48/4.01    inference(definition_unfolding,[],[f25,f36])).
% 27.48/4.01  
% 27.48/4.01  fof(f39,plain,(
% 27.48/4.01    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))),X2)) )),
% 27.48/4.01    inference(definition_unfolding,[],[f28,f37])).
% 27.48/4.01  
% 27.48/4.01  fof(f8,axiom,(
% 27.48/4.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 27.48/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.48/4.01  
% 27.48/4.01  fof(f31,plain,(
% 27.48/4.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 27.48/4.01    inference(cnf_transformation,[],[f8])).
% 27.48/4.01  
% 27.48/4.01  fof(f40,plain,(
% 27.48/4.01    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_subset_1(X0,X1)) )),
% 27.48/4.01    inference(definition_unfolding,[],[f31,f37])).
% 27.48/4.01  
% 27.48/4.01  fof(f3,axiom,(
% 27.48/4.01    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 27.48/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.48/4.01  
% 27.48/4.01  fof(f13,plain,(
% 27.48/4.01    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 27.48/4.01    inference(ennf_transformation,[],[f3])).
% 27.48/4.01  
% 27.48/4.01  fof(f26,plain,(
% 27.48/4.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 27.48/4.01    inference(cnf_transformation,[],[f13])).
% 27.48/4.01  
% 27.48/4.01  fof(f11,conjecture,(
% 27.48/4.01    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))))),
% 27.48/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.48/4.01  
% 27.48/4.01  fof(f12,negated_conjecture,(
% 27.48/4.01    ~! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))))),
% 27.48/4.01    inference(negated_conjecture,[],[f11])).
% 27.48/4.01  
% 27.48/4.01  fof(f17,plain,(
% 27.48/4.01    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2))),
% 27.48/4.01    inference(ennf_transformation,[],[f12])).
% 27.48/4.01  
% 27.48/4.01  fof(f20,plain,(
% 27.48/4.01    ? [X0,X1,X2] : (~r1_tarski(k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)),k10_relat_1(X2,k6_subset_1(X0,X1))) & v1_relat_1(X2)) => (~r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) & v1_relat_1(sK2))),
% 27.48/4.01    introduced(choice_axiom,[])).
% 27.48/4.01  
% 27.48/4.01  fof(f21,plain,(
% 27.48/4.01    ~r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) & v1_relat_1(sK2)),
% 27.48/4.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f20])).
% 27.48/4.01  
% 27.48/4.01  fof(f34,plain,(
% 27.48/4.01    v1_relat_1(sK2)),
% 27.48/4.01    inference(cnf_transformation,[],[f21])).
% 27.48/4.01  
% 27.48/4.01  fof(f10,axiom,(
% 27.48/4.01    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)))),
% 27.48/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.48/4.01  
% 27.48/4.01  fof(f16,plain,(
% 27.48/4.01    ! [X0,X1,X2] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 27.48/4.01    inference(ennf_transformation,[],[f10])).
% 27.48/4.01  
% 27.48/4.01  fof(f33,plain,(
% 27.48/4.01    ( ! [X2,X0,X1] : (k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k2_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 27.48/4.01    inference(cnf_transformation,[],[f16])).
% 27.48/4.01  
% 27.48/4.01  fof(f6,axiom,(
% 27.48/4.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 27.48/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.48/4.01  
% 27.48/4.01  fof(f29,plain,(
% 27.48/4.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 27.48/4.01    inference(cnf_transformation,[],[f6])).
% 27.48/4.01  
% 27.48/4.01  fof(f4,axiom,(
% 27.48/4.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 27.48/4.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.48/4.01  
% 27.48/4.01  fof(f14,plain,(
% 27.48/4.01    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 27.48/4.01    inference(ennf_transformation,[],[f4])).
% 27.48/4.01  
% 27.48/4.01  fof(f27,plain,(
% 27.48/4.01    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 27.48/4.01    inference(cnf_transformation,[],[f14])).
% 27.48/4.01  
% 27.48/4.01  fof(f38,plain,(
% 27.48/4.01    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 27.48/4.01    inference(definition_unfolding,[],[f27,f37])).
% 27.48/4.01  
% 27.48/4.01  fof(f35,plain,(
% 27.48/4.01    ~r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1)))),
% 27.48/4.01    inference(cnf_transformation,[],[f21])).
% 27.48/4.01  
% 27.48/4.01  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f41]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_435,plain,
% 27.48/4.01      ( r1_tarski(X0,X0) = iProver_top ),
% 27.48/4.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_5,plain,
% 27.48/4.01      ( r1_tarski(X0,k2_xboole_0(X1,X2))
% 27.48/4.01      | ~ r1_tarski(k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))),X2) ),
% 27.48/4.01      inference(cnf_transformation,[],[f39]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_432,plain,
% 27.48/4.01      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 27.48/4.01      | r1_tarski(k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))),X2) != iProver_top ),
% 27.48/4.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_7,plain,
% 27.48/4.01      ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) = k6_subset_1(X0,X1) ),
% 27.48/4.01      inference(cnf_transformation,[],[f40]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_461,plain,
% 27.48/4.01      ( r1_tarski(X0,k2_xboole_0(X1,X2)) = iProver_top
% 27.48/4.01      | r1_tarski(k6_subset_1(X0,X1),X2) != iProver_top ),
% 27.48/4.01      inference(light_normalisation,[status(thm)],[c_432,c_7]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_846,plain,
% 27.48/4.01      ( r1_tarski(X0,k2_xboole_0(X1,k6_subset_1(X0,X1))) = iProver_top ),
% 27.48/4.01      inference(superposition,[status(thm)],[c_435,c_461]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_3,plain,
% 27.48/4.01      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 27.48/4.01      inference(cnf_transformation,[],[f26]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_434,plain,
% 27.48/4.01      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 27.48/4.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_1120,plain,
% 27.48/4.01      ( k2_xboole_0(X0,k2_xboole_0(X1,k6_subset_1(X0,X1))) = k2_xboole_0(X1,k6_subset_1(X0,X1)) ),
% 27.48/4.01      inference(superposition,[status(thm)],[c_846,c_434]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_10,negated_conjecture,
% 27.48/4.01      ( v1_relat_1(sK2) ),
% 27.48/4.01      inference(cnf_transformation,[],[f34]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_428,plain,
% 27.48/4.01      ( v1_relat_1(sK2) = iProver_top ),
% 27.48/4.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_8,plain,
% 27.48/4.01      ( ~ v1_relat_1(X0)
% 27.48/4.01      | k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2)) ),
% 27.48/4.01      inference(cnf_transformation,[],[f33]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_430,plain,
% 27.48/4.01      ( k2_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) = k10_relat_1(X0,k2_xboole_0(X1,X2))
% 27.48/4.01      | v1_relat_1(X0) != iProver_top ),
% 27.48/4.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_1040,plain,
% 27.48/4.01      ( k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) = k10_relat_1(sK2,k2_xboole_0(X0,X1)) ),
% 27.48/4.01      inference(superposition,[status(thm)],[c_428,c_430]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_6,plain,
% 27.48/4.01      ( r1_tarski(X0,k2_xboole_0(X0,X1)) ),
% 27.48/4.01      inference(cnf_transformation,[],[f29]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_431,plain,
% 27.48/4.01      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 27.48/4.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_2541,plain,
% 27.48/4.01      ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X0,X1))) = iProver_top ),
% 27.48/4.01      inference(superposition,[status(thm)],[c_1040,c_431]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_2926,plain,
% 27.48/4.01      ( r1_tarski(k10_relat_1(sK2,X0),k10_relat_1(sK2,k2_xboole_0(X1,k6_subset_1(X0,X1)))) = iProver_top ),
% 27.48/4.01      inference(superposition,[status(thm)],[c_1120,c_2541]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_4,plain,
% 27.48/4.01      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
% 27.48/4.01      | r1_tarski(k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))),X2) ),
% 27.48/4.01      inference(cnf_transformation,[],[f38]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_433,plain,
% 27.48/4.01      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 27.48/4.01      | r1_tarski(k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))),X2) = iProver_top ),
% 27.48/4.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_466,plain,
% 27.48/4.01      ( r1_tarski(X0,k2_xboole_0(X1,X2)) != iProver_top
% 27.48/4.01      | r1_tarski(k6_subset_1(X0,X1),X2) = iProver_top ),
% 27.48/4.01      inference(light_normalisation,[status(thm)],[c_433,c_7]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_2542,plain,
% 27.48/4.01      ( r1_tarski(X0,k10_relat_1(sK2,k2_xboole_0(X1,X2))) != iProver_top
% 27.48/4.01      | r1_tarski(k6_subset_1(X0,k10_relat_1(sK2,X1)),k10_relat_1(sK2,X2)) = iProver_top ),
% 27.48/4.01      inference(superposition,[status(thm)],[c_1040,c_466]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_9,negated_conjecture,
% 27.48/4.01      ( ~ r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) ),
% 27.48/4.01      inference(cnf_transformation,[],[f35]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_429,plain,
% 27.48/4.01      ( r1_tarski(k6_subset_1(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)),k10_relat_1(sK2,k6_subset_1(sK0,sK1))) != iProver_top ),
% 27.48/4.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_45915,plain,
% 27.48/4.01      ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,k2_xboole_0(sK1,k6_subset_1(sK0,sK1)))) != iProver_top ),
% 27.48/4.01      inference(superposition,[status(thm)],[c_2542,c_429]) ).
% 27.48/4.01  
% 27.48/4.01  cnf(c_81433,plain,
% 27.48/4.01      ( $false ),
% 27.48/4.01      inference(superposition,[status(thm)],[c_2926,c_45915]) ).
% 27.48/4.01  
% 27.48/4.01  
% 27.48/4.01  % SZS output end CNFRefutation for theBenchmark.p
% 27.48/4.01  
% 27.48/4.01  ------                               Statistics
% 27.48/4.01  
% 27.48/4.01  ------ Selected
% 27.48/4.01  
% 27.48/4.01  total_time:                             3.329
% 27.48/4.01  
%------------------------------------------------------------------------------
