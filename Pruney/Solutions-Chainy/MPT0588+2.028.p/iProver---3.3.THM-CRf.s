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
% DateTime   : Thu Dec  3 11:48:07 EST 2020

% Result     : Theorem 1.19s
% Output     : CNFRefutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 133 expanded)
%              Number of clauses        :   29 (  41 expanded)
%              Number of leaves         :   14 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :   91 ( 192 expanded)
%              Number of equality atoms :   66 ( 132 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X2))) ),
    inference(definition_unfolding,[],[f29,f36,f30])).

fof(f50,plain,(
    ! [X2,X0,X1] : k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X2))) = k3_tarski(k2_tarski(k2_tarski(X1,X1),k2_tarski(X2,X0))) ),
    inference(definition_unfolding,[],[f26,f47,f47])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f31,f47])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) ),
    inference(definition_unfolding,[],[f28,f36,f30,f30])).

fof(f14,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f13,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f42,f37])).

fof(f16,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).

fof(f43,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0))) ),
    inference(definition_unfolding,[],[f44,f37])).

cnf(c_2,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X2))) = k3_tarski(k2_tarski(k2_tarski(X2,X2),k2_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_4,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_418,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X1,X0) ),
    inference(superposition,[status(thm)],[c_2,c_4])).

cnf(c_0,plain,
    ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_887,plain,
    ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(superposition,[status(thm)],[c_418,c_0])).

cnf(c_6,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_161,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_159,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_280,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[status(thm)],[c_161,c_159])).

cnf(c_9,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_285,plain,
    ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_280,c_9])).

cnf(c_12,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_158,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k7_relat_1(X1,k1_relat_1(k7_relat_1(X0,k1_relat_1(X1)))) = k7_relat_1(X1,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_160,plain,
    ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_338,plain,
    ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(X0,k1_relat_1(sK1)))) = k7_relat_1(sK1,k1_relat_1(X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_158,c_160])).

cnf(c_572,plain,
    ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)))) = k7_relat_1(sK1,k1_relat_1(k6_relat_1(X0))) ),
    inference(superposition,[status(thm)],[c_161,c_338])).

cnf(c_577,plain,
    ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)))) = k7_relat_1(sK1,X0) ),
    inference(light_normalisation,[status(thm)],[c_572,c_9])).

cnf(c_735,plain,
    ( k7_relat_1(sK1,k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))) = k7_relat_1(sK1,X0) ),
    inference(demodulation,[status(thm)],[c_285,c_577])).

cnf(c_917,plain,
    ( k7_relat_1(sK1,k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) = k7_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_887,c_735])).

cnf(c_281,plain,
    ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_158,c_159])).

cnf(c_919,plain,
    ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
    inference(light_normalisation,[status(thm)],[c_917,c_281])).

cnf(c_11,negated_conjecture,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_525,plain,
    ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK0))) != k7_relat_1(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_281,c_11])).

cnf(c_1105,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
    inference(demodulation,[status(thm)],[c_919,c_525])).

cnf(c_69,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_214,plain,
    ( k7_relat_1(sK1,sK0) = k7_relat_1(sK1,sK0) ),
    inference(instantiation,[status(thm)],[c_69])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1105,c_214])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n013.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 16:08:39 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 1.19/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.19/0.94  
% 1.19/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.19/0.94  
% 1.19/0.94  ------  iProver source info
% 1.19/0.94  
% 1.19/0.94  git: date: 2020-06-30 10:37:57 +0100
% 1.19/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.19/0.94  git: non_committed_changes: false
% 1.19/0.94  git: last_make_outside_of_git: false
% 1.19/0.94  
% 1.19/0.94  ------ 
% 1.19/0.94  
% 1.19/0.94  ------ Input Options
% 1.19/0.94  
% 1.19/0.94  --out_options                           all
% 1.19/0.94  --tptp_safe_out                         true
% 1.19/0.94  --problem_path                          ""
% 1.19/0.94  --include_path                          ""
% 1.19/0.94  --clausifier                            res/vclausify_rel
% 1.19/0.94  --clausifier_options                    --mode clausify
% 1.19/0.94  --stdin                                 false
% 1.19/0.94  --stats_out                             all
% 1.19/0.94  
% 1.19/0.94  ------ General Options
% 1.19/0.94  
% 1.19/0.94  --fof                                   false
% 1.19/0.94  --time_out_real                         305.
% 1.19/0.94  --time_out_virtual                      -1.
% 1.19/0.94  --symbol_type_check                     false
% 1.19/0.94  --clausify_out                          false
% 1.19/0.94  --sig_cnt_out                           false
% 1.19/0.94  --trig_cnt_out                          false
% 1.19/0.94  --trig_cnt_out_tolerance                1.
% 1.19/0.94  --trig_cnt_out_sk_spl                   false
% 1.19/0.94  --abstr_cl_out                          false
% 1.19/0.94  
% 1.19/0.94  ------ Global Options
% 1.19/0.94  
% 1.19/0.94  --schedule                              default
% 1.19/0.94  --add_important_lit                     false
% 1.19/0.94  --prop_solver_per_cl                    1000
% 1.19/0.94  --min_unsat_core                        false
% 1.19/0.94  --soft_assumptions                      false
% 1.19/0.94  --soft_lemma_size                       3
% 1.19/0.94  --prop_impl_unit_size                   0
% 1.19/0.94  --prop_impl_unit                        []
% 1.19/0.94  --share_sel_clauses                     true
% 1.19/0.94  --reset_solvers                         false
% 1.19/0.94  --bc_imp_inh                            [conj_cone]
% 1.19/0.94  --conj_cone_tolerance                   3.
% 1.19/0.94  --extra_neg_conj                        none
% 1.19/0.94  --large_theory_mode                     true
% 1.19/0.94  --prolific_symb_bound                   200
% 1.19/0.94  --lt_threshold                          2000
% 1.19/0.94  --clause_weak_htbl                      true
% 1.19/0.94  --gc_record_bc_elim                     false
% 1.19/0.94  
% 1.19/0.94  ------ Preprocessing Options
% 1.19/0.94  
% 1.19/0.94  --preprocessing_flag                    true
% 1.19/0.94  --time_out_prep_mult                    0.1
% 1.19/0.94  --splitting_mode                        input
% 1.19/0.94  --splitting_grd                         true
% 1.19/0.94  --splitting_cvd                         false
% 1.19/0.94  --splitting_cvd_svl                     false
% 1.19/0.94  --splitting_nvd                         32
% 1.19/0.94  --sub_typing                            true
% 1.19/0.94  --prep_gs_sim                           true
% 1.19/0.94  --prep_unflatten                        true
% 1.19/0.94  --prep_res_sim                          true
% 1.19/0.94  --prep_upred                            true
% 1.19/0.94  --prep_sem_filter                       exhaustive
% 1.19/0.94  --prep_sem_filter_out                   false
% 1.19/0.94  --pred_elim                             true
% 1.19/0.94  --res_sim_input                         true
% 1.19/0.94  --eq_ax_congr_red                       true
% 1.19/0.94  --pure_diseq_elim                       true
% 1.19/0.94  --brand_transform                       false
% 1.19/0.94  --non_eq_to_eq                          false
% 1.19/0.94  --prep_def_merge                        true
% 1.19/0.94  --prep_def_merge_prop_impl              false
% 1.19/0.94  --prep_def_merge_mbd                    true
% 1.19/0.94  --prep_def_merge_tr_red                 false
% 1.19/0.94  --prep_def_merge_tr_cl                  false
% 1.19/0.94  --smt_preprocessing                     true
% 1.19/0.94  --smt_ac_axioms                         fast
% 1.19/0.94  --preprocessed_out                      false
% 1.19/0.94  --preprocessed_stats                    false
% 1.19/0.94  
% 1.19/0.94  ------ Abstraction refinement Options
% 1.19/0.94  
% 1.19/0.94  --abstr_ref                             []
% 1.19/0.94  --abstr_ref_prep                        false
% 1.19/0.94  --abstr_ref_until_sat                   false
% 1.19/0.94  --abstr_ref_sig_restrict                funpre
% 1.19/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 1.19/0.94  --abstr_ref_under                       []
% 1.19/0.94  
% 1.19/0.94  ------ SAT Options
% 1.19/0.94  
% 1.19/0.94  --sat_mode                              false
% 1.19/0.94  --sat_fm_restart_options                ""
% 1.19/0.94  --sat_gr_def                            false
% 1.19/0.94  --sat_epr_types                         true
% 1.19/0.94  --sat_non_cyclic_types                  false
% 1.19/0.94  --sat_finite_models                     false
% 1.19/0.94  --sat_fm_lemmas                         false
% 1.19/0.94  --sat_fm_prep                           false
% 1.19/0.94  --sat_fm_uc_incr                        true
% 1.19/0.94  --sat_out_model                         small
% 1.19/0.94  --sat_out_clauses                       false
% 1.19/0.94  
% 1.19/0.94  ------ QBF Options
% 1.19/0.94  
% 1.19/0.94  --qbf_mode                              false
% 1.19/0.94  --qbf_elim_univ                         false
% 1.19/0.94  --qbf_dom_inst                          none
% 1.19/0.94  --qbf_dom_pre_inst                      false
% 1.19/0.94  --qbf_sk_in                             false
% 1.19/0.94  --qbf_pred_elim                         true
% 1.19/0.94  --qbf_split                             512
% 1.19/0.94  
% 1.19/0.94  ------ BMC1 Options
% 1.19/0.94  
% 1.19/0.94  --bmc1_incremental                      false
% 1.19/0.94  --bmc1_axioms                           reachable_all
% 1.19/0.94  --bmc1_min_bound                        0
% 1.19/0.94  --bmc1_max_bound                        -1
% 1.19/0.94  --bmc1_max_bound_default                -1
% 1.19/0.94  --bmc1_symbol_reachability              true
% 1.19/0.94  --bmc1_property_lemmas                  false
% 1.19/0.94  --bmc1_k_induction                      false
% 1.19/0.94  --bmc1_non_equiv_states                 false
% 1.19/0.94  --bmc1_deadlock                         false
% 1.19/0.94  --bmc1_ucm                              false
% 1.19/0.94  --bmc1_add_unsat_core                   none
% 1.19/0.94  --bmc1_unsat_core_children              false
% 1.19/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 1.19/0.94  --bmc1_out_stat                         full
% 1.19/0.94  --bmc1_ground_init                      false
% 1.19/0.94  --bmc1_pre_inst_next_state              false
% 1.19/0.94  --bmc1_pre_inst_state                   false
% 1.19/0.94  --bmc1_pre_inst_reach_state             false
% 1.19/0.94  --bmc1_out_unsat_core                   false
% 1.19/0.94  --bmc1_aig_witness_out                  false
% 1.19/0.94  --bmc1_verbose                          false
% 1.19/0.94  --bmc1_dump_clauses_tptp                false
% 1.19/0.94  --bmc1_dump_unsat_core_tptp             false
% 1.19/0.94  --bmc1_dump_file                        -
% 1.19/0.94  --bmc1_ucm_expand_uc_limit              128
% 1.19/0.94  --bmc1_ucm_n_expand_iterations          6
% 1.19/0.94  --bmc1_ucm_extend_mode                  1
% 1.19/0.94  --bmc1_ucm_init_mode                    2
% 1.19/0.94  --bmc1_ucm_cone_mode                    none
% 1.19/0.94  --bmc1_ucm_reduced_relation_type        0
% 1.19/0.94  --bmc1_ucm_relax_model                  4
% 1.19/0.94  --bmc1_ucm_full_tr_after_sat            true
% 1.19/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 1.19/0.94  --bmc1_ucm_layered_model                none
% 1.19/0.94  --bmc1_ucm_max_lemma_size               10
% 1.19/0.94  
% 1.19/0.94  ------ AIG Options
% 1.19/0.94  
% 1.19/0.94  --aig_mode                              false
% 1.19/0.94  
% 1.19/0.94  ------ Instantiation Options
% 1.19/0.94  
% 1.19/0.94  --instantiation_flag                    true
% 1.19/0.94  --inst_sos_flag                         false
% 1.19/0.94  --inst_sos_phase                        true
% 1.19/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.19/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.19/0.94  --inst_lit_sel_side                     num_symb
% 1.19/0.94  --inst_solver_per_active                1400
% 1.19/0.94  --inst_solver_calls_frac                1.
% 1.19/0.94  --inst_passive_queue_type               priority_queues
% 1.19/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.19/0.94  --inst_passive_queues_freq              [25;2]
% 1.19/0.94  --inst_dismatching                      true
% 1.19/0.94  --inst_eager_unprocessed_to_passive     true
% 1.19/0.94  --inst_prop_sim_given                   true
% 1.19/0.94  --inst_prop_sim_new                     false
% 1.19/0.94  --inst_subs_new                         false
% 1.19/0.94  --inst_eq_res_simp                      false
% 1.19/0.94  --inst_subs_given                       false
% 1.19/0.94  --inst_orphan_elimination               true
% 1.19/0.94  --inst_learning_loop_flag               true
% 1.19/0.94  --inst_learning_start                   3000
% 1.19/0.94  --inst_learning_factor                  2
% 1.19/0.94  --inst_start_prop_sim_after_learn       3
% 1.19/0.94  --inst_sel_renew                        solver
% 1.19/0.94  --inst_lit_activity_flag                true
% 1.19/0.94  --inst_restr_to_given                   false
% 1.19/0.94  --inst_activity_threshold               500
% 1.19/0.94  --inst_out_proof                        true
% 1.19/0.94  
% 1.19/0.94  ------ Resolution Options
% 1.19/0.94  
% 1.19/0.94  --resolution_flag                       true
% 1.19/0.94  --res_lit_sel                           adaptive
% 1.19/0.94  --res_lit_sel_side                      none
% 1.19/0.94  --res_ordering                          kbo
% 1.19/0.94  --res_to_prop_solver                    active
% 1.19/0.94  --res_prop_simpl_new                    false
% 1.19/0.94  --res_prop_simpl_given                  true
% 1.19/0.94  --res_passive_queue_type                priority_queues
% 1.19/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.19/0.94  --res_passive_queues_freq               [15;5]
% 1.19/0.94  --res_forward_subs                      full
% 1.19/0.94  --res_backward_subs                     full
% 1.19/0.94  --res_forward_subs_resolution           true
% 1.19/0.94  --res_backward_subs_resolution          true
% 1.19/0.94  --res_orphan_elimination                true
% 1.19/0.94  --res_time_limit                        2.
% 1.19/0.94  --res_out_proof                         true
% 1.19/0.94  
% 1.19/0.94  ------ Superposition Options
% 1.19/0.94  
% 1.19/0.94  --superposition_flag                    true
% 1.19/0.94  --sup_passive_queue_type                priority_queues
% 1.19/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.19/0.94  --sup_passive_queues_freq               [8;1;4]
% 1.19/0.94  --demod_completeness_check              fast
% 1.19/0.94  --demod_use_ground                      true
% 1.19/0.94  --sup_to_prop_solver                    passive
% 1.19/0.94  --sup_prop_simpl_new                    true
% 1.19/0.94  --sup_prop_simpl_given                  true
% 1.19/0.94  --sup_fun_splitting                     false
% 1.19/0.94  --sup_smt_interval                      50000
% 1.19/0.95  
% 1.19/0.95  ------ Superposition Simplification Setup
% 1.19/0.95  
% 1.19/0.95  --sup_indices_passive                   []
% 1.19/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.19/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.19/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.19/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 1.19/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.19/0.95  --sup_full_bw                           [BwDemod]
% 1.19/0.95  --sup_immed_triv                        [TrivRules]
% 1.19/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.19/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.19/0.95  --sup_immed_bw_main                     []
% 1.19/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.19/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 1.19/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.19/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.19/0.95  
% 1.19/0.95  ------ Combination Options
% 1.19/0.95  
% 1.19/0.95  --comb_res_mult                         3
% 1.19/0.95  --comb_sup_mult                         2
% 1.19/0.95  --comb_inst_mult                        10
% 1.19/0.95  
% 1.19/0.95  ------ Debug Options
% 1.19/0.95  
% 1.19/0.95  --dbg_backtrace                         false
% 1.19/0.95  --dbg_dump_prop_clauses                 false
% 1.19/0.95  --dbg_dump_prop_clauses_file            -
% 1.19/0.95  --dbg_out_stat                          false
% 1.19/0.95  ------ Parsing...
% 1.19/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.19/0.95  
% 1.19/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.19/0.95  
% 1.19/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.19/0.95  
% 1.19/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.19/0.95  ------ Proving...
% 1.19/0.95  ------ Problem Properties 
% 1.19/0.95  
% 1.19/0.95  
% 1.19/0.95  clauses                                 13
% 1.19/0.95  conjectures                             2
% 1.19/0.95  EPR                                     1
% 1.19/0.95  Horn                                    13
% 1.19/0.95  unary                                   11
% 1.19/0.95  binary                                  1
% 1.19/0.95  lits                                    16
% 1.19/0.95  lits eq                                 11
% 1.19/0.95  fd_pure                                 0
% 1.19/0.95  fd_pseudo                               0
% 1.19/0.95  fd_cond                                 0
% 1.19/0.95  fd_pseudo_cond                          0
% 1.19/0.95  AC symbols                              0
% 1.19/0.95  
% 1.19/0.95  ------ Schedule dynamic 5 is on 
% 1.19/0.95  
% 1.19/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.19/0.95  
% 1.19/0.95  
% 1.19/0.95  ------ 
% 1.19/0.95  Current options:
% 1.19/0.95  ------ 
% 1.19/0.95  
% 1.19/0.95  ------ Input Options
% 1.19/0.95  
% 1.19/0.95  --out_options                           all
% 1.19/0.95  --tptp_safe_out                         true
% 1.19/0.95  --problem_path                          ""
% 1.19/0.95  --include_path                          ""
% 1.19/0.95  --clausifier                            res/vclausify_rel
% 1.19/0.95  --clausifier_options                    --mode clausify
% 1.19/0.95  --stdin                                 false
% 1.19/0.95  --stats_out                             all
% 1.19/0.95  
% 1.19/0.95  ------ General Options
% 1.19/0.95  
% 1.19/0.95  --fof                                   false
% 1.19/0.95  --time_out_real                         305.
% 1.19/0.95  --time_out_virtual                      -1.
% 1.19/0.95  --symbol_type_check                     false
% 1.19/0.95  --clausify_out                          false
% 1.19/0.95  --sig_cnt_out                           false
% 1.19/0.95  --trig_cnt_out                          false
% 1.19/0.95  --trig_cnt_out_tolerance                1.
% 1.19/0.95  --trig_cnt_out_sk_spl                   false
% 1.19/0.95  --abstr_cl_out                          false
% 1.19/0.95  
% 1.19/0.95  ------ Global Options
% 1.19/0.95  
% 1.19/0.95  --schedule                              default
% 1.19/0.95  --add_important_lit                     false
% 1.19/0.95  --prop_solver_per_cl                    1000
% 1.19/0.95  --min_unsat_core                        false
% 1.19/0.95  --soft_assumptions                      false
% 1.19/0.95  --soft_lemma_size                       3
% 1.19/0.95  --prop_impl_unit_size                   0
% 1.19/0.95  --prop_impl_unit                        []
% 1.19/0.95  --share_sel_clauses                     true
% 1.19/0.95  --reset_solvers                         false
% 1.19/0.95  --bc_imp_inh                            [conj_cone]
% 1.19/0.95  --conj_cone_tolerance                   3.
% 1.19/0.95  --extra_neg_conj                        none
% 1.19/0.95  --large_theory_mode                     true
% 1.19/0.95  --prolific_symb_bound                   200
% 1.19/0.95  --lt_threshold                          2000
% 1.19/0.95  --clause_weak_htbl                      true
% 1.19/0.95  --gc_record_bc_elim                     false
% 1.19/0.95  
% 1.19/0.95  ------ Preprocessing Options
% 1.19/0.95  
% 1.19/0.95  --preprocessing_flag                    true
% 1.19/0.95  --time_out_prep_mult                    0.1
% 1.19/0.95  --splitting_mode                        input
% 1.19/0.95  --splitting_grd                         true
% 1.19/0.95  --splitting_cvd                         false
% 1.19/0.95  --splitting_cvd_svl                     false
% 1.19/0.95  --splitting_nvd                         32
% 1.19/0.95  --sub_typing                            true
% 1.19/0.95  --prep_gs_sim                           true
% 1.19/0.95  --prep_unflatten                        true
% 1.19/0.95  --prep_res_sim                          true
% 1.19/0.95  --prep_upred                            true
% 1.19/0.95  --prep_sem_filter                       exhaustive
% 1.19/0.95  --prep_sem_filter_out                   false
% 1.19/0.95  --pred_elim                             true
% 1.19/0.95  --res_sim_input                         true
% 1.19/0.95  --eq_ax_congr_red                       true
% 1.19/0.95  --pure_diseq_elim                       true
% 1.19/0.95  --brand_transform                       false
% 1.19/0.95  --non_eq_to_eq                          false
% 1.19/0.95  --prep_def_merge                        true
% 1.19/0.95  --prep_def_merge_prop_impl              false
% 1.19/0.95  --prep_def_merge_mbd                    true
% 1.19/0.95  --prep_def_merge_tr_red                 false
% 1.19/0.95  --prep_def_merge_tr_cl                  false
% 1.19/0.95  --smt_preprocessing                     true
% 1.19/0.95  --smt_ac_axioms                         fast
% 1.19/0.95  --preprocessed_out                      false
% 1.19/0.95  --preprocessed_stats                    false
% 1.19/0.95  
% 1.19/0.95  ------ Abstraction refinement Options
% 1.19/0.95  
% 1.19/0.95  --abstr_ref                             []
% 1.19/0.95  --abstr_ref_prep                        false
% 1.19/0.95  --abstr_ref_until_sat                   false
% 1.19/0.95  --abstr_ref_sig_restrict                funpre
% 1.19/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 1.19/0.95  --abstr_ref_under                       []
% 1.19/0.95  
% 1.19/0.95  ------ SAT Options
% 1.19/0.95  
% 1.19/0.95  --sat_mode                              false
% 1.19/0.95  --sat_fm_restart_options                ""
% 1.19/0.95  --sat_gr_def                            false
% 1.19/0.95  --sat_epr_types                         true
% 1.19/0.95  --sat_non_cyclic_types                  false
% 1.19/0.95  --sat_finite_models                     false
% 1.19/0.95  --sat_fm_lemmas                         false
% 1.19/0.95  --sat_fm_prep                           false
% 1.19/0.95  --sat_fm_uc_incr                        true
% 1.19/0.95  --sat_out_model                         small
% 1.19/0.95  --sat_out_clauses                       false
% 1.19/0.95  
% 1.19/0.95  ------ QBF Options
% 1.19/0.95  
% 1.19/0.95  --qbf_mode                              false
% 1.19/0.95  --qbf_elim_univ                         false
% 1.19/0.95  --qbf_dom_inst                          none
% 1.19/0.95  --qbf_dom_pre_inst                      false
% 1.19/0.95  --qbf_sk_in                             false
% 1.19/0.95  --qbf_pred_elim                         true
% 1.19/0.95  --qbf_split                             512
% 1.19/0.95  
% 1.19/0.95  ------ BMC1 Options
% 1.19/0.95  
% 1.19/0.95  --bmc1_incremental                      false
% 1.19/0.95  --bmc1_axioms                           reachable_all
% 1.19/0.95  --bmc1_min_bound                        0
% 1.19/0.95  --bmc1_max_bound                        -1
% 1.19/0.95  --bmc1_max_bound_default                -1
% 1.19/0.95  --bmc1_symbol_reachability              true
% 1.19/0.95  --bmc1_property_lemmas                  false
% 1.19/0.95  --bmc1_k_induction                      false
% 1.19/0.95  --bmc1_non_equiv_states                 false
% 1.19/0.95  --bmc1_deadlock                         false
% 1.19/0.95  --bmc1_ucm                              false
% 1.19/0.95  --bmc1_add_unsat_core                   none
% 1.19/0.95  --bmc1_unsat_core_children              false
% 1.19/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 1.19/0.95  --bmc1_out_stat                         full
% 1.19/0.95  --bmc1_ground_init                      false
% 1.19/0.95  --bmc1_pre_inst_next_state              false
% 1.19/0.95  --bmc1_pre_inst_state                   false
% 1.19/0.95  --bmc1_pre_inst_reach_state             false
% 1.19/0.95  --bmc1_out_unsat_core                   false
% 1.19/0.95  --bmc1_aig_witness_out                  false
% 1.19/0.95  --bmc1_verbose                          false
% 1.19/0.95  --bmc1_dump_clauses_tptp                false
% 1.19/0.95  --bmc1_dump_unsat_core_tptp             false
% 1.19/0.95  --bmc1_dump_file                        -
% 1.19/0.95  --bmc1_ucm_expand_uc_limit              128
% 1.19/0.95  --bmc1_ucm_n_expand_iterations          6
% 1.19/0.95  --bmc1_ucm_extend_mode                  1
% 1.19/0.95  --bmc1_ucm_init_mode                    2
% 1.19/0.95  --bmc1_ucm_cone_mode                    none
% 1.19/0.95  --bmc1_ucm_reduced_relation_type        0
% 1.19/0.95  --bmc1_ucm_relax_model                  4
% 1.19/0.95  --bmc1_ucm_full_tr_after_sat            true
% 1.19/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 1.19/0.95  --bmc1_ucm_layered_model                none
% 1.19/0.95  --bmc1_ucm_max_lemma_size               10
% 1.19/0.95  
% 1.19/0.95  ------ AIG Options
% 1.19/0.95  
% 1.19/0.95  --aig_mode                              false
% 1.19/0.95  
% 1.19/0.95  ------ Instantiation Options
% 1.19/0.95  
% 1.19/0.95  --instantiation_flag                    true
% 1.19/0.95  --inst_sos_flag                         false
% 1.19/0.95  --inst_sos_phase                        true
% 1.19/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.19/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.19/0.95  --inst_lit_sel_side                     none
% 1.19/0.95  --inst_solver_per_active                1400
% 1.19/0.95  --inst_solver_calls_frac                1.
% 1.19/0.95  --inst_passive_queue_type               priority_queues
% 1.19/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.19/0.95  --inst_passive_queues_freq              [25;2]
% 1.19/0.95  --inst_dismatching                      true
% 1.19/0.95  --inst_eager_unprocessed_to_passive     true
% 1.19/0.95  --inst_prop_sim_given                   true
% 1.19/0.95  --inst_prop_sim_new                     false
% 1.19/0.95  --inst_subs_new                         false
% 1.19/0.95  --inst_eq_res_simp                      false
% 1.19/0.95  --inst_subs_given                       false
% 1.19/0.95  --inst_orphan_elimination               true
% 1.19/0.95  --inst_learning_loop_flag               true
% 1.19/0.95  --inst_learning_start                   3000
% 1.19/0.95  --inst_learning_factor                  2
% 1.19/0.95  --inst_start_prop_sim_after_learn       3
% 1.19/0.95  --inst_sel_renew                        solver
% 1.19/0.95  --inst_lit_activity_flag                true
% 1.19/0.95  --inst_restr_to_given                   false
% 1.19/0.95  --inst_activity_threshold               500
% 1.19/0.95  --inst_out_proof                        true
% 1.19/0.95  
% 1.19/0.95  ------ Resolution Options
% 1.19/0.95  
% 1.19/0.95  --resolution_flag                       false
% 1.19/0.95  --res_lit_sel                           adaptive
% 1.19/0.95  --res_lit_sel_side                      none
% 1.19/0.95  --res_ordering                          kbo
% 1.19/0.95  --res_to_prop_solver                    active
% 1.19/0.95  --res_prop_simpl_new                    false
% 1.19/0.95  --res_prop_simpl_given                  true
% 1.19/0.95  --res_passive_queue_type                priority_queues
% 1.19/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.19/0.95  --res_passive_queues_freq               [15;5]
% 1.19/0.95  --res_forward_subs                      full
% 1.19/0.95  --res_backward_subs                     full
% 1.19/0.95  --res_forward_subs_resolution           true
% 1.19/0.95  --res_backward_subs_resolution          true
% 1.19/0.95  --res_orphan_elimination                true
% 1.19/0.95  --res_time_limit                        2.
% 1.19/0.95  --res_out_proof                         true
% 1.19/0.95  
% 1.19/0.95  ------ Superposition Options
% 1.19/0.95  
% 1.19/0.95  --superposition_flag                    true
% 1.19/0.95  --sup_passive_queue_type                priority_queues
% 1.19/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.19/0.95  --sup_passive_queues_freq               [8;1;4]
% 1.19/0.95  --demod_completeness_check              fast
% 1.19/0.95  --demod_use_ground                      true
% 1.19/0.95  --sup_to_prop_solver                    passive
% 1.19/0.95  --sup_prop_simpl_new                    true
% 1.19/0.95  --sup_prop_simpl_given                  true
% 1.19/0.95  --sup_fun_splitting                     false
% 1.19/0.95  --sup_smt_interval                      50000
% 1.19/0.95  
% 1.19/0.95  ------ Superposition Simplification Setup
% 1.19/0.95  
% 1.19/0.95  --sup_indices_passive                   []
% 1.19/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.19/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.19/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.19/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 1.19/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.19/0.95  --sup_full_bw                           [BwDemod]
% 1.19/0.95  --sup_immed_triv                        [TrivRules]
% 1.19/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.19/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.19/0.95  --sup_immed_bw_main                     []
% 1.19/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.19/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 1.19/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.19/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.19/0.95  
% 1.19/0.95  ------ Combination Options
% 1.19/0.95  
% 1.19/0.95  --comb_res_mult                         3
% 1.19/0.95  --comb_sup_mult                         2
% 1.19/0.95  --comb_inst_mult                        10
% 1.19/0.95  
% 1.19/0.95  ------ Debug Options
% 1.19/0.95  
% 1.19/0.95  --dbg_backtrace                         false
% 1.19/0.95  --dbg_dump_prop_clauses                 false
% 1.19/0.95  --dbg_dump_prop_clauses_file            -
% 1.19/0.95  --dbg_out_stat                          false
% 1.19/0.95  
% 1.19/0.95  
% 1.19/0.95  
% 1.19/0.95  
% 1.19/0.95  ------ Proving...
% 1.19/0.95  
% 1.19/0.95  
% 1.19/0.95  % SZS status Theorem for theBenchmark.p
% 1.19/0.95  
% 1.19/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 1.19/0.95  
% 1.19/0.95  fof(f2,axiom,(
% 1.19/0.95    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 1.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.95  
% 1.19/0.95  fof(f26,plain,(
% 1.19/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 1.19/0.95    inference(cnf_transformation,[],[f2])).
% 1.19/0.95  
% 1.19/0.95  fof(f5,axiom,(
% 1.19/0.95    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 1.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.95  
% 1.19/0.95  fof(f29,plain,(
% 1.19/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.19/0.95    inference(cnf_transformation,[],[f5])).
% 1.19/0.95  
% 1.19/0.95  fof(f12,axiom,(
% 1.19/0.95    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.95  
% 1.19/0.95  fof(f36,plain,(
% 1.19/0.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.19/0.95    inference(cnf_transformation,[],[f12])).
% 1.19/0.95  
% 1.19/0.95  fof(f6,axiom,(
% 1.19/0.95    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.95  
% 1.19/0.95  fof(f30,plain,(
% 1.19/0.95    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.19/0.95    inference(cnf_transformation,[],[f6])).
% 1.19/0.95  
% 1.19/0.95  fof(f47,plain,(
% 1.19/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X2)))) )),
% 1.19/0.95    inference(definition_unfolding,[],[f29,f36,f30])).
% 1.19/0.95  
% 1.19/0.95  fof(f50,plain,(
% 1.19/0.95    ( ! [X2,X0,X1] : (k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X2))) = k3_tarski(k2_tarski(k2_tarski(X1,X1),k2_tarski(X2,X0)))) )),
% 1.19/0.95    inference(definition_unfolding,[],[f26,f47,f47])).
% 1.19/0.95  
% 1.19/0.95  fof(f7,axiom,(
% 1.19/0.95    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.95  
% 1.19/0.95  fof(f31,plain,(
% 1.19/0.95    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.19/0.95    inference(cnf_transformation,[],[f7])).
% 1.19/0.95  
% 1.19/0.95  fof(f52,plain,(
% 1.19/0.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)))) )),
% 1.19/0.95    inference(definition_unfolding,[],[f31,f47])).
% 1.19/0.95  
% 1.19/0.95  fof(f4,axiom,(
% 1.19/0.95    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.95  
% 1.19/0.95  fof(f28,plain,(
% 1.19/0.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.19/0.95    inference(cnf_transformation,[],[f4])).
% 1.19/0.95  
% 1.19/0.95  fof(f48,plain,(
% 1.19/0.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1)))) )),
% 1.19/0.95    inference(definition_unfolding,[],[f28,f36,f30,f30])).
% 1.19/0.95  
% 1.19/0.95  fof(f14,axiom,(
% 1.19/0.95    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.95  
% 1.19/0.95  fof(f38,plain,(
% 1.19/0.95    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.19/0.95    inference(cnf_transformation,[],[f14])).
% 1.19/0.95  
% 1.19/0.95  fof(f17,axiom,(
% 1.19/0.95    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 1.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.95  
% 1.19/0.95  fof(f21,plain,(
% 1.19/0.95    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.19/0.95    inference(ennf_transformation,[],[f17])).
% 1.19/0.95  
% 1.19/0.95  fof(f42,plain,(
% 1.19/0.95    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.19/0.95    inference(cnf_transformation,[],[f21])).
% 1.19/0.95  
% 1.19/0.95  fof(f13,axiom,(
% 1.19/0.95    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.95  
% 1.19/0.95  fof(f37,plain,(
% 1.19/0.95    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.19/0.95    inference(cnf_transformation,[],[f13])).
% 1.19/0.95  
% 1.19/0.95  fof(f54,plain,(
% 1.19/0.95    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(k1_relat_1(X1),X0)) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 1.19/0.95    inference(definition_unfolding,[],[f42,f37])).
% 1.19/0.95  
% 1.19/0.95  fof(f16,axiom,(
% 1.19/0.95    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.95  
% 1.19/0.95  fof(f40,plain,(
% 1.19/0.95    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.19/0.95    inference(cnf_transformation,[],[f16])).
% 1.19/0.95  
% 1.19/0.95  fof(f18,conjecture,(
% 1.19/0.95    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.95  
% 1.19/0.95  fof(f19,negated_conjecture,(
% 1.19/0.95    ~! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.19/0.95    inference(negated_conjecture,[],[f18])).
% 1.19/0.95  
% 1.19/0.95  fof(f22,plain,(
% 1.19/0.95    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.19/0.95    inference(ennf_transformation,[],[f19])).
% 1.19/0.95  
% 1.19/0.95  fof(f23,plain,(
% 1.19/0.95    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1)) => (k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1))),
% 1.19/0.95    introduced(choice_axiom,[])).
% 1.19/0.95  
% 1.19/0.95  fof(f24,plain,(
% 1.19/0.95    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1)),
% 1.19/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f23])).
% 1.19/0.95  
% 1.19/0.95  fof(f43,plain,(
% 1.19/0.95    v1_relat_1(sK1)),
% 1.19/0.95    inference(cnf_transformation,[],[f24])).
% 1.19/0.95  
% 1.19/0.95  fof(f15,axiom,(
% 1.19/0.95    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))))),
% 1.19/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.19/0.95  
% 1.19/0.95  fof(f20,plain,(
% 1.19/0.95    ! [X0] : (! [X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.19/0.95    inference(ennf_transformation,[],[f15])).
% 1.19/0.95  
% 1.19/0.95  fof(f39,plain,(
% 1.19/0.95    ( ! [X0,X1] : (k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.19/0.95    inference(cnf_transformation,[],[f20])).
% 1.19/0.95  
% 1.19/0.95  fof(f44,plain,(
% 1.19/0.95    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),
% 1.19/0.95    inference(cnf_transformation,[],[f24])).
% 1.19/0.95  
% 1.19/0.95  fof(f55,plain,(
% 1.19/0.95    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0)))),
% 1.19/0.95    inference(definition_unfolding,[],[f44,f37])).
% 1.19/0.95  
% 1.19/0.95  cnf(c_2,plain,
% 1.19/0.95      ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X2))) = k3_tarski(k2_tarski(k2_tarski(X2,X2),k2_tarski(X0,X1))) ),
% 1.19/0.95      inference(cnf_transformation,[],[f50]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_4,plain,
% 1.19/0.95      ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1))) = k2_tarski(X0,X1) ),
% 1.19/0.95      inference(cnf_transformation,[],[f52]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_418,plain,
% 1.19/0.95      ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X1,X0) ),
% 1.19/0.95      inference(superposition,[status(thm)],[c_2,c_4]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_0,plain,
% 1.19/0.95      ( k3_tarski(k2_tarski(k2_tarski(X0,X0),k2_tarski(X1,X1))) = k2_tarski(X0,X1) ),
% 1.19/0.95      inference(cnf_transformation,[],[f48]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_887,plain,
% 1.19/0.95      ( k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
% 1.19/0.95      inference(superposition,[status(thm)],[c_418,c_0]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_6,plain,
% 1.19/0.95      ( v1_relat_1(k6_relat_1(X0)) ),
% 1.19/0.95      inference(cnf_transformation,[],[f38]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_161,plain,
% 1.19/0.95      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 1.19/0.95      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_10,plain,
% 1.19/0.95      ( ~ v1_relat_1(X0)
% 1.19/0.95      | k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1)) ),
% 1.19/0.95      inference(cnf_transformation,[],[f54]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_159,plain,
% 1.19/0.95      ( k1_setfam_1(k2_tarski(k1_relat_1(X0),X1)) = k1_relat_1(k7_relat_1(X0,X1))
% 1.19/0.95      | v1_relat_1(X0) != iProver_top ),
% 1.19/0.95      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_280,plain,
% 1.19/0.95      ( k1_setfam_1(k2_tarski(k1_relat_1(k6_relat_1(X0)),X1)) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
% 1.19/0.95      inference(superposition,[status(thm)],[c_161,c_159]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_9,plain,
% 1.19/0.95      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 1.19/0.95      inference(cnf_transformation,[],[f40]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_285,plain,
% 1.19/0.95      ( k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
% 1.19/0.95      inference(light_normalisation,[status(thm)],[c_280,c_9]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_12,negated_conjecture,
% 1.19/0.95      ( v1_relat_1(sK1) ),
% 1.19/0.95      inference(cnf_transformation,[],[f43]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_158,plain,
% 1.19/0.95      ( v1_relat_1(sK1) = iProver_top ),
% 1.19/0.95      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_7,plain,
% 1.19/0.95      ( ~ v1_relat_1(X0)
% 1.19/0.95      | ~ v1_relat_1(X1)
% 1.19/0.95      | k7_relat_1(X1,k1_relat_1(k7_relat_1(X0,k1_relat_1(X1)))) = k7_relat_1(X1,k1_relat_1(X0)) ),
% 1.19/0.95      inference(cnf_transformation,[],[f39]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_160,plain,
% 1.19/0.95      ( k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) = k7_relat_1(X0,k1_relat_1(X1))
% 1.19/0.95      | v1_relat_1(X1) != iProver_top
% 1.19/0.95      | v1_relat_1(X0) != iProver_top ),
% 1.19/0.95      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_338,plain,
% 1.19/0.95      ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(X0,k1_relat_1(sK1)))) = k7_relat_1(sK1,k1_relat_1(X0))
% 1.19/0.95      | v1_relat_1(X0) != iProver_top ),
% 1.19/0.95      inference(superposition,[status(thm)],[c_158,c_160]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_572,plain,
% 1.19/0.95      ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)))) = k7_relat_1(sK1,k1_relat_1(k6_relat_1(X0))) ),
% 1.19/0.95      inference(superposition,[status(thm)],[c_161,c_338]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_577,plain,
% 1.19/0.95      ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(k6_relat_1(X0),k1_relat_1(sK1)))) = k7_relat_1(sK1,X0) ),
% 1.19/0.95      inference(light_normalisation,[status(thm)],[c_572,c_9]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_735,plain,
% 1.19/0.95      ( k7_relat_1(sK1,k1_setfam_1(k2_tarski(X0,k1_relat_1(sK1)))) = k7_relat_1(sK1,X0) ),
% 1.19/0.95      inference(demodulation,[status(thm)],[c_285,c_577]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_917,plain,
% 1.19/0.95      ( k7_relat_1(sK1,k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0))) = k7_relat_1(sK1,X0) ),
% 1.19/0.95      inference(superposition,[status(thm)],[c_887,c_735]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_281,plain,
% 1.19/0.95      ( k1_setfam_1(k2_tarski(k1_relat_1(sK1),X0)) = k1_relat_1(k7_relat_1(sK1,X0)) ),
% 1.19/0.95      inference(superposition,[status(thm)],[c_158,c_159]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_919,plain,
% 1.19/0.95      ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,X0))) = k7_relat_1(sK1,X0) ),
% 1.19/0.95      inference(light_normalisation,[status(thm)],[c_917,c_281]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_11,negated_conjecture,
% 1.19/0.95      ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k1_setfam_1(k2_tarski(k1_relat_1(sK1),sK0))) ),
% 1.19/0.95      inference(cnf_transformation,[],[f55]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_525,plain,
% 1.19/0.95      ( k7_relat_1(sK1,k1_relat_1(k7_relat_1(sK1,sK0))) != k7_relat_1(sK1,sK0) ),
% 1.19/0.95      inference(demodulation,[status(thm)],[c_281,c_11]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_1105,plain,
% 1.19/0.95      ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,sK0) ),
% 1.19/0.95      inference(demodulation,[status(thm)],[c_919,c_525]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_69,plain,( X0 = X0 ),theory(equality) ).
% 1.19/0.95  
% 1.19/0.95  cnf(c_214,plain,
% 1.19/0.95      ( k7_relat_1(sK1,sK0) = k7_relat_1(sK1,sK0) ),
% 1.19/0.95      inference(instantiation,[status(thm)],[c_69]) ).
% 1.19/0.95  
% 1.19/0.95  cnf(contradiction,plain,
% 1.19/0.95      ( $false ),
% 1.19/0.95      inference(minisat,[status(thm)],[c_1105,c_214]) ).
% 1.19/0.95  
% 1.19/0.95  
% 1.19/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 1.19/0.95  
% 1.19/0.95  ------                               Statistics
% 1.19/0.95  
% 1.19/0.95  ------ General
% 1.19/0.95  
% 1.19/0.95  abstr_ref_over_cycles:                  0
% 1.19/0.95  abstr_ref_under_cycles:                 0
% 1.19/0.95  gc_basic_clause_elim:                   0
% 1.19/0.95  forced_gc_time:                         0
% 1.19/0.95  parsing_time:                           0.008
% 1.19/0.95  unif_index_cands_time:                  0.
% 1.19/0.95  unif_index_add_time:                    0.
% 1.19/0.95  orderings_time:                         0.
% 1.19/0.95  out_proof_time:                         0.006
% 1.19/0.95  total_time:                             0.089
% 1.19/0.95  num_of_symbols:                         42
% 1.19/0.95  num_of_terms:                           1166
% 1.19/0.95  
% 1.19/0.95  ------ Preprocessing
% 1.19/0.95  
% 1.19/0.95  num_of_splits:                          0
% 1.19/0.95  num_of_split_atoms:                     0
% 1.19/0.95  num_of_reused_defs:                     0
% 1.19/0.95  num_eq_ax_congr_red:                    16
% 1.19/0.95  num_of_sem_filtered_clauses:            1
% 1.19/0.95  num_of_subtypes:                        0
% 1.19/0.95  monotx_restored_types:                  0
% 1.19/0.95  sat_num_of_epr_types:                   0
% 1.19/0.95  sat_num_of_non_cyclic_types:            0
% 1.19/0.95  sat_guarded_non_collapsed_types:        0
% 1.19/0.95  num_pure_diseq_elim:                    0
% 1.19/0.95  simp_replaced_by:                       0
% 1.19/0.95  res_preprocessed:                       58
% 1.19/0.95  prep_upred:                             0
% 1.19/0.95  prep_unflattend:                        0
% 1.19/0.95  smt_new_axioms:                         0
% 1.19/0.95  pred_elim_cands:                        1
% 1.19/0.95  pred_elim:                              0
% 1.19/0.95  pred_elim_cl:                           0
% 1.19/0.95  pred_elim_cycles:                       1
% 1.19/0.95  merged_defs:                            0
% 1.19/0.95  merged_defs_ncl:                        0
% 1.19/0.95  bin_hyper_res:                          0
% 1.19/0.95  prep_cycles:                            3
% 1.19/0.95  pred_elim_time:                         0.
% 1.19/0.95  splitting_time:                         0.
% 1.19/0.95  sem_filter_time:                        0.
% 1.19/0.95  monotx_time:                            0.
% 1.19/0.95  subtype_inf_time:                       0.
% 1.19/0.95  
% 1.19/0.95  ------ Problem properties
% 1.19/0.95  
% 1.19/0.95  clauses:                                13
% 1.19/0.95  conjectures:                            2
% 1.19/0.95  epr:                                    1
% 1.19/0.95  horn:                                   13
% 1.19/0.95  ground:                                 2
% 1.19/0.95  unary:                                  11
% 1.19/0.95  binary:                                 1
% 1.19/0.95  lits:                                   16
% 1.19/0.95  lits_eq:                                11
% 1.19/0.95  fd_pure:                                0
% 1.19/0.95  fd_pseudo:                              0
% 1.19/0.95  fd_cond:                                0
% 1.19/0.95  fd_pseudo_cond:                         0
% 1.19/0.95  ac_symbols:                             0
% 1.19/0.95  
% 1.19/0.95  ------ Propositional Solver
% 1.19/0.95  
% 1.19/0.95  prop_solver_calls:                      26
% 1.19/0.95  prop_fast_solver_calls:                 216
% 1.19/0.95  smt_solver_calls:                       0
% 1.19/0.95  smt_fast_solver_calls:                  0
% 1.19/0.95  prop_num_of_clauses:                    449
% 1.19/0.95  prop_preprocess_simplified:             1697
% 1.19/0.95  prop_fo_subsumed:                       0
% 1.19/0.95  prop_solver_time:                       0.
% 1.19/0.95  smt_solver_time:                        0.
% 1.19/0.95  smt_fast_solver_time:                   0.
% 1.19/0.95  prop_fast_solver_time:                  0.
% 1.19/0.95  prop_unsat_core_time:                   0.
% 1.19/0.95  
% 1.19/0.95  ------ QBF
% 1.19/0.95  
% 1.19/0.95  qbf_q_res:                              0
% 1.19/0.95  qbf_num_tautologies:                    0
% 1.19/0.95  qbf_prep_cycles:                        0
% 1.19/0.95  
% 1.19/0.95  ------ BMC1
% 1.19/0.95  
% 1.19/0.95  bmc1_current_bound:                     -1
% 1.19/0.95  bmc1_last_solved_bound:                 -1
% 1.19/0.95  bmc1_unsat_core_size:                   -1
% 1.19/0.95  bmc1_unsat_core_parents_size:           -1
% 1.19/0.95  bmc1_merge_next_fun:                    0
% 1.19/0.95  bmc1_unsat_core_clauses_time:           0.
% 1.19/0.95  
% 1.19/0.95  ------ Instantiation
% 1.19/0.95  
% 1.19/0.95  inst_num_of_clauses:                    271
% 1.19/0.95  inst_num_in_passive:                    49
% 1.19/0.95  inst_num_in_active:                     145
% 1.19/0.95  inst_num_in_unprocessed:                77
% 1.19/0.95  inst_num_of_loops:                      150
% 1.19/0.95  inst_num_of_learning_restarts:          0
% 1.19/0.95  inst_num_moves_active_passive:          0
% 1.19/0.95  inst_lit_activity:                      0
% 1.19/0.95  inst_lit_activity_moves:                0
% 1.19/0.95  inst_num_tautologies:                   0
% 1.19/0.95  inst_num_prop_implied:                  0
% 1.19/0.95  inst_num_existing_simplified:           0
% 1.19/0.95  inst_num_eq_res_simplified:             0
% 1.19/0.95  inst_num_child_elim:                    0
% 1.19/0.95  inst_num_of_dismatching_blockings:      28
% 1.19/0.95  inst_num_of_non_proper_insts:           211
% 1.19/0.95  inst_num_of_duplicates:                 0
% 1.19/0.95  inst_inst_num_from_inst_to_res:         0
% 1.19/0.95  inst_dismatching_checking_time:         0.
% 1.19/0.95  
% 1.19/0.95  ------ Resolution
% 1.19/0.95  
% 1.19/0.95  res_num_of_clauses:                     0
% 1.19/0.95  res_num_in_passive:                     0
% 1.19/0.95  res_num_in_active:                      0
% 1.19/0.95  res_num_of_loops:                       61
% 1.19/0.95  res_forward_subset_subsumed:            49
% 1.19/0.95  res_backward_subset_subsumed:           0
% 1.19/0.95  res_forward_subsumed:                   0
% 1.19/0.95  res_backward_subsumed:                  0
% 1.19/0.95  res_forward_subsumption_resolution:     0
% 1.19/0.95  res_backward_subsumption_resolution:    0
% 1.19/0.95  res_clause_to_clause_subsumption:       186
% 1.19/0.95  res_orphan_elimination:                 0
% 1.19/0.95  res_tautology_del:                      40
% 1.19/0.95  res_num_eq_res_simplified:              0
% 1.19/0.95  res_num_sel_changes:                    0
% 1.19/0.95  res_moves_from_active_to_pass:          0
% 1.19/0.95  
% 1.19/0.95  ------ Superposition
% 1.19/0.95  
% 1.19/0.95  sup_time_total:                         0.
% 1.19/0.95  sup_time_generating:                    0.
% 1.19/0.95  sup_time_sim_full:                      0.
% 1.19/0.95  sup_time_sim_immed:                     0.
% 1.19/0.95  
% 1.19/0.95  sup_num_of_clauses:                     47
% 1.19/0.95  sup_num_in_active:                      24
% 1.19/0.95  sup_num_in_passive:                     23
% 1.19/0.95  sup_num_of_loops:                       28
% 1.19/0.95  sup_fw_superposition:                   48
% 1.19/0.95  sup_bw_superposition:                   52
% 1.19/0.95  sup_immediate_simplified:               6
% 1.19/0.95  sup_given_eliminated:                   0
% 1.19/0.95  comparisons_done:                       0
% 1.19/0.95  comparisons_avoided:                    0
% 1.19/0.95  
% 1.19/0.95  ------ Simplifications
% 1.19/0.95  
% 1.19/0.95  
% 1.19/0.95  sim_fw_subset_subsumed:                 0
% 1.19/0.95  sim_bw_subset_subsumed:                 0
% 1.19/0.95  sim_fw_subsumed:                        0
% 1.19/0.95  sim_bw_subsumed:                        0
% 1.19/0.95  sim_fw_subsumption_res:                 0
% 1.19/0.95  sim_bw_subsumption_res:                 0
% 1.19/0.95  sim_tautology_del:                      0
% 1.19/0.95  sim_eq_tautology_del:                   0
% 1.19/0.95  sim_eq_res_simp:                        0
% 1.19/0.95  sim_fw_demodulated:                     2
% 1.19/0.95  sim_bw_demodulated:                     4
% 1.19/0.95  sim_light_normalised:                   4
% 1.19/0.95  sim_joinable_taut:                      0
% 1.19/0.95  sim_joinable_simp:                      0
% 1.19/0.95  sim_ac_normalised:                      0
% 1.19/0.95  sim_smt_subsumption:                    0
% 1.19/0.95  
%------------------------------------------------------------------------------
