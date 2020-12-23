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
% DateTime   : Thu Dec  3 11:50:10 EST 2020

% Result     : Theorem 1.10s
% Output     : CNFRefutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 101 expanded)
%              Number of clauses        :   28 (  44 expanded)
%              Number of leaves         :   10 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :   92 ( 150 expanded)
%              Number of equality atoms :   59 (  87 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f19,f20])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f24,f20])).

fof(f25,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f9,conjecture,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f9])).

fof(f16,plain,(
    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f10])).

fof(f17,plain,
    ( ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
   => k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f28,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f31,plain,(
    k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f28,f20])).

cnf(c_0,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_249,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_3,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_115,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | k8_relat_1(X1,X0) = X0
    | k6_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_116,plain,
    ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
    | k8_relat_1(X1,k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_115])).

cnf(c_248,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(k2_relat_1(k6_relat_1(X1)),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_116])).

cnf(c_5,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_264,plain,
    ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_248,c_5])).

cnf(c_480,plain,
    ( k8_relat_1(X0,k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_249,c_264])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_103,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | k6_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_104,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(unflattening,[status(thm)],[c_103])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_127,plain,
    ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
    | k6_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_128,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
    inference(unflattening,[status(thm)],[c_127])).

cnf(c_258,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(light_normalisation,[status(thm)],[c_104,c_128])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1))) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_109,plain,
    ( k7_relat_1(X0,k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1))) = k7_relat_1(X0,X1)
    | k6_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_4])).

cnf(c_110,plain,
    ( k7_relat_1(k6_relat_1(X0),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(unflattening,[status(thm)],[c_109])).

cnf(c_6,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_269,plain,
    ( k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(light_normalisation,[status(thm)],[c_110,c_6,c_258])).

cnf(c_442,plain,
    ( k8_relat_1(X0,k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(superposition,[status(thm)],[c_258,c_269])).

cnf(c_481,plain,
    ( k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(light_normalisation,[status(thm)],[c_480,c_442])).

cnf(c_8,negated_conjecture,
    ( k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_261,plain,
    ( k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_8,c_128])).

cnf(c_484,plain,
    ( k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(demodulation,[status(thm)],[c_481,c_261])).

cnf(c_488,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_484])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:49:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.10/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.10/0.94  
% 1.10/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.10/0.94  
% 1.10/0.94  ------  iProver source info
% 1.10/0.94  
% 1.10/0.94  git: date: 2020-06-30 10:37:57 +0100
% 1.10/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.10/0.94  git: non_committed_changes: false
% 1.10/0.94  git: last_make_outside_of_git: false
% 1.10/0.94  
% 1.10/0.94  ------ 
% 1.10/0.94  
% 1.10/0.94  ------ Input Options
% 1.10/0.94  
% 1.10/0.94  --out_options                           all
% 1.10/0.94  --tptp_safe_out                         true
% 1.10/0.94  --problem_path                          ""
% 1.10/0.94  --include_path                          ""
% 1.10/0.94  --clausifier                            res/vclausify_rel
% 1.10/0.94  --clausifier_options                    --mode clausify
% 1.10/0.94  --stdin                                 false
% 1.10/0.94  --stats_out                             all
% 1.10/0.94  
% 1.10/0.94  ------ General Options
% 1.10/0.94  
% 1.10/0.94  --fof                                   false
% 1.10/0.94  --time_out_real                         305.
% 1.10/0.94  --time_out_virtual                      -1.
% 1.10/0.94  --symbol_type_check                     false
% 1.10/0.94  --clausify_out                          false
% 1.10/0.94  --sig_cnt_out                           false
% 1.10/0.94  --trig_cnt_out                          false
% 1.10/0.94  --trig_cnt_out_tolerance                1.
% 1.10/0.94  --trig_cnt_out_sk_spl                   false
% 1.10/0.94  --abstr_cl_out                          false
% 1.10/0.94  
% 1.10/0.94  ------ Global Options
% 1.10/0.94  
% 1.10/0.94  --schedule                              default
% 1.10/0.94  --add_important_lit                     false
% 1.10/0.94  --prop_solver_per_cl                    1000
% 1.10/0.94  --min_unsat_core                        false
% 1.10/0.94  --soft_assumptions                      false
% 1.10/0.94  --soft_lemma_size                       3
% 1.10/0.94  --prop_impl_unit_size                   0
% 1.10/0.94  --prop_impl_unit                        []
% 1.10/0.94  --share_sel_clauses                     true
% 1.10/0.94  --reset_solvers                         false
% 1.10/0.94  --bc_imp_inh                            [conj_cone]
% 1.10/0.94  --conj_cone_tolerance                   3.
% 1.10/0.94  --extra_neg_conj                        none
% 1.10/0.94  --large_theory_mode                     true
% 1.10/0.94  --prolific_symb_bound                   200
% 1.10/0.94  --lt_threshold                          2000
% 1.10/0.94  --clause_weak_htbl                      true
% 1.10/0.94  --gc_record_bc_elim                     false
% 1.10/0.94  
% 1.10/0.94  ------ Preprocessing Options
% 1.10/0.94  
% 1.10/0.94  --preprocessing_flag                    true
% 1.10/0.94  --time_out_prep_mult                    0.1
% 1.10/0.94  --splitting_mode                        input
% 1.10/0.94  --splitting_grd                         true
% 1.10/0.94  --splitting_cvd                         false
% 1.10/0.94  --splitting_cvd_svl                     false
% 1.10/0.94  --splitting_nvd                         32
% 1.10/0.94  --sub_typing                            true
% 1.10/0.94  --prep_gs_sim                           true
% 1.10/0.94  --prep_unflatten                        true
% 1.10/0.94  --prep_res_sim                          true
% 1.10/0.94  --prep_upred                            true
% 1.10/0.94  --prep_sem_filter                       exhaustive
% 1.10/0.94  --prep_sem_filter_out                   false
% 1.10/0.94  --pred_elim                             true
% 1.10/0.94  --res_sim_input                         true
% 1.10/0.94  --eq_ax_congr_red                       true
% 1.10/0.94  --pure_diseq_elim                       true
% 1.10/0.94  --brand_transform                       false
% 1.10/0.94  --non_eq_to_eq                          false
% 1.10/0.94  --prep_def_merge                        true
% 1.10/0.94  --prep_def_merge_prop_impl              false
% 1.10/0.94  --prep_def_merge_mbd                    true
% 1.10/0.94  --prep_def_merge_tr_red                 false
% 1.10/0.94  --prep_def_merge_tr_cl                  false
% 1.10/0.94  --smt_preprocessing                     true
% 1.10/0.94  --smt_ac_axioms                         fast
% 1.10/0.94  --preprocessed_out                      false
% 1.10/0.94  --preprocessed_stats                    false
% 1.10/0.94  
% 1.10/0.94  ------ Abstraction refinement Options
% 1.10/0.94  
% 1.10/0.94  --abstr_ref                             []
% 1.10/0.94  --abstr_ref_prep                        false
% 1.10/0.94  --abstr_ref_until_sat                   false
% 1.10/0.94  --abstr_ref_sig_restrict                funpre
% 1.10/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 1.10/0.94  --abstr_ref_under                       []
% 1.10/0.94  
% 1.10/0.94  ------ SAT Options
% 1.10/0.94  
% 1.10/0.94  --sat_mode                              false
% 1.10/0.94  --sat_fm_restart_options                ""
% 1.10/0.94  --sat_gr_def                            false
% 1.10/0.94  --sat_epr_types                         true
% 1.10/0.94  --sat_non_cyclic_types                  false
% 1.10/0.94  --sat_finite_models                     false
% 1.10/0.94  --sat_fm_lemmas                         false
% 1.10/0.94  --sat_fm_prep                           false
% 1.10/0.94  --sat_fm_uc_incr                        true
% 1.10/0.94  --sat_out_model                         small
% 1.10/0.94  --sat_out_clauses                       false
% 1.10/0.94  
% 1.10/0.94  ------ QBF Options
% 1.10/0.94  
% 1.10/0.94  --qbf_mode                              false
% 1.10/0.94  --qbf_elim_univ                         false
% 1.10/0.94  --qbf_dom_inst                          none
% 1.10/0.94  --qbf_dom_pre_inst                      false
% 1.10/0.94  --qbf_sk_in                             false
% 1.10/0.94  --qbf_pred_elim                         true
% 1.10/0.94  --qbf_split                             512
% 1.10/0.94  
% 1.10/0.94  ------ BMC1 Options
% 1.10/0.94  
% 1.10/0.94  --bmc1_incremental                      false
% 1.10/0.94  --bmc1_axioms                           reachable_all
% 1.10/0.94  --bmc1_min_bound                        0
% 1.10/0.94  --bmc1_max_bound                        -1
% 1.10/0.94  --bmc1_max_bound_default                -1
% 1.10/0.94  --bmc1_symbol_reachability              true
% 1.10/0.94  --bmc1_property_lemmas                  false
% 1.10/0.94  --bmc1_k_induction                      false
% 1.10/0.94  --bmc1_non_equiv_states                 false
% 1.10/0.94  --bmc1_deadlock                         false
% 1.10/0.94  --bmc1_ucm                              false
% 1.10/0.94  --bmc1_add_unsat_core                   none
% 1.10/0.94  --bmc1_unsat_core_children              false
% 1.10/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 1.10/0.94  --bmc1_out_stat                         full
% 1.10/0.94  --bmc1_ground_init                      false
% 1.10/0.94  --bmc1_pre_inst_next_state              false
% 1.10/0.94  --bmc1_pre_inst_state                   false
% 1.10/0.94  --bmc1_pre_inst_reach_state             false
% 1.10/0.94  --bmc1_out_unsat_core                   false
% 1.10/0.94  --bmc1_aig_witness_out                  false
% 1.10/0.94  --bmc1_verbose                          false
% 1.10/0.94  --bmc1_dump_clauses_tptp                false
% 1.10/0.94  --bmc1_dump_unsat_core_tptp             false
% 1.10/0.94  --bmc1_dump_file                        -
% 1.10/0.94  --bmc1_ucm_expand_uc_limit              128
% 1.10/0.94  --bmc1_ucm_n_expand_iterations          6
% 1.10/0.94  --bmc1_ucm_extend_mode                  1
% 1.10/0.94  --bmc1_ucm_init_mode                    2
% 1.10/0.94  --bmc1_ucm_cone_mode                    none
% 1.10/0.94  --bmc1_ucm_reduced_relation_type        0
% 1.10/0.94  --bmc1_ucm_relax_model                  4
% 1.10/0.94  --bmc1_ucm_full_tr_after_sat            true
% 1.10/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 1.10/0.94  --bmc1_ucm_layered_model                none
% 1.10/0.94  --bmc1_ucm_max_lemma_size               10
% 1.10/0.94  
% 1.10/0.94  ------ AIG Options
% 1.10/0.94  
% 1.10/0.94  --aig_mode                              false
% 1.10/0.94  
% 1.10/0.94  ------ Instantiation Options
% 1.10/0.94  
% 1.10/0.94  --instantiation_flag                    true
% 1.10/0.94  --inst_sos_flag                         false
% 1.10/0.94  --inst_sos_phase                        true
% 1.10/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.10/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.10/0.94  --inst_lit_sel_side                     num_symb
% 1.10/0.94  --inst_solver_per_active                1400
% 1.10/0.94  --inst_solver_calls_frac                1.
% 1.10/0.94  --inst_passive_queue_type               priority_queues
% 1.10/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.10/0.94  --inst_passive_queues_freq              [25;2]
% 1.10/0.94  --inst_dismatching                      true
% 1.10/0.94  --inst_eager_unprocessed_to_passive     true
% 1.10/0.94  --inst_prop_sim_given                   true
% 1.10/0.94  --inst_prop_sim_new                     false
% 1.10/0.94  --inst_subs_new                         false
% 1.10/0.94  --inst_eq_res_simp                      false
% 1.10/0.94  --inst_subs_given                       false
% 1.10/0.94  --inst_orphan_elimination               true
% 1.10/0.94  --inst_learning_loop_flag               true
% 1.10/0.94  --inst_learning_start                   3000
% 1.10/0.94  --inst_learning_factor                  2
% 1.10/0.94  --inst_start_prop_sim_after_learn       3
% 1.10/0.94  --inst_sel_renew                        solver
% 1.10/0.94  --inst_lit_activity_flag                true
% 1.10/0.94  --inst_restr_to_given                   false
% 1.10/0.94  --inst_activity_threshold               500
% 1.10/0.94  --inst_out_proof                        true
% 1.10/0.94  
% 1.10/0.94  ------ Resolution Options
% 1.10/0.94  
% 1.10/0.94  --resolution_flag                       true
% 1.10/0.94  --res_lit_sel                           adaptive
% 1.10/0.94  --res_lit_sel_side                      none
% 1.10/0.94  --res_ordering                          kbo
% 1.10/0.94  --res_to_prop_solver                    active
% 1.10/0.94  --res_prop_simpl_new                    false
% 1.10/0.94  --res_prop_simpl_given                  true
% 1.10/0.94  --res_passive_queue_type                priority_queues
% 1.10/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.10/0.94  --res_passive_queues_freq               [15;5]
% 1.10/0.94  --res_forward_subs                      full
% 1.10/0.94  --res_backward_subs                     full
% 1.10/0.94  --res_forward_subs_resolution           true
% 1.10/0.94  --res_backward_subs_resolution          true
% 1.10/0.94  --res_orphan_elimination                true
% 1.10/0.94  --res_time_limit                        2.
% 1.10/0.94  --res_out_proof                         true
% 1.10/0.94  
% 1.10/0.94  ------ Superposition Options
% 1.10/0.94  
% 1.10/0.94  --superposition_flag                    true
% 1.10/0.94  --sup_passive_queue_type                priority_queues
% 1.10/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.10/0.94  --sup_passive_queues_freq               [8;1;4]
% 1.10/0.94  --demod_completeness_check              fast
% 1.10/0.94  --demod_use_ground                      true
% 1.10/0.94  --sup_to_prop_solver                    passive
% 1.10/0.94  --sup_prop_simpl_new                    true
% 1.10/0.94  --sup_prop_simpl_given                  true
% 1.10/0.94  --sup_fun_splitting                     false
% 1.10/0.94  --sup_smt_interval                      50000
% 1.10/0.94  
% 1.10/0.94  ------ Superposition Simplification Setup
% 1.10/0.94  
% 1.10/0.94  --sup_indices_passive                   []
% 1.10/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 1.10/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/0.94  --sup_full_bw                           [BwDemod]
% 1.10/0.94  --sup_immed_triv                        [TrivRules]
% 1.10/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.10/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/0.94  --sup_immed_bw_main                     []
% 1.10/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 1.10/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/0.94  
% 1.10/0.94  ------ Combination Options
% 1.10/0.94  
% 1.10/0.94  --comb_res_mult                         3
% 1.10/0.94  --comb_sup_mult                         2
% 1.10/0.94  --comb_inst_mult                        10
% 1.10/0.94  
% 1.10/0.94  ------ Debug Options
% 1.10/0.94  
% 1.10/0.94  --dbg_backtrace                         false
% 1.10/0.94  --dbg_dump_prop_clauses                 false
% 1.10/0.94  --dbg_dump_prop_clauses_file            -
% 1.10/0.94  --dbg_out_stat                          false
% 1.10/0.94  ------ Parsing...
% 1.10/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.10/0.94  
% 1.10/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.10/0.94  
% 1.10/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.10/0.94  
% 1.10/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.10/0.94  ------ Proving...
% 1.10/0.94  ------ Problem Properties 
% 1.10/0.94  
% 1.10/0.94  
% 1.10/0.94  clauses                                 8
% 1.10/0.94  conjectures                             1
% 1.10/0.94  EPR                                     0
% 1.10/0.94  Horn                                    8
% 1.10/0.94  unary                                   7
% 1.10/0.94  binary                                  1
% 1.10/0.94  lits                                    9
% 1.10/0.94  lits eq                                 7
% 1.10/0.94  fd_pure                                 0
% 1.10/0.94  fd_pseudo                               0
% 1.10/0.94  fd_cond                                 0
% 1.10/0.94  fd_pseudo_cond                          0
% 1.10/0.94  AC symbols                              0
% 1.10/0.94  
% 1.10/0.94  ------ Schedule dynamic 5 is on 
% 1.10/0.94  
% 1.10/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.10/0.94  
% 1.10/0.94  
% 1.10/0.94  ------ 
% 1.10/0.94  Current options:
% 1.10/0.94  ------ 
% 1.10/0.94  
% 1.10/0.94  ------ Input Options
% 1.10/0.94  
% 1.10/0.94  --out_options                           all
% 1.10/0.94  --tptp_safe_out                         true
% 1.10/0.94  --problem_path                          ""
% 1.10/0.94  --include_path                          ""
% 1.10/0.94  --clausifier                            res/vclausify_rel
% 1.10/0.94  --clausifier_options                    --mode clausify
% 1.10/0.94  --stdin                                 false
% 1.10/0.94  --stats_out                             all
% 1.10/0.94  
% 1.10/0.94  ------ General Options
% 1.10/0.94  
% 1.10/0.94  --fof                                   false
% 1.10/0.94  --time_out_real                         305.
% 1.10/0.94  --time_out_virtual                      -1.
% 1.10/0.94  --symbol_type_check                     false
% 1.10/0.94  --clausify_out                          false
% 1.10/0.94  --sig_cnt_out                           false
% 1.10/0.94  --trig_cnt_out                          false
% 1.10/0.94  --trig_cnt_out_tolerance                1.
% 1.10/0.94  --trig_cnt_out_sk_spl                   false
% 1.10/0.94  --abstr_cl_out                          false
% 1.10/0.94  
% 1.10/0.94  ------ Global Options
% 1.10/0.94  
% 1.10/0.94  --schedule                              default
% 1.10/0.94  --add_important_lit                     false
% 1.10/0.94  --prop_solver_per_cl                    1000
% 1.10/0.94  --min_unsat_core                        false
% 1.10/0.94  --soft_assumptions                      false
% 1.10/0.94  --soft_lemma_size                       3
% 1.10/0.94  --prop_impl_unit_size                   0
% 1.10/0.94  --prop_impl_unit                        []
% 1.10/0.94  --share_sel_clauses                     true
% 1.10/0.94  --reset_solvers                         false
% 1.10/0.94  --bc_imp_inh                            [conj_cone]
% 1.10/0.94  --conj_cone_tolerance                   3.
% 1.10/0.94  --extra_neg_conj                        none
% 1.10/0.94  --large_theory_mode                     true
% 1.10/0.94  --prolific_symb_bound                   200
% 1.10/0.94  --lt_threshold                          2000
% 1.10/0.94  --clause_weak_htbl                      true
% 1.10/0.94  --gc_record_bc_elim                     false
% 1.10/0.94  
% 1.10/0.94  ------ Preprocessing Options
% 1.10/0.94  
% 1.10/0.94  --preprocessing_flag                    true
% 1.10/0.94  --time_out_prep_mult                    0.1
% 1.10/0.94  --splitting_mode                        input
% 1.10/0.94  --splitting_grd                         true
% 1.10/0.94  --splitting_cvd                         false
% 1.10/0.94  --splitting_cvd_svl                     false
% 1.10/0.94  --splitting_nvd                         32
% 1.10/0.94  --sub_typing                            true
% 1.10/0.94  --prep_gs_sim                           true
% 1.10/0.94  --prep_unflatten                        true
% 1.10/0.94  --prep_res_sim                          true
% 1.10/0.94  --prep_upred                            true
% 1.10/0.94  --prep_sem_filter                       exhaustive
% 1.10/0.94  --prep_sem_filter_out                   false
% 1.10/0.94  --pred_elim                             true
% 1.10/0.94  --res_sim_input                         true
% 1.10/0.94  --eq_ax_congr_red                       true
% 1.10/0.94  --pure_diseq_elim                       true
% 1.10/0.94  --brand_transform                       false
% 1.10/0.94  --non_eq_to_eq                          false
% 1.10/0.94  --prep_def_merge                        true
% 1.10/0.94  --prep_def_merge_prop_impl              false
% 1.10/0.94  --prep_def_merge_mbd                    true
% 1.10/0.94  --prep_def_merge_tr_red                 false
% 1.10/0.94  --prep_def_merge_tr_cl                  false
% 1.10/0.94  --smt_preprocessing                     true
% 1.10/0.94  --smt_ac_axioms                         fast
% 1.10/0.94  --preprocessed_out                      false
% 1.10/0.94  --preprocessed_stats                    false
% 1.10/0.94  
% 1.10/0.94  ------ Abstraction refinement Options
% 1.10/0.94  
% 1.10/0.94  --abstr_ref                             []
% 1.10/0.94  --abstr_ref_prep                        false
% 1.10/0.94  --abstr_ref_until_sat                   false
% 1.10/0.94  --abstr_ref_sig_restrict                funpre
% 1.10/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 1.10/0.94  --abstr_ref_under                       []
% 1.10/0.94  
% 1.10/0.94  ------ SAT Options
% 1.10/0.94  
% 1.10/0.94  --sat_mode                              false
% 1.10/0.94  --sat_fm_restart_options                ""
% 1.10/0.94  --sat_gr_def                            false
% 1.10/0.94  --sat_epr_types                         true
% 1.10/0.94  --sat_non_cyclic_types                  false
% 1.10/0.94  --sat_finite_models                     false
% 1.10/0.94  --sat_fm_lemmas                         false
% 1.10/0.94  --sat_fm_prep                           false
% 1.10/0.94  --sat_fm_uc_incr                        true
% 1.10/0.94  --sat_out_model                         small
% 1.10/0.94  --sat_out_clauses                       false
% 1.10/0.94  
% 1.10/0.94  ------ QBF Options
% 1.10/0.94  
% 1.10/0.94  --qbf_mode                              false
% 1.10/0.94  --qbf_elim_univ                         false
% 1.10/0.94  --qbf_dom_inst                          none
% 1.10/0.94  --qbf_dom_pre_inst                      false
% 1.10/0.94  --qbf_sk_in                             false
% 1.10/0.94  --qbf_pred_elim                         true
% 1.10/0.94  --qbf_split                             512
% 1.10/0.94  
% 1.10/0.94  ------ BMC1 Options
% 1.10/0.94  
% 1.10/0.94  --bmc1_incremental                      false
% 1.10/0.94  --bmc1_axioms                           reachable_all
% 1.10/0.94  --bmc1_min_bound                        0
% 1.10/0.94  --bmc1_max_bound                        -1
% 1.10/0.94  --bmc1_max_bound_default                -1
% 1.10/0.94  --bmc1_symbol_reachability              true
% 1.10/0.94  --bmc1_property_lemmas                  false
% 1.10/0.94  --bmc1_k_induction                      false
% 1.10/0.94  --bmc1_non_equiv_states                 false
% 1.10/0.94  --bmc1_deadlock                         false
% 1.10/0.94  --bmc1_ucm                              false
% 1.10/0.94  --bmc1_add_unsat_core                   none
% 1.10/0.94  --bmc1_unsat_core_children              false
% 1.10/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 1.10/0.94  --bmc1_out_stat                         full
% 1.10/0.94  --bmc1_ground_init                      false
% 1.10/0.94  --bmc1_pre_inst_next_state              false
% 1.10/0.94  --bmc1_pre_inst_state                   false
% 1.10/0.94  --bmc1_pre_inst_reach_state             false
% 1.10/0.94  --bmc1_out_unsat_core                   false
% 1.10/0.94  --bmc1_aig_witness_out                  false
% 1.10/0.94  --bmc1_verbose                          false
% 1.10/0.94  --bmc1_dump_clauses_tptp                false
% 1.10/0.94  --bmc1_dump_unsat_core_tptp             false
% 1.10/0.94  --bmc1_dump_file                        -
% 1.10/0.94  --bmc1_ucm_expand_uc_limit              128
% 1.10/0.94  --bmc1_ucm_n_expand_iterations          6
% 1.10/0.94  --bmc1_ucm_extend_mode                  1
% 1.10/0.94  --bmc1_ucm_init_mode                    2
% 1.10/0.94  --bmc1_ucm_cone_mode                    none
% 1.10/0.94  --bmc1_ucm_reduced_relation_type        0
% 1.10/0.94  --bmc1_ucm_relax_model                  4
% 1.10/0.94  --bmc1_ucm_full_tr_after_sat            true
% 1.10/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 1.10/0.94  --bmc1_ucm_layered_model                none
% 1.10/0.94  --bmc1_ucm_max_lemma_size               10
% 1.10/0.94  
% 1.10/0.94  ------ AIG Options
% 1.10/0.94  
% 1.10/0.94  --aig_mode                              false
% 1.10/0.94  
% 1.10/0.94  ------ Instantiation Options
% 1.10/0.94  
% 1.10/0.94  --instantiation_flag                    true
% 1.10/0.94  --inst_sos_flag                         false
% 1.10/0.94  --inst_sos_phase                        true
% 1.10/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.10/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.10/0.94  --inst_lit_sel_side                     none
% 1.10/0.94  --inst_solver_per_active                1400
% 1.10/0.94  --inst_solver_calls_frac                1.
% 1.10/0.94  --inst_passive_queue_type               priority_queues
% 1.10/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.10/0.94  --inst_passive_queues_freq              [25;2]
% 1.10/0.94  --inst_dismatching                      true
% 1.10/0.94  --inst_eager_unprocessed_to_passive     true
% 1.10/0.94  --inst_prop_sim_given                   true
% 1.10/0.94  --inst_prop_sim_new                     false
% 1.10/0.94  --inst_subs_new                         false
% 1.10/0.94  --inst_eq_res_simp                      false
% 1.10/0.94  --inst_subs_given                       false
% 1.10/0.94  --inst_orphan_elimination               true
% 1.10/0.94  --inst_learning_loop_flag               true
% 1.10/0.94  --inst_learning_start                   3000
% 1.10/0.94  --inst_learning_factor                  2
% 1.10/0.94  --inst_start_prop_sim_after_learn       3
% 1.10/0.94  --inst_sel_renew                        solver
% 1.10/0.94  --inst_lit_activity_flag                true
% 1.10/0.94  --inst_restr_to_given                   false
% 1.10/0.94  --inst_activity_threshold               500
% 1.10/0.94  --inst_out_proof                        true
% 1.10/0.94  
% 1.10/0.94  ------ Resolution Options
% 1.10/0.94  
% 1.10/0.94  --resolution_flag                       false
% 1.10/0.94  --res_lit_sel                           adaptive
% 1.10/0.94  --res_lit_sel_side                      none
% 1.10/0.94  --res_ordering                          kbo
% 1.10/0.94  --res_to_prop_solver                    active
% 1.10/0.94  --res_prop_simpl_new                    false
% 1.10/0.94  --res_prop_simpl_given                  true
% 1.10/0.94  --res_passive_queue_type                priority_queues
% 1.10/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.10/0.94  --res_passive_queues_freq               [15;5]
% 1.10/0.94  --res_forward_subs                      full
% 1.10/0.94  --res_backward_subs                     full
% 1.10/0.94  --res_forward_subs_resolution           true
% 1.10/0.94  --res_backward_subs_resolution          true
% 1.10/0.94  --res_orphan_elimination                true
% 1.10/0.94  --res_time_limit                        2.
% 1.10/0.94  --res_out_proof                         true
% 1.10/0.94  
% 1.10/0.94  ------ Superposition Options
% 1.10/0.94  
% 1.10/0.94  --superposition_flag                    true
% 1.10/0.94  --sup_passive_queue_type                priority_queues
% 1.10/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.10/0.94  --sup_passive_queues_freq               [8;1;4]
% 1.10/0.94  --demod_completeness_check              fast
% 1.10/0.94  --demod_use_ground                      true
% 1.10/0.94  --sup_to_prop_solver                    passive
% 1.10/0.94  --sup_prop_simpl_new                    true
% 1.10/0.94  --sup_prop_simpl_given                  true
% 1.10/0.94  --sup_fun_splitting                     false
% 1.10/0.94  --sup_smt_interval                      50000
% 1.10/0.94  
% 1.10/0.94  ------ Superposition Simplification Setup
% 1.10/0.94  
% 1.10/0.94  --sup_indices_passive                   []
% 1.10/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.10/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 1.10/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/0.94  --sup_full_bw                           [BwDemod]
% 1.10/0.94  --sup_immed_triv                        [TrivRules]
% 1.10/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.10/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/0.94  --sup_immed_bw_main                     []
% 1.10/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 1.10/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.10/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.10/0.94  
% 1.10/0.94  ------ Combination Options
% 1.10/0.94  
% 1.10/0.94  --comb_res_mult                         3
% 1.10/0.94  --comb_sup_mult                         2
% 1.10/0.94  --comb_inst_mult                        10
% 1.10/0.94  
% 1.10/0.94  ------ Debug Options
% 1.10/0.94  
% 1.10/0.94  --dbg_backtrace                         false
% 1.10/0.94  --dbg_dump_prop_clauses                 false
% 1.10/0.94  --dbg_dump_prop_clauses_file            -
% 1.10/0.94  --dbg_out_stat                          false
% 1.10/0.94  
% 1.10/0.94  
% 1.10/0.94  
% 1.10/0.94  
% 1.10/0.94  ------ Proving...
% 1.10/0.94  
% 1.10/0.94  
% 1.10/0.94  % SZS status Theorem for theBenchmark.p
% 1.10/0.94  
% 1.10/0.94   Resolution empty clause
% 1.10/0.94  
% 1.10/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 1.10/0.94  
% 1.10/0.94  fof(f1,axiom,(
% 1.10/0.94    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.10/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/0.94  
% 1.10/0.94  fof(f19,plain,(
% 1.10/0.94    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.10/0.94    inference(cnf_transformation,[],[f1])).
% 1.10/0.94  
% 1.10/0.94  fof(f2,axiom,(
% 1.10/0.94    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.10/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/0.94  
% 1.10/0.94  fof(f20,plain,(
% 1.10/0.94    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.10/0.94    inference(cnf_transformation,[],[f2])).
% 1.10/0.94  
% 1.10/0.94  fof(f29,plain,(
% 1.10/0.94    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.10/0.94    inference(definition_unfolding,[],[f19,f20])).
% 1.10/0.94  
% 1.10/0.94  fof(f3,axiom,(
% 1.10/0.94    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.10/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/0.94  
% 1.10/0.94  fof(f21,plain,(
% 1.10/0.94    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.10/0.94    inference(cnf_transformation,[],[f3])).
% 1.10/0.94  
% 1.10/0.94  fof(f5,axiom,(
% 1.10/0.94    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.10/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/0.94  
% 1.10/0.94  fof(f12,plain,(
% 1.10/0.94    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.10/0.94    inference(ennf_transformation,[],[f5])).
% 1.10/0.94  
% 1.10/0.94  fof(f13,plain,(
% 1.10/0.94    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.10/0.94    inference(flattening,[],[f12])).
% 1.10/0.94  
% 1.10/0.94  fof(f23,plain,(
% 1.10/0.94    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.10/0.94    inference(cnf_transformation,[],[f13])).
% 1.10/0.94  
% 1.10/0.94  fof(f7,axiom,(
% 1.10/0.94    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.10/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/0.94  
% 1.10/0.94  fof(f26,plain,(
% 1.10/0.94    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.10/0.94    inference(cnf_transformation,[],[f7])).
% 1.10/0.94  
% 1.10/0.94  fof(f8,axiom,(
% 1.10/0.94    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 1.10/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/0.94  
% 1.10/0.94  fof(f15,plain,(
% 1.10/0.94    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.10/0.94    inference(ennf_transformation,[],[f8])).
% 1.10/0.94  
% 1.10/0.94  fof(f27,plain,(
% 1.10/0.94    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.10/0.94    inference(cnf_transformation,[],[f15])).
% 1.10/0.94  
% 1.10/0.94  fof(f4,axiom,(
% 1.10/0.94    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 1.10/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/0.94  
% 1.10/0.94  fof(f11,plain,(
% 1.10/0.94    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 1.10/0.94    inference(ennf_transformation,[],[f4])).
% 1.10/0.94  
% 1.10/0.94  fof(f22,plain,(
% 1.10/0.94    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.10/0.94    inference(cnf_transformation,[],[f11])).
% 1.10/0.94  
% 1.10/0.94  fof(f6,axiom,(
% 1.10/0.94    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 1.10/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/0.94  
% 1.10/0.94  fof(f14,plain,(
% 1.10/0.94    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.10/0.94    inference(ennf_transformation,[],[f6])).
% 1.10/0.94  
% 1.10/0.94  fof(f24,plain,(
% 1.10/0.94    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 1.10/0.94    inference(cnf_transformation,[],[f14])).
% 1.10/0.94  
% 1.10/0.94  fof(f30,plain,(
% 1.10/0.94    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 1.10/0.94    inference(definition_unfolding,[],[f24,f20])).
% 1.10/0.94  
% 1.10/0.94  fof(f25,plain,(
% 1.10/0.94    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.10/0.94    inference(cnf_transformation,[],[f7])).
% 1.10/0.94  
% 1.10/0.94  fof(f9,conjecture,(
% 1.10/0.94    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 1.10/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.10/0.94  
% 1.10/0.94  fof(f10,negated_conjecture,(
% 1.10/0.94    ~! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 1.10/0.94    inference(negated_conjecture,[],[f9])).
% 1.10/0.94  
% 1.10/0.94  fof(f16,plain,(
% 1.10/0.94    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 1.10/0.94    inference(ennf_transformation,[],[f10])).
% 1.10/0.94  
% 1.10/0.94  fof(f17,plain,(
% 1.10/0.94    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) => k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 1.10/0.94    introduced(choice_axiom,[])).
% 1.10/0.94  
% 1.10/0.94  fof(f18,plain,(
% 1.10/0.94    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 1.10/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 1.10/0.94  
% 1.10/0.94  fof(f28,plain,(
% 1.10/0.94    k6_relat_1(k3_xboole_0(sK0,sK1)) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 1.10/0.94    inference(cnf_transformation,[],[f18])).
% 1.10/0.94  
% 1.10/0.94  fof(f31,plain,(
% 1.10/0.94    k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0))),
% 1.10/0.94    inference(definition_unfolding,[],[f28,f20])).
% 1.10/0.94  
% 1.10/0.94  cnf(c_0,plain,
% 1.10/0.94      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 1.10/0.94      inference(cnf_transformation,[],[f29]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_249,plain,
% 1.10/0.94      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 1.10/0.94      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_1,plain,
% 1.10/0.94      ( v1_relat_1(k6_relat_1(X0)) ),
% 1.10/0.94      inference(cnf_transformation,[],[f21]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_3,plain,
% 1.10/0.94      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 1.10/0.94      | ~ v1_relat_1(X0)
% 1.10/0.94      | k8_relat_1(X1,X0) = X0 ),
% 1.10/0.94      inference(cnf_transformation,[],[f23]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_115,plain,
% 1.10/0.94      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 1.10/0.94      | k8_relat_1(X1,X0) = X0
% 1.10/0.94      | k6_relat_1(X2) != X0 ),
% 1.10/0.94      inference(resolution_lifted,[status(thm)],[c_1,c_3]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_116,plain,
% 1.10/0.94      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
% 1.10/0.94      | k8_relat_1(X1,k6_relat_1(X0)) = k6_relat_1(X0) ),
% 1.10/0.94      inference(unflattening,[status(thm)],[c_115]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_248,plain,
% 1.10/0.94      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
% 1.10/0.94      | r1_tarski(k2_relat_1(k6_relat_1(X1)),X0) != iProver_top ),
% 1.10/0.94      inference(predicate_to_equality,[status(thm)],[c_116]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_5,plain,
% 1.10/0.94      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 1.10/0.94      inference(cnf_transformation,[],[f26]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_264,plain,
% 1.10/0.94      ( k8_relat_1(X0,k6_relat_1(X1)) = k6_relat_1(X1)
% 1.10/0.94      | r1_tarski(X1,X0) != iProver_top ),
% 1.10/0.94      inference(demodulation,[status(thm)],[c_248,c_5]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_480,plain,
% 1.10/0.94      ( k8_relat_1(X0,k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
% 1.10/0.94      inference(superposition,[status(thm)],[c_249,c_264]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_7,plain,
% 1.10/0.94      ( ~ v1_relat_1(X0) | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 1.10/0.94      inference(cnf_transformation,[],[f27]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_103,plain,
% 1.10/0.94      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 1.10/0.94      | k6_relat_1(X2) != X1 ),
% 1.10/0.94      inference(resolution_lifted,[status(thm)],[c_1,c_7]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_104,plain,
% 1.10/0.94      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 1.10/0.94      inference(unflattening,[status(thm)],[c_103]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_2,plain,
% 1.10/0.94      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0) ),
% 1.10/0.94      inference(cnf_transformation,[],[f22]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_127,plain,
% 1.10/0.94      ( k5_relat_1(X0,k6_relat_1(X1)) = k8_relat_1(X1,X0)
% 1.10/0.94      | k6_relat_1(X2) != X0 ),
% 1.10/0.94      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_128,plain,
% 1.10/0.94      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k8_relat_1(X1,k6_relat_1(X0)) ),
% 1.10/0.94      inference(unflattening,[status(thm)],[c_127]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_258,plain,
% 1.10/0.94      ( k7_relat_1(k6_relat_1(X0),X1) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 1.10/0.94      inference(light_normalisation,[status(thm)],[c_104,c_128]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_4,plain,
% 1.10/0.94      ( ~ v1_relat_1(X0)
% 1.10/0.94      | k7_relat_1(X0,k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1))) = k7_relat_1(X0,X1) ),
% 1.10/0.94      inference(cnf_transformation,[],[f30]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_109,plain,
% 1.10/0.94      ( k7_relat_1(X0,k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1))) = k7_relat_1(X0,X1)
% 1.10/0.94      | k6_relat_1(X2) != X0 ),
% 1.10/0.94      inference(resolution_lifted,[status(thm)],[c_1,c_4]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_110,plain,
% 1.10/0.94      ( k7_relat_1(k6_relat_1(X0),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 1.10/0.94      inference(unflattening,[status(thm)],[c_109]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_6,plain,
% 1.10/0.94      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 1.10/0.94      inference(cnf_transformation,[],[f25]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_269,plain,
% 1.10/0.94      ( k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 1.10/0.94      inference(light_normalisation,[status(thm)],[c_110,c_6,c_258]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_442,plain,
% 1.10/0.94      ( k8_relat_1(X0,k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 1.10/0.94      inference(superposition,[status(thm)],[c_258,c_269]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_481,plain,
% 1.10/0.94      ( k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k8_relat_1(X0,k6_relat_1(X1)) ),
% 1.10/0.94      inference(light_normalisation,[status(thm)],[c_480,c_442]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_8,negated_conjecture,
% 1.10/0.94      ( k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) ),
% 1.10/0.94      inference(cnf_transformation,[],[f31]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_261,plain,
% 1.10/0.94      ( k6_relat_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
% 1.10/0.94      inference(demodulation,[status(thm)],[c_8,c_128]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_484,plain,
% 1.10/0.94      ( k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
% 1.10/0.94      inference(demodulation,[status(thm)],[c_481,c_261]) ).
% 1.10/0.94  
% 1.10/0.94  cnf(c_488,plain,
% 1.10/0.94      ( $false ),
% 1.10/0.94      inference(equality_resolution_simp,[status(thm)],[c_484]) ).
% 1.10/0.94  
% 1.10/0.94  
% 1.10/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 1.10/0.94  
% 1.10/0.94  ------                               Statistics
% 1.10/0.94  
% 1.10/0.94  ------ General
% 1.10/0.94  
% 1.10/0.94  abstr_ref_over_cycles:                  0
% 1.10/0.94  abstr_ref_under_cycles:                 0
% 1.10/0.94  gc_basic_clause_elim:                   0
% 1.10/0.94  forced_gc_time:                         0
% 1.10/0.94  parsing_time:                           0.008
% 1.10/0.94  unif_index_cands_time:                  0.
% 1.10/0.94  unif_index_add_time:                    0.
% 1.10/0.94  orderings_time:                         0.
% 1.10/0.94  out_proof_time:                         0.01
% 1.10/0.94  total_time:                             0.058
% 1.10/0.94  num_of_symbols:                         42
% 1.10/0.94  num_of_terms:                           813
% 1.10/0.94  
% 1.10/0.94  ------ Preprocessing
% 1.10/0.94  
% 1.10/0.94  num_of_splits:                          0
% 1.10/0.94  num_of_split_atoms:                     0
% 1.10/0.94  num_of_reused_defs:                     0
% 1.10/0.94  num_eq_ax_congr_red:                    8
% 1.10/0.94  num_of_sem_filtered_clauses:            1
% 1.10/0.94  num_of_subtypes:                        0
% 1.10/0.94  monotx_restored_types:                  0
% 1.10/0.94  sat_num_of_epr_types:                   0
% 1.10/0.94  sat_num_of_non_cyclic_types:            0
% 1.10/0.94  sat_guarded_non_collapsed_types:        0
% 1.10/0.94  num_pure_diseq_elim:                    0
% 1.10/0.94  simp_replaced_by:                       0
% 1.10/0.94  res_preprocessed:                       54
% 1.10/0.94  prep_upred:                             0
% 1.10/0.94  prep_unflattend:                        7
% 1.10/0.94  smt_new_axioms:                         0
% 1.10/0.94  pred_elim_cands:                        1
% 1.10/0.94  pred_elim:                              1
% 1.10/0.94  pred_elim_cl:                           1
% 1.10/0.94  pred_elim_cycles:                       4
% 1.10/0.94  merged_defs:                            0
% 1.10/0.94  merged_defs_ncl:                        0
% 1.10/0.94  bin_hyper_res:                          0
% 1.10/0.94  prep_cycles:                            4
% 1.10/0.94  pred_elim_time:                         0.001
% 1.10/0.94  splitting_time:                         0.
% 1.10/0.94  sem_filter_time:                        0.
% 1.10/0.94  monotx_time:                            0.001
% 1.10/0.94  subtype_inf_time:                       0.
% 1.10/0.94  
% 1.10/0.94  ------ Problem properties
% 1.10/0.94  
% 1.10/0.94  clauses:                                8
% 1.10/0.94  conjectures:                            1
% 1.10/0.94  epr:                                    0
% 1.10/0.94  horn:                                   8
% 1.10/0.94  ground:                                 1
% 1.10/0.94  unary:                                  7
% 1.10/0.94  binary:                                 1
% 1.10/0.94  lits:                                   9
% 1.10/0.94  lits_eq:                                7
% 1.10/0.94  fd_pure:                                0
% 1.10/0.94  fd_pseudo:                              0
% 1.10/0.94  fd_cond:                                0
% 1.10/0.94  fd_pseudo_cond:                         0
% 1.10/0.94  ac_symbols:                             0
% 1.10/0.94  
% 1.10/0.94  ------ Propositional Solver
% 1.10/0.94  
% 1.10/0.94  prop_solver_calls:                      26
% 1.10/0.94  prop_fast_solver_calls:                 203
% 1.10/0.94  smt_solver_calls:                       0
% 1.10/0.94  smt_fast_solver_calls:                  0
% 1.10/0.94  prop_num_of_clauses:                    212
% 1.10/0.94  prop_preprocess_simplified:             1267
% 1.10/0.94  prop_fo_subsumed:                       0
% 1.10/0.94  prop_solver_time:                       0.
% 1.10/0.94  smt_solver_time:                        0.
% 1.10/0.94  smt_fast_solver_time:                   0.
% 1.10/0.94  prop_fast_solver_time:                  0.
% 1.10/0.94  prop_unsat_core_time:                   0.
% 1.10/0.94  
% 1.10/0.94  ------ QBF
% 1.10/0.94  
% 1.10/0.94  qbf_q_res:                              0
% 1.10/0.94  qbf_num_tautologies:                    0
% 1.10/0.94  qbf_prep_cycles:                        0
% 1.10/0.94  
% 1.10/0.94  ------ BMC1
% 1.10/0.94  
% 1.10/0.94  bmc1_current_bound:                     -1
% 1.10/0.94  bmc1_last_solved_bound:                 -1
% 1.10/0.94  bmc1_unsat_core_size:                   -1
% 1.10/0.94  bmc1_unsat_core_parents_size:           -1
% 1.10/0.94  bmc1_merge_next_fun:                    0
% 1.10/0.94  bmc1_unsat_core_clauses_time:           0.
% 1.10/0.94  
% 1.10/0.94  ------ Instantiation
% 1.10/0.94  
% 1.10/0.94  inst_num_of_clauses:                    98
% 1.10/0.94  inst_num_in_passive:                    37
% 1.10/0.94  inst_num_in_active:                     48
% 1.10/0.94  inst_num_in_unprocessed:                13
% 1.10/0.94  inst_num_of_loops:                      50
% 1.10/0.94  inst_num_of_learning_restarts:          0
% 1.10/0.94  inst_num_moves_active_passive:          0
% 1.10/0.94  inst_lit_activity:                      0
% 1.10/0.94  inst_lit_activity_moves:                0
% 1.10/0.94  inst_num_tautologies:                   0
% 1.10/0.94  inst_num_prop_implied:                  0
% 1.10/0.94  inst_num_existing_simplified:           0
% 1.10/0.94  inst_num_eq_res_simplified:             0
% 1.10/0.94  inst_num_child_elim:                    0
% 1.10/0.94  inst_num_of_dismatching_blockings:      3
% 1.10/0.94  inst_num_of_non_proper_insts:           42
% 1.10/0.94  inst_num_of_duplicates:                 0
% 1.10/0.94  inst_inst_num_from_inst_to_res:         0
% 1.10/0.94  inst_dismatching_checking_time:         0.
% 1.10/0.94  
% 1.10/0.94  ------ Resolution
% 1.10/0.94  
% 1.10/0.94  res_num_of_clauses:                     0
% 1.10/0.94  res_num_in_passive:                     0
% 1.10/0.94  res_num_in_active:                      0
% 1.10/0.94  res_num_of_loops:                       58
% 1.10/0.94  res_forward_subset_subsumed:            15
% 1.10/0.94  res_backward_subset_subsumed:           0
% 1.10/0.94  res_forward_subsumed:                   0
% 1.10/0.94  res_backward_subsumed:                  0
% 1.10/0.94  res_forward_subsumption_resolution:     0
% 1.10/0.94  res_backward_subsumption_resolution:    0
% 1.10/0.94  res_clause_to_clause_subsumption:       14
% 1.10/0.94  res_orphan_elimination:                 0
% 1.10/0.94  res_tautology_del:                      3
% 1.10/0.94  res_num_eq_res_simplified:              0
% 1.10/0.94  res_num_sel_changes:                    0
% 1.10/0.94  res_moves_from_active_to_pass:          0
% 1.10/0.94  
% 1.10/0.94  ------ Superposition
% 1.10/0.94  
% 1.10/0.94  sup_time_total:                         0.
% 1.10/0.94  sup_time_generating:                    0.
% 1.10/0.94  sup_time_sim_full:                      0.
% 1.10/0.94  sup_time_sim_immed:                     0.
% 1.10/0.94  
% 1.10/0.94  sup_num_of_clauses:                     8
% 1.10/0.94  sup_num_in_active:                      7
% 1.10/0.94  sup_num_in_passive:                     1
% 1.10/0.94  sup_num_of_loops:                       9
% 1.10/0.94  sup_fw_superposition:                   2
% 1.10/0.94  sup_bw_superposition:                   1
% 1.10/0.94  sup_immediate_simplified:               1
% 1.10/0.94  sup_given_eliminated:                   0
% 1.10/0.94  comparisons_done:                       0
% 1.10/0.94  comparisons_avoided:                    0
% 1.10/0.94  
% 1.10/0.94  ------ Simplifications
% 1.10/0.94  
% 1.10/0.94  
% 1.10/0.94  sim_fw_subset_subsumed:                 0
% 1.10/0.94  sim_bw_subset_subsumed:                 0
% 1.10/0.94  sim_fw_subsumed:                        0
% 1.10/0.94  sim_bw_subsumed:                        0
% 1.10/0.94  sim_fw_subsumption_res:                 0
% 1.10/0.94  sim_bw_subsumption_res:                 0
% 1.10/0.94  sim_tautology_del:                      0
% 1.10/0.94  sim_eq_tautology_del:                   0
% 1.10/0.94  sim_eq_res_simp:                        0
% 1.10/0.94  sim_fw_demodulated:                     2
% 1.10/0.94  sim_bw_demodulated:                     2
% 1.10/0.94  sim_light_normalised:                   3
% 1.10/0.94  sim_joinable_taut:                      0
% 1.10/0.94  sim_joinable_simp:                      0
% 1.10/0.94  sim_ac_normalised:                      0
% 1.10/0.94  sim_smt_subsumption:                    0
% 1.10/0.94  
%------------------------------------------------------------------------------
