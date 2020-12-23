%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:18 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 119 expanded)
%              Number of clauses        :   25 (  36 expanded)
%              Number of leaves         :    8 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :   88 ( 162 expanded)
%              Number of equality atoms :   69 ( 134 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f58,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) ),
    inference(definition_unfolding,[],[f47,f46])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_tarski(X1,X3) = k2_relat_1(X4)
          & k2_tarski(X0,X2) = k1_relat_1(X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_tarski(X1,X3) = k2_relat_1(X4)
        & k2_tarski(X0,X2) = k1_relat_1(X4) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_tarski(X1,X3) = k2_relat_1(X4)
        & k2_tarski(X0,X2) = k1_relat_1(X4) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(flattening,[],[f18])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_tarski(X0,X2) = k1_relat_1(X4)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X2)) = k1_relat_1(X4)
      | k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(definition_unfolding,[],[f60,f46,f46])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X2)) = k1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))))
      | ~ v1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ),
    inference(definition_unfolding,[],[f57,f46])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_tarski(X1,X3) = k2_relat_1(X4)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_xboole_0(k1_tarski(X1),k1_tarski(X3)) = k2_relat_1(X4)
      | k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(definition_unfolding,[],[f61,f46,f46])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_xboole_0(k1_tarski(X1),k1_tarski(X3)) = k2_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))))
      | ~ v1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))) ) ),
    inference(equality_resolution,[],[f74])).

fof(f15,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(negated_conjecture,[],[f15])).

fof(f20,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1)))
   => k2_tarski(sK2,sK3) != k3_relat_1(k1_tarski(k4_tarski(sK2,sK3))) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    k2_tarski(sK2,sK3) != k3_relat_1(k1_tarski(k4_tarski(sK2,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f33])).

fof(f62,plain,(
    k2_tarski(sK2,sK3) != k3_relat_1(k1_tarski(k4_tarski(sK2,sK3))) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k3_relat_1(k1_tarski(k4_tarski(sK2,sK3))) ),
    inference(definition_unfolding,[],[f62,f46])).

cnf(c_23,plain,
    ( v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_551,plain,
    ( v1_relat_1(k1_tarski(k4_tarski(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_552,plain,
    ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2140,plain,
    ( k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X0,X1))),k2_relat_1(k1_tarski(k4_tarski(X0,X1)))) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(superposition,[status(thm)],[c_551,c_552])).

cnf(c_1,plain,
    ( k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_25,plain,
    ( ~ v1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))))
    | k1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))) = k2_xboole_0(k1_tarski(X0),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_549,plain,
    ( k1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))) = k2_xboole_0(k1_tarski(X0),k1_tarski(X2))
    | v1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_923,plain,
    ( k1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X0,X1)))) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))
    | v1_relat_1(k1_tarski(k4_tarski(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_549])).

cnf(c_924,plain,
    ( k1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X0,X1)))) = k1_tarski(X0)
    | v1_relat_1(k1_tarski(k4_tarski(X0,X1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_923,c_1])).

cnf(c_925,plain,
    ( k1_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X0)
    | v1_relat_1(k1_tarski(k4_tarski(X0,X1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_924,c_1])).

cnf(c_33,plain,
    ( v1_relat_1(k1_tarski(k4_tarski(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2546,plain,
    ( k1_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_925,c_33])).

cnf(c_0,plain,
    ( k3_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_930,plain,
    ( k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_24,plain,
    ( ~ v1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))))
    | k2_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))) = k2_xboole_0(k1_tarski(X1),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_550,plain,
    ( k2_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))) = k2_xboole_0(k1_tarski(X1),k1_tarski(X3))
    | v1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1865,plain,
    ( k2_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X0,X1)))) = k2_xboole_0(k1_tarski(X1),k1_tarski(X1))
    | v1_relat_1(k3_tarski(k1_tarski(k1_tarski(k4_tarski(X0,X1))))) != iProver_top ),
    inference(superposition,[status(thm)],[c_930,c_550])).

cnf(c_1164,plain,
    ( k3_tarski(k1_tarski(k1_tarski(X0))) = k1_tarski(X0) ),
    inference(superposition,[status(thm)],[c_930,c_1])).

cnf(c_1873,plain,
    ( k2_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X1)
    | v1_relat_1(k1_tarski(k4_tarski(X0,X1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1865,c_1,c_1164])).

cnf(c_2847,plain,
    ( k2_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1873,c_33])).

cnf(c_3768,plain,
    ( k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(light_normalisation,[status(thm)],[c_2140,c_2546,c_2847])).

cnf(c_26,negated_conjecture,
    ( k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k3_relat_1(k1_tarski(k4_tarski(sK2,sK3))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3786,plain,
    ( k3_relat_1(k1_tarski(k4_tarski(sK2,sK3))) != k3_relat_1(k1_tarski(k4_tarski(sK2,sK3))) ),
    inference(demodulation,[status(thm)],[c_3768,c_26])).

cnf(c_3800,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3786])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n021.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 18:19:34 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.62/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/0.98  
% 2.62/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.62/0.98  
% 2.62/0.98  ------  iProver source info
% 2.62/0.98  
% 2.62/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.62/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.62/0.98  git: non_committed_changes: false
% 2.62/0.98  git: last_make_outside_of_git: false
% 2.62/0.98  
% 2.62/0.98  ------ 
% 2.62/0.98  
% 2.62/0.98  ------ Input Options
% 2.62/0.98  
% 2.62/0.98  --out_options                           all
% 2.62/0.98  --tptp_safe_out                         true
% 2.62/0.98  --problem_path                          ""
% 2.62/0.98  --include_path                          ""
% 2.62/0.98  --clausifier                            res/vclausify_rel
% 2.62/0.98  --clausifier_options                    --mode clausify
% 2.62/0.98  --stdin                                 false
% 2.62/0.98  --stats_out                             all
% 2.62/0.98  
% 2.62/0.98  ------ General Options
% 2.62/0.98  
% 2.62/0.98  --fof                                   false
% 2.62/0.98  --time_out_real                         305.
% 2.62/0.98  --time_out_virtual                      -1.
% 2.62/0.98  --symbol_type_check                     false
% 2.62/0.98  --clausify_out                          false
% 2.62/0.98  --sig_cnt_out                           false
% 2.62/0.98  --trig_cnt_out                          false
% 2.62/0.98  --trig_cnt_out_tolerance                1.
% 2.62/0.98  --trig_cnt_out_sk_spl                   false
% 2.62/0.98  --abstr_cl_out                          false
% 2.62/0.98  
% 2.62/0.98  ------ Global Options
% 2.62/0.98  
% 2.62/0.98  --schedule                              default
% 2.62/0.98  --add_important_lit                     false
% 2.62/0.98  --prop_solver_per_cl                    1000
% 2.62/0.98  --min_unsat_core                        false
% 2.62/0.98  --soft_assumptions                      false
% 2.62/0.98  --soft_lemma_size                       3
% 2.62/0.98  --prop_impl_unit_size                   0
% 2.62/0.98  --prop_impl_unit                        []
% 2.62/0.98  --share_sel_clauses                     true
% 2.62/0.98  --reset_solvers                         false
% 2.62/0.98  --bc_imp_inh                            [conj_cone]
% 2.62/0.98  --conj_cone_tolerance                   3.
% 2.62/0.98  --extra_neg_conj                        none
% 2.62/0.98  --large_theory_mode                     true
% 2.62/0.98  --prolific_symb_bound                   200
% 2.62/0.98  --lt_threshold                          2000
% 2.62/0.98  --clause_weak_htbl                      true
% 2.62/0.98  --gc_record_bc_elim                     false
% 2.62/0.98  
% 2.62/0.98  ------ Preprocessing Options
% 2.62/0.98  
% 2.62/0.98  --preprocessing_flag                    true
% 2.62/0.98  --time_out_prep_mult                    0.1
% 2.62/0.98  --splitting_mode                        input
% 2.62/0.98  --splitting_grd                         true
% 2.62/0.98  --splitting_cvd                         false
% 2.62/0.98  --splitting_cvd_svl                     false
% 2.62/0.98  --splitting_nvd                         32
% 2.62/0.98  --sub_typing                            true
% 2.62/0.98  --prep_gs_sim                           true
% 2.62/0.98  --prep_unflatten                        true
% 2.62/0.98  --prep_res_sim                          true
% 2.62/0.98  --prep_upred                            true
% 2.62/0.98  --prep_sem_filter                       exhaustive
% 2.62/0.98  --prep_sem_filter_out                   false
% 2.62/0.98  --pred_elim                             true
% 2.62/0.98  --res_sim_input                         true
% 2.62/0.98  --eq_ax_congr_red                       true
% 2.62/0.98  --pure_diseq_elim                       true
% 2.62/0.98  --brand_transform                       false
% 2.62/0.98  --non_eq_to_eq                          false
% 2.62/0.98  --prep_def_merge                        true
% 2.62/0.98  --prep_def_merge_prop_impl              false
% 2.62/0.98  --prep_def_merge_mbd                    true
% 2.62/0.98  --prep_def_merge_tr_red                 false
% 2.62/0.98  --prep_def_merge_tr_cl                  false
% 2.62/0.98  --smt_preprocessing                     true
% 2.62/0.98  --smt_ac_axioms                         fast
% 2.62/0.98  --preprocessed_out                      false
% 2.62/0.98  --preprocessed_stats                    false
% 2.62/0.98  
% 2.62/0.98  ------ Abstraction refinement Options
% 2.62/0.98  
% 2.62/0.98  --abstr_ref                             []
% 2.62/0.98  --abstr_ref_prep                        false
% 2.62/0.98  --abstr_ref_until_sat                   false
% 2.62/0.98  --abstr_ref_sig_restrict                funpre
% 2.62/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.62/0.98  --abstr_ref_under                       []
% 2.62/0.98  
% 2.62/0.98  ------ SAT Options
% 2.62/0.98  
% 2.62/0.98  --sat_mode                              false
% 2.62/0.98  --sat_fm_restart_options                ""
% 2.62/0.98  --sat_gr_def                            false
% 2.62/0.98  --sat_epr_types                         true
% 2.62/0.98  --sat_non_cyclic_types                  false
% 2.62/0.98  --sat_finite_models                     false
% 2.62/0.98  --sat_fm_lemmas                         false
% 2.62/0.98  --sat_fm_prep                           false
% 2.62/0.98  --sat_fm_uc_incr                        true
% 2.62/0.98  --sat_out_model                         small
% 2.62/0.98  --sat_out_clauses                       false
% 2.62/0.98  
% 2.62/0.98  ------ QBF Options
% 2.62/0.98  
% 2.62/0.98  --qbf_mode                              false
% 2.62/0.98  --qbf_elim_univ                         false
% 2.62/0.98  --qbf_dom_inst                          none
% 2.62/0.98  --qbf_dom_pre_inst                      false
% 2.62/0.98  --qbf_sk_in                             false
% 2.62/0.98  --qbf_pred_elim                         true
% 2.62/0.98  --qbf_split                             512
% 2.62/0.98  
% 2.62/0.98  ------ BMC1 Options
% 2.62/0.98  
% 2.62/0.98  --bmc1_incremental                      false
% 2.62/0.98  --bmc1_axioms                           reachable_all
% 2.62/0.98  --bmc1_min_bound                        0
% 2.62/0.98  --bmc1_max_bound                        -1
% 2.62/0.98  --bmc1_max_bound_default                -1
% 2.62/0.98  --bmc1_symbol_reachability              true
% 2.62/0.98  --bmc1_property_lemmas                  false
% 2.62/0.98  --bmc1_k_induction                      false
% 2.62/0.98  --bmc1_non_equiv_states                 false
% 2.62/0.98  --bmc1_deadlock                         false
% 2.62/0.98  --bmc1_ucm                              false
% 2.62/0.98  --bmc1_add_unsat_core                   none
% 2.62/0.98  --bmc1_unsat_core_children              false
% 2.62/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.62/0.98  --bmc1_out_stat                         full
% 2.62/0.98  --bmc1_ground_init                      false
% 2.62/0.98  --bmc1_pre_inst_next_state              false
% 2.62/0.98  --bmc1_pre_inst_state                   false
% 2.62/0.98  --bmc1_pre_inst_reach_state             false
% 2.62/0.98  --bmc1_out_unsat_core                   false
% 2.62/0.98  --bmc1_aig_witness_out                  false
% 2.62/0.98  --bmc1_verbose                          false
% 2.62/0.98  --bmc1_dump_clauses_tptp                false
% 2.62/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.62/0.98  --bmc1_dump_file                        -
% 2.62/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.62/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.62/0.98  --bmc1_ucm_extend_mode                  1
% 2.62/0.98  --bmc1_ucm_init_mode                    2
% 2.62/0.98  --bmc1_ucm_cone_mode                    none
% 2.62/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.62/0.98  --bmc1_ucm_relax_model                  4
% 2.62/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.62/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.62/0.98  --bmc1_ucm_layered_model                none
% 2.62/0.98  --bmc1_ucm_max_lemma_size               10
% 2.62/0.98  
% 2.62/0.98  ------ AIG Options
% 2.62/0.98  
% 2.62/0.98  --aig_mode                              false
% 2.62/0.98  
% 2.62/0.98  ------ Instantiation Options
% 2.62/0.98  
% 2.62/0.98  --instantiation_flag                    true
% 2.62/0.98  --inst_sos_flag                         false
% 2.62/0.98  --inst_sos_phase                        true
% 2.62/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.62/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.62/0.98  --inst_lit_sel_side                     num_symb
% 2.62/0.98  --inst_solver_per_active                1400
% 2.62/0.98  --inst_solver_calls_frac                1.
% 2.62/0.98  --inst_passive_queue_type               priority_queues
% 2.62/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.62/0.98  --inst_passive_queues_freq              [25;2]
% 2.62/0.98  --inst_dismatching                      true
% 2.62/0.98  --inst_eager_unprocessed_to_passive     true
% 2.62/0.98  --inst_prop_sim_given                   true
% 2.62/0.98  --inst_prop_sim_new                     false
% 2.62/0.98  --inst_subs_new                         false
% 2.62/0.98  --inst_eq_res_simp                      false
% 2.62/0.98  --inst_subs_given                       false
% 2.62/0.98  --inst_orphan_elimination               true
% 2.62/0.98  --inst_learning_loop_flag               true
% 2.62/0.98  --inst_learning_start                   3000
% 2.62/0.98  --inst_learning_factor                  2
% 2.62/0.98  --inst_start_prop_sim_after_learn       3
% 2.62/0.98  --inst_sel_renew                        solver
% 2.62/0.98  --inst_lit_activity_flag                true
% 2.62/0.98  --inst_restr_to_given                   false
% 2.62/0.98  --inst_activity_threshold               500
% 2.62/0.98  --inst_out_proof                        true
% 2.62/0.98  
% 2.62/0.98  ------ Resolution Options
% 2.62/0.98  
% 2.62/0.98  --resolution_flag                       true
% 2.62/0.98  --res_lit_sel                           adaptive
% 2.62/0.98  --res_lit_sel_side                      none
% 2.62/0.98  --res_ordering                          kbo
% 2.62/0.98  --res_to_prop_solver                    active
% 2.62/0.98  --res_prop_simpl_new                    false
% 2.62/0.98  --res_prop_simpl_given                  true
% 2.62/0.98  --res_passive_queue_type                priority_queues
% 2.62/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.62/0.98  --res_passive_queues_freq               [15;5]
% 2.62/0.98  --res_forward_subs                      full
% 2.62/0.98  --res_backward_subs                     full
% 2.62/0.98  --res_forward_subs_resolution           true
% 2.62/0.98  --res_backward_subs_resolution          true
% 2.62/0.98  --res_orphan_elimination                true
% 2.62/0.98  --res_time_limit                        2.
% 2.62/0.98  --res_out_proof                         true
% 2.62/0.98  
% 2.62/0.98  ------ Superposition Options
% 2.62/0.98  
% 2.62/0.98  --superposition_flag                    true
% 2.62/0.98  --sup_passive_queue_type                priority_queues
% 2.62/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.62/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.62/0.98  --demod_completeness_check              fast
% 2.62/0.98  --demod_use_ground                      true
% 2.62/0.98  --sup_to_prop_solver                    passive
% 2.62/0.98  --sup_prop_simpl_new                    true
% 2.62/0.98  --sup_prop_simpl_given                  true
% 2.62/0.98  --sup_fun_splitting                     false
% 2.62/0.98  --sup_smt_interval                      50000
% 2.62/0.98  
% 2.62/0.98  ------ Superposition Simplification Setup
% 2.62/0.98  
% 2.62/0.98  --sup_indices_passive                   []
% 2.62/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.62/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.98  --sup_full_bw                           [BwDemod]
% 2.62/0.98  --sup_immed_triv                        [TrivRules]
% 2.62/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.62/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.98  --sup_immed_bw_main                     []
% 2.62/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.62/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.98  
% 2.62/0.98  ------ Combination Options
% 2.62/0.98  
% 2.62/0.98  --comb_res_mult                         3
% 2.62/0.98  --comb_sup_mult                         2
% 2.62/0.98  --comb_inst_mult                        10
% 2.62/0.98  
% 2.62/0.98  ------ Debug Options
% 2.62/0.98  
% 2.62/0.98  --dbg_backtrace                         false
% 2.62/0.98  --dbg_dump_prop_clauses                 false
% 2.62/0.98  --dbg_dump_prop_clauses_file            -
% 2.62/0.98  --dbg_out_stat                          false
% 2.62/0.98  ------ Parsing...
% 2.62/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.62/0.98  
% 2.62/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.62/0.98  
% 2.62/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.62/0.98  
% 2.62/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.62/0.98  ------ Proving...
% 2.62/0.98  ------ Problem Properties 
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  clauses                                 27
% 2.62/0.98  conjectures                             1
% 2.62/0.98  EPR                                     0
% 2.62/0.98  Horn                                    22
% 2.62/0.98  unary                                   14
% 2.62/0.98  binary                                  6
% 2.62/0.98  lits                                    48
% 2.62/0.98  lits eq                                 29
% 2.62/0.98  fd_pure                                 0
% 2.62/0.98  fd_pseudo                               0
% 2.62/0.98  fd_cond                                 0
% 2.62/0.98  fd_pseudo_cond                          7
% 2.62/0.98  AC symbols                              0
% 2.62/0.98  
% 2.62/0.98  ------ Schedule dynamic 5 is on 
% 2.62/0.98  
% 2.62/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  ------ 
% 2.62/0.98  Current options:
% 2.62/0.98  ------ 
% 2.62/0.98  
% 2.62/0.98  ------ Input Options
% 2.62/0.98  
% 2.62/0.98  --out_options                           all
% 2.62/0.98  --tptp_safe_out                         true
% 2.62/0.98  --problem_path                          ""
% 2.62/0.98  --include_path                          ""
% 2.62/0.98  --clausifier                            res/vclausify_rel
% 2.62/0.98  --clausifier_options                    --mode clausify
% 2.62/0.98  --stdin                                 false
% 2.62/0.98  --stats_out                             all
% 2.62/0.98  
% 2.62/0.98  ------ General Options
% 2.62/0.98  
% 2.62/0.98  --fof                                   false
% 2.62/0.98  --time_out_real                         305.
% 2.62/0.98  --time_out_virtual                      -1.
% 2.62/0.98  --symbol_type_check                     false
% 2.62/0.98  --clausify_out                          false
% 2.62/0.98  --sig_cnt_out                           false
% 2.62/0.98  --trig_cnt_out                          false
% 2.62/0.98  --trig_cnt_out_tolerance                1.
% 2.62/0.98  --trig_cnt_out_sk_spl                   false
% 2.62/0.98  --abstr_cl_out                          false
% 2.62/0.98  
% 2.62/0.98  ------ Global Options
% 2.62/0.98  
% 2.62/0.98  --schedule                              default
% 2.62/0.98  --add_important_lit                     false
% 2.62/0.98  --prop_solver_per_cl                    1000
% 2.62/0.98  --min_unsat_core                        false
% 2.62/0.98  --soft_assumptions                      false
% 2.62/0.98  --soft_lemma_size                       3
% 2.62/0.98  --prop_impl_unit_size                   0
% 2.62/0.98  --prop_impl_unit                        []
% 2.62/0.98  --share_sel_clauses                     true
% 2.62/0.98  --reset_solvers                         false
% 2.62/0.98  --bc_imp_inh                            [conj_cone]
% 2.62/0.98  --conj_cone_tolerance                   3.
% 2.62/0.98  --extra_neg_conj                        none
% 2.62/0.98  --large_theory_mode                     true
% 2.62/0.98  --prolific_symb_bound                   200
% 2.62/0.98  --lt_threshold                          2000
% 2.62/0.98  --clause_weak_htbl                      true
% 2.62/0.98  --gc_record_bc_elim                     false
% 2.62/0.98  
% 2.62/0.98  ------ Preprocessing Options
% 2.62/0.98  
% 2.62/0.98  --preprocessing_flag                    true
% 2.62/0.98  --time_out_prep_mult                    0.1
% 2.62/0.98  --splitting_mode                        input
% 2.62/0.98  --splitting_grd                         true
% 2.62/0.98  --splitting_cvd                         false
% 2.62/0.98  --splitting_cvd_svl                     false
% 2.62/0.98  --splitting_nvd                         32
% 2.62/0.98  --sub_typing                            true
% 2.62/0.98  --prep_gs_sim                           true
% 2.62/0.98  --prep_unflatten                        true
% 2.62/0.98  --prep_res_sim                          true
% 2.62/0.98  --prep_upred                            true
% 2.62/0.98  --prep_sem_filter                       exhaustive
% 2.62/0.98  --prep_sem_filter_out                   false
% 2.62/0.98  --pred_elim                             true
% 2.62/0.98  --res_sim_input                         true
% 2.62/0.98  --eq_ax_congr_red                       true
% 2.62/0.98  --pure_diseq_elim                       true
% 2.62/0.98  --brand_transform                       false
% 2.62/0.98  --non_eq_to_eq                          false
% 2.62/0.98  --prep_def_merge                        true
% 2.62/0.98  --prep_def_merge_prop_impl              false
% 2.62/0.98  --prep_def_merge_mbd                    true
% 2.62/0.98  --prep_def_merge_tr_red                 false
% 2.62/0.98  --prep_def_merge_tr_cl                  false
% 2.62/0.98  --smt_preprocessing                     true
% 2.62/0.98  --smt_ac_axioms                         fast
% 2.62/0.98  --preprocessed_out                      false
% 2.62/0.98  --preprocessed_stats                    false
% 2.62/0.98  
% 2.62/0.98  ------ Abstraction refinement Options
% 2.62/0.98  
% 2.62/0.98  --abstr_ref                             []
% 2.62/0.98  --abstr_ref_prep                        false
% 2.62/0.98  --abstr_ref_until_sat                   false
% 2.62/0.98  --abstr_ref_sig_restrict                funpre
% 2.62/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.62/0.98  --abstr_ref_under                       []
% 2.62/0.98  
% 2.62/0.98  ------ SAT Options
% 2.62/0.98  
% 2.62/0.98  --sat_mode                              false
% 2.62/0.98  --sat_fm_restart_options                ""
% 2.62/0.98  --sat_gr_def                            false
% 2.62/0.98  --sat_epr_types                         true
% 2.62/0.98  --sat_non_cyclic_types                  false
% 2.62/0.98  --sat_finite_models                     false
% 2.62/0.98  --sat_fm_lemmas                         false
% 2.62/0.98  --sat_fm_prep                           false
% 2.62/0.98  --sat_fm_uc_incr                        true
% 2.62/0.98  --sat_out_model                         small
% 2.62/0.98  --sat_out_clauses                       false
% 2.62/0.98  
% 2.62/0.98  ------ QBF Options
% 2.62/0.98  
% 2.62/0.98  --qbf_mode                              false
% 2.62/0.98  --qbf_elim_univ                         false
% 2.62/0.98  --qbf_dom_inst                          none
% 2.62/0.98  --qbf_dom_pre_inst                      false
% 2.62/0.98  --qbf_sk_in                             false
% 2.62/0.98  --qbf_pred_elim                         true
% 2.62/0.98  --qbf_split                             512
% 2.62/0.98  
% 2.62/0.98  ------ BMC1 Options
% 2.62/0.98  
% 2.62/0.98  --bmc1_incremental                      false
% 2.62/0.98  --bmc1_axioms                           reachable_all
% 2.62/0.98  --bmc1_min_bound                        0
% 2.62/0.98  --bmc1_max_bound                        -1
% 2.62/0.98  --bmc1_max_bound_default                -1
% 2.62/0.98  --bmc1_symbol_reachability              true
% 2.62/0.98  --bmc1_property_lemmas                  false
% 2.62/0.98  --bmc1_k_induction                      false
% 2.62/0.98  --bmc1_non_equiv_states                 false
% 2.62/0.98  --bmc1_deadlock                         false
% 2.62/0.98  --bmc1_ucm                              false
% 2.62/0.98  --bmc1_add_unsat_core                   none
% 2.62/0.98  --bmc1_unsat_core_children              false
% 2.62/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.62/0.98  --bmc1_out_stat                         full
% 2.62/0.98  --bmc1_ground_init                      false
% 2.62/0.98  --bmc1_pre_inst_next_state              false
% 2.62/0.98  --bmc1_pre_inst_state                   false
% 2.62/0.98  --bmc1_pre_inst_reach_state             false
% 2.62/0.98  --bmc1_out_unsat_core                   false
% 2.62/0.98  --bmc1_aig_witness_out                  false
% 2.62/0.98  --bmc1_verbose                          false
% 2.62/0.98  --bmc1_dump_clauses_tptp                false
% 2.62/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.62/0.98  --bmc1_dump_file                        -
% 2.62/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.62/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.62/0.98  --bmc1_ucm_extend_mode                  1
% 2.62/0.98  --bmc1_ucm_init_mode                    2
% 2.62/0.98  --bmc1_ucm_cone_mode                    none
% 2.62/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.62/0.98  --bmc1_ucm_relax_model                  4
% 2.62/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.62/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.62/0.98  --bmc1_ucm_layered_model                none
% 2.62/0.98  --bmc1_ucm_max_lemma_size               10
% 2.62/0.98  
% 2.62/0.98  ------ AIG Options
% 2.62/0.98  
% 2.62/0.98  --aig_mode                              false
% 2.62/0.98  
% 2.62/0.98  ------ Instantiation Options
% 2.62/0.98  
% 2.62/0.98  --instantiation_flag                    true
% 2.62/0.98  --inst_sos_flag                         false
% 2.62/0.98  --inst_sos_phase                        true
% 2.62/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.62/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.62/0.98  --inst_lit_sel_side                     none
% 2.62/0.98  --inst_solver_per_active                1400
% 2.62/0.98  --inst_solver_calls_frac                1.
% 2.62/0.98  --inst_passive_queue_type               priority_queues
% 2.62/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.62/0.98  --inst_passive_queues_freq              [25;2]
% 2.62/0.98  --inst_dismatching                      true
% 2.62/0.98  --inst_eager_unprocessed_to_passive     true
% 2.62/0.98  --inst_prop_sim_given                   true
% 2.62/0.98  --inst_prop_sim_new                     false
% 2.62/0.98  --inst_subs_new                         false
% 2.62/0.98  --inst_eq_res_simp                      false
% 2.62/0.98  --inst_subs_given                       false
% 2.62/0.98  --inst_orphan_elimination               true
% 2.62/0.98  --inst_learning_loop_flag               true
% 2.62/0.98  --inst_learning_start                   3000
% 2.62/0.98  --inst_learning_factor                  2
% 2.62/0.98  --inst_start_prop_sim_after_learn       3
% 2.62/0.98  --inst_sel_renew                        solver
% 2.62/0.98  --inst_lit_activity_flag                true
% 2.62/0.98  --inst_restr_to_given                   false
% 2.62/0.98  --inst_activity_threshold               500
% 2.62/0.98  --inst_out_proof                        true
% 2.62/0.98  
% 2.62/0.98  ------ Resolution Options
% 2.62/0.98  
% 2.62/0.98  --resolution_flag                       false
% 2.62/0.98  --res_lit_sel                           adaptive
% 2.62/0.98  --res_lit_sel_side                      none
% 2.62/0.98  --res_ordering                          kbo
% 2.62/0.98  --res_to_prop_solver                    active
% 2.62/0.98  --res_prop_simpl_new                    false
% 2.62/0.98  --res_prop_simpl_given                  true
% 2.62/0.98  --res_passive_queue_type                priority_queues
% 2.62/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.62/0.98  --res_passive_queues_freq               [15;5]
% 2.62/0.98  --res_forward_subs                      full
% 2.62/0.98  --res_backward_subs                     full
% 2.62/0.98  --res_forward_subs_resolution           true
% 2.62/0.98  --res_backward_subs_resolution          true
% 2.62/0.98  --res_orphan_elimination                true
% 2.62/0.98  --res_time_limit                        2.
% 2.62/0.98  --res_out_proof                         true
% 2.62/0.98  
% 2.62/0.98  ------ Superposition Options
% 2.62/0.98  
% 2.62/0.98  --superposition_flag                    true
% 2.62/0.98  --sup_passive_queue_type                priority_queues
% 2.62/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.62/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.62/0.98  --demod_completeness_check              fast
% 2.62/0.98  --demod_use_ground                      true
% 2.62/0.98  --sup_to_prop_solver                    passive
% 2.62/0.98  --sup_prop_simpl_new                    true
% 2.62/0.98  --sup_prop_simpl_given                  true
% 2.62/0.98  --sup_fun_splitting                     false
% 2.62/0.98  --sup_smt_interval                      50000
% 2.62/0.98  
% 2.62/0.98  ------ Superposition Simplification Setup
% 2.62/0.98  
% 2.62/0.98  --sup_indices_passive                   []
% 2.62/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.62/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.98  --sup_full_bw                           [BwDemod]
% 2.62/0.98  --sup_immed_triv                        [TrivRules]
% 2.62/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.62/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.98  --sup_immed_bw_main                     []
% 2.62/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.62/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.98  
% 2.62/0.98  ------ Combination Options
% 2.62/0.98  
% 2.62/0.98  --comb_res_mult                         3
% 2.62/0.98  --comb_sup_mult                         2
% 2.62/0.98  --comb_inst_mult                        10
% 2.62/0.98  
% 2.62/0.98  ------ Debug Options
% 2.62/0.98  
% 2.62/0.98  --dbg_backtrace                         false
% 2.62/0.98  --dbg_dump_prop_clauses                 false
% 2.62/0.98  --dbg_dump_prop_clauses_file            -
% 2.62/0.98  --dbg_out_stat                          false
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  ------ Proving...
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  % SZS status Theorem for theBenchmark.p
% 2.62/0.98  
% 2.62/0.98   Resolution empty clause
% 2.62/0.98  
% 2.62/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.62/0.98  
% 2.62/0.98  fof(f13,axiom,(
% 2.62/0.98    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 2.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.98  
% 2.62/0.98  fof(f59,plain,(
% 2.62/0.98    ( ! [X0,X1] : (v1_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 2.62/0.98    inference(cnf_transformation,[],[f13])).
% 2.62/0.98  
% 2.62/0.98  fof(f12,axiom,(
% 2.62/0.98    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 2.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.98  
% 2.62/0.98  fof(f17,plain,(
% 2.62/0.98    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 2.62/0.98    inference(ennf_transformation,[],[f12])).
% 2.62/0.98  
% 2.62/0.98  fof(f58,plain,(
% 2.62/0.98    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.62/0.98    inference(cnf_transformation,[],[f17])).
% 2.62/0.98  
% 2.62/0.98  fof(f5,axiom,(
% 2.62/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.98  
% 2.62/0.98  fof(f47,plain,(
% 2.62/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.62/0.98    inference(cnf_transformation,[],[f5])).
% 2.62/0.98  
% 2.62/0.98  fof(f4,axiom,(
% 2.62/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 2.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.98  
% 2.62/0.98  fof(f46,plain,(
% 2.62/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 2.62/0.98    inference(cnf_transformation,[],[f4])).
% 2.62/0.98  
% 2.62/0.98  fof(f64,plain,(
% 2.62/0.98    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))) )),
% 2.62/0.98    inference(definition_unfolding,[],[f47,f46])).
% 2.62/0.98  
% 2.62/0.98  fof(f14,axiom,(
% 2.62/0.98    ! [X0,X1,X2,X3,X4] : (v1_relat_1(X4) => (k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4 => (k2_tarski(X1,X3) = k2_relat_1(X4) & k2_tarski(X0,X2) = k1_relat_1(X4))))),
% 2.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.98  
% 2.62/0.98  fof(f18,plain,(
% 2.62/0.98    ! [X0,X1,X2,X3,X4] : (((k2_tarski(X1,X3) = k2_relat_1(X4) & k2_tarski(X0,X2) = k1_relat_1(X4)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4) | ~v1_relat_1(X4))),
% 2.62/0.98    inference(ennf_transformation,[],[f14])).
% 2.62/0.98  
% 2.62/0.98  fof(f19,plain,(
% 2.62/0.98    ! [X0,X1,X2,X3,X4] : ((k2_tarski(X1,X3) = k2_relat_1(X4) & k2_tarski(X0,X2) = k1_relat_1(X4)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4))),
% 2.62/0.98    inference(flattening,[],[f18])).
% 2.62/0.98  
% 2.62/0.98  fof(f60,plain,(
% 2.62/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_tarski(X0,X2) = k1_relat_1(X4) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 2.62/0.98    inference(cnf_transformation,[],[f19])).
% 2.62/0.98  
% 2.62/0.98  fof(f75,plain,(
% 2.62/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X2)) = k1_relat_1(X4) | k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))) != X4 | ~v1_relat_1(X4)) )),
% 2.62/0.98    inference(definition_unfolding,[],[f60,f46,f46])).
% 2.62/0.98  
% 2.62/0.98  fof(f88,plain,(
% 2.62/0.98    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X2)) = k1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))) | ~v1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))))) )),
% 2.62/0.98    inference(equality_resolution,[],[f75])).
% 2.62/0.98  
% 2.62/0.98  fof(f11,axiom,(
% 2.62/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.98  
% 2.62/0.98  fof(f57,plain,(
% 2.62/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.62/0.98    inference(cnf_transformation,[],[f11])).
% 2.62/0.98  
% 2.62/0.98  fof(f63,plain,(
% 2.62/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))) )),
% 2.62/0.98    inference(definition_unfolding,[],[f57,f46])).
% 2.62/0.98  
% 2.62/0.98  fof(f61,plain,(
% 2.62/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_tarski(X1,X3) = k2_relat_1(X4) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 2.62/0.98    inference(cnf_transformation,[],[f19])).
% 2.62/0.98  
% 2.62/0.98  fof(f74,plain,(
% 2.62/0.98    ( ! [X4,X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X1),k1_tarski(X3)) = k2_relat_1(X4) | k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))) != X4 | ~v1_relat_1(X4)) )),
% 2.62/0.98    inference(definition_unfolding,[],[f61,f46,f46])).
% 2.62/0.98  
% 2.62/0.98  fof(f87,plain,(
% 2.62/0.98    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X1),k1_tarski(X3)) = k2_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))) | ~v1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))))) )),
% 2.62/0.98    inference(equality_resolution,[],[f74])).
% 2.62/0.98  
% 2.62/0.98  fof(f15,conjecture,(
% 2.62/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 2.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.62/0.98  
% 2.62/0.98  fof(f16,negated_conjecture,(
% 2.62/0.98    ~! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 2.62/0.98    inference(negated_conjecture,[],[f15])).
% 2.62/0.98  
% 2.62/0.98  fof(f20,plain,(
% 2.62/0.98    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 2.62/0.98    inference(ennf_transformation,[],[f16])).
% 2.62/0.98  
% 2.62/0.98  fof(f33,plain,(
% 2.62/0.98    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1))) => k2_tarski(sK2,sK3) != k3_relat_1(k1_tarski(k4_tarski(sK2,sK3)))),
% 2.62/0.98    introduced(choice_axiom,[])).
% 2.62/0.98  
% 2.62/0.98  fof(f34,plain,(
% 2.62/0.98    k2_tarski(sK2,sK3) != k3_relat_1(k1_tarski(k4_tarski(sK2,sK3)))),
% 2.62/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f33])).
% 2.62/0.98  
% 2.62/0.98  fof(f62,plain,(
% 2.62/0.98    k2_tarski(sK2,sK3) != k3_relat_1(k1_tarski(k4_tarski(sK2,sK3)))),
% 2.62/0.98    inference(cnf_transformation,[],[f34])).
% 2.62/0.98  
% 2.62/0.98  fof(f76,plain,(
% 2.62/0.98    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k3_relat_1(k1_tarski(k4_tarski(sK2,sK3)))),
% 2.62/0.98    inference(definition_unfolding,[],[f62,f46])).
% 2.62/0.98  
% 2.62/0.98  cnf(c_23,plain,
% 2.62/0.98      ( v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
% 2.62/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_551,plain,
% 2.62/0.98      ( v1_relat_1(k1_tarski(k4_tarski(X0,X1))) = iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_22,plain,
% 2.62/0.98      ( ~ v1_relat_1(X0)
% 2.62/0.98      | k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ),
% 2.62/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_552,plain,
% 2.62/0.98      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
% 2.62/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_2140,plain,
% 2.62/0.98      ( k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X0,X1))),k2_relat_1(k1_tarski(k4_tarski(X0,X1)))) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_551,c_552]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1,plain,
% 2.62/0.98      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X0)) = k1_tarski(X0) ),
% 2.62/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_25,plain,
% 2.62/0.98      ( ~ v1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))))
% 2.62/0.98      | k1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))) = k2_xboole_0(k1_tarski(X0),k1_tarski(X2)) ),
% 2.62/0.98      inference(cnf_transformation,[],[f88]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_549,plain,
% 2.62/0.98      ( k1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))) = k2_xboole_0(k1_tarski(X0),k1_tarski(X2))
% 2.62/0.98      | v1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))) != iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_923,plain,
% 2.62/0.98      ( k1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X0,X1)))) = k2_xboole_0(k1_tarski(X0),k1_tarski(X0))
% 2.62/0.98      | v1_relat_1(k1_tarski(k4_tarski(X0,X1))) != iProver_top ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_1,c_549]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_924,plain,
% 2.62/0.98      ( k1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X0,X1)))) = k1_tarski(X0)
% 2.62/0.98      | v1_relat_1(k1_tarski(k4_tarski(X0,X1))) != iProver_top ),
% 2.62/0.98      inference(light_normalisation,[status(thm)],[c_923,c_1]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_925,plain,
% 2.62/0.98      ( k1_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X0)
% 2.62/0.98      | v1_relat_1(k1_tarski(k4_tarski(X0,X1))) != iProver_top ),
% 2.62/0.98      inference(demodulation,[status(thm)],[c_924,c_1]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_33,plain,
% 2.62/0.98      ( v1_relat_1(k1_tarski(k4_tarski(X0,X1))) = iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_2546,plain,
% 2.62/0.98      ( k1_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X0) ),
% 2.62/0.98      inference(global_propositional_subsumption,[status(thm)],[c_925,c_33]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_0,plain,
% 2.62/0.98      ( k3_tarski(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k2_xboole_0(X0,X1) ),
% 2.62/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_930,plain,
% 2.62/0.98      ( k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_24,plain,
% 2.62/0.98      ( ~ v1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3))))
% 2.62/0.98      | k2_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))) = k2_xboole_0(k1_tarski(X1),k1_tarski(X3)) ),
% 2.62/0.98      inference(cnf_transformation,[],[f87]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_550,plain,
% 2.62/0.98      ( k2_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))) = k2_xboole_0(k1_tarski(X1),k1_tarski(X3))
% 2.62/0.98      | v1_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X2,X3)))) != iProver_top ),
% 2.62/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1865,plain,
% 2.62/0.98      ( k2_relat_1(k2_xboole_0(k1_tarski(k4_tarski(X0,X1)),k1_tarski(k4_tarski(X0,X1)))) = k2_xboole_0(k1_tarski(X1),k1_tarski(X1))
% 2.62/0.98      | v1_relat_1(k3_tarski(k1_tarski(k1_tarski(k4_tarski(X0,X1))))) != iProver_top ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_930,c_550]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1164,plain,
% 2.62/0.98      ( k3_tarski(k1_tarski(k1_tarski(X0))) = k1_tarski(X0) ),
% 2.62/0.98      inference(superposition,[status(thm)],[c_930,c_1]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_1873,plain,
% 2.62/0.98      ( k2_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X1)
% 2.62/0.98      | v1_relat_1(k1_tarski(k4_tarski(X0,X1))) != iProver_top ),
% 2.62/0.98      inference(demodulation,[status(thm)],[c_1865,c_1,c_1164]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_2847,plain,
% 2.62/0.98      ( k2_relat_1(k1_tarski(k4_tarski(X0,X1))) = k1_tarski(X1) ),
% 2.62/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1873,c_33]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_3768,plain,
% 2.62/0.98      ( k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
% 2.62/0.98      inference(light_normalisation,[status(thm)],[c_2140,c_2546,c_2847]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_26,negated_conjecture,
% 2.62/0.98      ( k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k3_relat_1(k1_tarski(k4_tarski(sK2,sK3))) ),
% 2.62/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_3786,plain,
% 2.62/0.98      ( k3_relat_1(k1_tarski(k4_tarski(sK2,sK3))) != k3_relat_1(k1_tarski(k4_tarski(sK2,sK3))) ),
% 2.62/0.98      inference(demodulation,[status(thm)],[c_3768,c_26]) ).
% 2.62/0.98  
% 2.62/0.98  cnf(c_3800,plain,
% 2.62/0.98      ( $false ),
% 2.62/0.98      inference(equality_resolution_simp,[status(thm)],[c_3786]) ).
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.62/0.98  
% 2.62/0.98  ------                               Statistics
% 2.62/0.98  
% 2.62/0.98  ------ General
% 2.62/0.98  
% 2.62/0.98  abstr_ref_over_cycles:                  0
% 2.62/0.98  abstr_ref_under_cycles:                 0
% 2.62/0.98  gc_basic_clause_elim:                   0
% 2.62/0.98  forced_gc_time:                         0
% 2.62/0.98  parsing_time:                           0.01
% 2.62/0.98  unif_index_cands_time:                  0.
% 2.62/0.98  unif_index_add_time:                    0.
% 2.62/0.98  orderings_time:                         0.
% 2.62/0.98  out_proof_time:                         0.007
% 2.62/0.98  total_time:                             0.157
% 2.62/0.98  num_of_symbols:                         47
% 2.62/0.98  num_of_terms:                           5164
% 2.62/0.98  
% 2.62/0.98  ------ Preprocessing
% 2.62/0.98  
% 2.62/0.98  num_of_splits:                          0
% 2.62/0.98  num_of_split_atoms:                     0
% 2.62/0.98  num_of_reused_defs:                     0
% 2.62/0.98  num_eq_ax_congr_red:                    18
% 2.62/0.98  num_of_sem_filtered_clauses:            1
% 2.62/0.98  num_of_subtypes:                        0
% 2.62/0.98  monotx_restored_types:                  0
% 2.62/0.98  sat_num_of_epr_types:                   0
% 2.62/0.98  sat_num_of_non_cyclic_types:            0
% 2.62/0.98  sat_guarded_non_collapsed_types:        0
% 2.62/0.98  num_pure_diseq_elim:                    0
% 2.62/0.98  simp_replaced_by:                       0
% 2.62/0.98  res_preprocessed:                       108
% 2.62/0.98  prep_upred:                             0
% 2.62/0.98  prep_unflattend:                        1
% 2.62/0.98  smt_new_axioms:                         0
% 2.62/0.98  pred_elim_cands:                        2
% 2.62/0.98  pred_elim:                              0
% 2.62/0.98  pred_elim_cl:                           0
% 2.62/0.98  pred_elim_cycles:                       1
% 2.62/0.98  merged_defs:                            0
% 2.62/0.98  merged_defs_ncl:                        0
% 2.62/0.98  bin_hyper_res:                          0
% 2.62/0.98  prep_cycles:                            3
% 2.62/0.98  pred_elim_time:                         0.
% 2.62/0.98  splitting_time:                         0.
% 2.62/0.98  sem_filter_time:                        0.
% 2.62/0.98  monotx_time:                            0.001
% 2.62/0.98  subtype_inf_time:                       0.
% 2.62/0.98  
% 2.62/0.98  ------ Problem properties
% 2.62/0.98  
% 2.62/0.98  clauses:                                27
% 2.62/0.98  conjectures:                            1
% 2.62/0.98  epr:                                    0
% 2.62/0.98  horn:                                   22
% 2.62/0.98  ground:                                 1
% 2.62/0.98  unary:                                  14
% 2.62/0.98  binary:                                 6
% 2.62/0.98  lits:                                   48
% 2.62/0.98  lits_eq:                                29
% 2.62/0.98  fd_pure:                                0
% 2.62/0.98  fd_pseudo:                              0
% 2.62/0.98  fd_cond:                                0
% 2.62/0.98  fd_pseudo_cond:                         7
% 2.62/0.98  ac_symbols:                             0
% 2.62/0.98  
% 2.62/0.98  ------ Propositional Solver
% 2.62/0.98  
% 2.62/0.98  prop_solver_calls:                      22
% 2.62/0.98  prop_fast_solver_calls:                 484
% 2.62/0.98  smt_solver_calls:                       0
% 2.62/0.98  smt_fast_solver_calls:                  0
% 2.62/0.98  prop_num_of_clauses:                    1646
% 2.62/0.98  prop_preprocess_simplified:             5227
% 2.62/0.98  prop_fo_subsumed:                       2
% 2.62/0.98  prop_solver_time:                       0.
% 2.62/0.98  smt_solver_time:                        0.
% 2.62/0.98  smt_fast_solver_time:                   0.
% 2.62/0.98  prop_fast_solver_time:                  0.
% 2.62/0.98  prop_unsat_core_time:                   0.
% 2.62/0.98  
% 2.62/0.98  ------ QBF
% 2.62/0.98  
% 2.62/0.98  qbf_q_res:                              0
% 2.62/0.98  qbf_num_tautologies:                    0
% 2.62/0.98  qbf_prep_cycles:                        0
% 2.62/0.98  
% 2.62/0.98  ------ BMC1
% 2.62/0.98  
% 2.62/0.98  bmc1_current_bound:                     -1
% 2.62/0.98  bmc1_last_solved_bound:                 -1
% 2.62/0.98  bmc1_unsat_core_size:                   -1
% 2.62/0.98  bmc1_unsat_core_parents_size:           -1
% 2.62/0.98  bmc1_merge_next_fun:                    0
% 2.62/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.62/0.98  
% 2.62/0.98  ------ Instantiation
% 2.62/0.98  
% 2.62/0.98  inst_num_of_clauses:                    492
% 2.62/0.98  inst_num_in_passive:                    210
% 2.62/0.98  inst_num_in_active:                     159
% 2.62/0.98  inst_num_in_unprocessed:                124
% 2.62/0.98  inst_num_of_loops:                      200
% 2.62/0.98  inst_num_of_learning_restarts:          0
% 2.62/0.98  inst_num_moves_active_passive:          40
% 2.62/0.98  inst_lit_activity:                      0
% 2.62/0.98  inst_lit_activity_moves:                0
% 2.62/0.98  inst_num_tautologies:                   0
% 2.62/0.98  inst_num_prop_implied:                  0
% 2.62/0.98  inst_num_existing_simplified:           0
% 2.62/0.98  inst_num_eq_res_simplified:             0
% 2.62/0.98  inst_num_child_elim:                    0
% 2.62/0.98  inst_num_of_dismatching_blockings:      194
% 2.62/0.98  inst_num_of_non_proper_insts:           356
% 2.62/0.98  inst_num_of_duplicates:                 0
% 2.62/0.98  inst_inst_num_from_inst_to_res:         0
% 2.62/0.98  inst_dismatching_checking_time:         0.
% 2.62/0.98  
% 2.62/0.98  ------ Resolution
% 2.62/0.98  
% 2.62/0.98  res_num_of_clauses:                     0
% 2.62/0.98  res_num_in_passive:                     0
% 2.62/0.98  res_num_in_active:                      0
% 2.62/0.98  res_num_of_loops:                       111
% 2.62/0.98  res_forward_subset_subsumed:            58
% 2.62/0.98  res_backward_subset_subsumed:           2
% 2.62/0.98  res_forward_subsumed:                   0
% 2.62/0.98  res_backward_subsumed:                  0
% 2.62/0.98  res_forward_subsumption_resolution:     0
% 2.62/0.98  res_backward_subsumption_resolution:    0
% 2.62/0.98  res_clause_to_clause_subsumption:       181
% 2.62/0.98  res_orphan_elimination:                 0
% 2.62/0.98  res_tautology_del:                      5
% 2.62/0.98  res_num_eq_res_simplified:              0
% 2.62/0.98  res_num_sel_changes:                    0
% 2.62/0.98  res_moves_from_active_to_pass:          0
% 2.62/0.98  
% 2.62/0.98  ------ Superposition
% 2.62/0.98  
% 2.62/0.98  sup_time_total:                         0.
% 2.62/0.98  sup_time_generating:                    0.
% 2.62/0.98  sup_time_sim_full:                      0.
% 2.62/0.98  sup_time_sim_immed:                     0.
% 2.62/0.98  
% 2.62/0.98  sup_num_of_clauses:                     58
% 2.62/0.98  sup_num_in_active:                      19
% 2.62/0.98  sup_num_in_passive:                     39
% 2.62/0.98  sup_num_of_loops:                       38
% 2.62/0.98  sup_fw_superposition:                   131
% 2.62/0.98  sup_bw_superposition:                   74
% 2.62/0.98  sup_immediate_simplified:               32
% 2.62/0.98  sup_given_eliminated:                   0
% 2.62/0.98  comparisons_done:                       0
% 2.62/0.98  comparisons_avoided:                    3
% 2.62/0.98  
% 2.62/0.98  ------ Simplifications
% 2.62/0.98  
% 2.62/0.98  
% 2.62/0.98  sim_fw_subset_subsumed:                 0
% 2.62/0.98  sim_bw_subset_subsumed:                 0
% 2.62/0.98  sim_fw_subsumed:                        9
% 2.62/0.98  sim_bw_subsumed:                        0
% 2.62/0.98  sim_fw_subsumption_res:                 0
% 2.62/0.98  sim_bw_subsumption_res:                 0
% 2.62/0.98  sim_tautology_del:                      2
% 2.62/0.98  sim_eq_tautology_del:                   13
% 2.62/0.98  sim_eq_res_simp:                        0
% 2.62/0.98  sim_fw_demodulated:                     13
% 2.62/0.98  sim_bw_demodulated:                     20
% 2.62/0.98  sim_light_normalised:                   19
% 2.62/0.98  sim_joinable_taut:                      0
% 2.62/0.98  sim_joinable_simp:                      0
% 2.62/0.98  sim_ac_normalised:                      0
% 2.62/0.98  sim_smt_subsumption:                    0
% 2.62/0.98  
%------------------------------------------------------------------------------
