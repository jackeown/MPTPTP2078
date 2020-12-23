%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:27 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 355 expanded)
%              Number of clauses        :   36 ( 137 expanded)
%              Number of leaves         :   10 (  90 expanded)
%              Depth                    :   20
%              Number of atoms          :   85 ( 448 expanded)
%              Number of equality atoms :   56 ( 336 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f30,f28])).

fof(f9,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f28])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f29,f28,f28])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f22,f28])).

fof(f10,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(negated_conjecture,[],[f10])).

fof(f15,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1)
   => ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f15,f19])).

fof(f32,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_8,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_9,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_338,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_341,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_xboole_0(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_836,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_338,c_341])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_342,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1983,plain,
    ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_836,c_342])).

cnf(c_5,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f26])).

cnf(c_7,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_715,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(superposition,[status(thm)],[c_5,c_7])).

cnf(c_6,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_766,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_715,c_6])).

cnf(c_2232,plain,
    ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1983,c_766])).

cnf(c_1982,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_338,c_342])).

cnf(c_1987,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1982,c_5])).

cnf(c_615,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
    inference(superposition,[status(thm)],[c_5,c_8])).

cnf(c_2063,plain,
    ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(demodulation,[status(thm)],[c_1987,c_615])).

cnf(c_2236,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2232,c_2063])).

cnf(c_2358,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(demodulation,[status(thm)],[c_2236,c_766])).

cnf(c_2360,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2358,c_5,c_1987])).

cnf(c_2405,plain,
    ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8,c_2360])).

cnf(c_2598,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2405,c_7])).

cnf(c_2966,plain,
    ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = X0 ),
    inference(superposition,[status(thm)],[c_2598,c_8])).

cnf(c_3060,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_2966,c_2063])).

cnf(c_3337,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_3060,c_3060])).

cnf(c_0,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_343,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4227,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3337,c_343])).

cnf(c_2079,plain,
    ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1987,c_6])).

cnf(c_4236,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4227,c_6,c_2079])).

cnf(c_4237,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4236])).

cnf(c_10,negated_conjecture,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_337,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4883,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4237,c_337])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n020.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 13:42:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.71/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/0.99  
% 2.71/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.71/0.99  
% 2.71/0.99  ------  iProver source info
% 2.71/0.99  
% 2.71/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.71/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.71/0.99  git: non_committed_changes: false
% 2.71/0.99  git: last_make_outside_of_git: false
% 2.71/0.99  
% 2.71/0.99  ------ 
% 2.71/0.99  
% 2.71/0.99  ------ Input Options
% 2.71/0.99  
% 2.71/0.99  --out_options                           all
% 2.71/0.99  --tptp_safe_out                         true
% 2.71/0.99  --problem_path                          ""
% 2.71/0.99  --include_path                          ""
% 2.71/0.99  --clausifier                            res/vclausify_rel
% 2.71/0.99  --clausifier_options                    --mode clausify
% 2.71/0.99  --stdin                                 false
% 2.71/0.99  --stats_out                             all
% 2.71/0.99  
% 2.71/0.99  ------ General Options
% 2.71/0.99  
% 2.71/0.99  --fof                                   false
% 2.71/0.99  --time_out_real                         305.
% 2.71/0.99  --time_out_virtual                      -1.
% 2.71/0.99  --symbol_type_check                     false
% 2.71/0.99  --clausify_out                          false
% 2.71/0.99  --sig_cnt_out                           false
% 2.71/0.99  --trig_cnt_out                          false
% 2.71/0.99  --trig_cnt_out_tolerance                1.
% 2.71/0.99  --trig_cnt_out_sk_spl                   false
% 2.71/0.99  --abstr_cl_out                          false
% 2.71/0.99  
% 2.71/0.99  ------ Global Options
% 2.71/0.99  
% 2.71/0.99  --schedule                              default
% 2.71/0.99  --add_important_lit                     false
% 2.71/0.99  --prop_solver_per_cl                    1000
% 2.71/0.99  --min_unsat_core                        false
% 2.71/0.99  --soft_assumptions                      false
% 2.71/0.99  --soft_lemma_size                       3
% 2.71/0.99  --prop_impl_unit_size                   0
% 2.71/0.99  --prop_impl_unit                        []
% 2.71/0.99  --share_sel_clauses                     true
% 2.71/0.99  --reset_solvers                         false
% 2.71/0.99  --bc_imp_inh                            [conj_cone]
% 2.71/0.99  --conj_cone_tolerance                   3.
% 2.71/0.99  --extra_neg_conj                        none
% 2.71/0.99  --large_theory_mode                     true
% 2.71/0.99  --prolific_symb_bound                   200
% 2.71/0.99  --lt_threshold                          2000
% 2.71/0.99  --clause_weak_htbl                      true
% 2.71/0.99  --gc_record_bc_elim                     false
% 2.71/0.99  
% 2.71/0.99  ------ Preprocessing Options
% 2.71/0.99  
% 2.71/0.99  --preprocessing_flag                    true
% 2.71/0.99  --time_out_prep_mult                    0.1
% 2.71/0.99  --splitting_mode                        input
% 2.71/0.99  --splitting_grd                         true
% 2.71/0.99  --splitting_cvd                         false
% 2.71/0.99  --splitting_cvd_svl                     false
% 2.71/0.99  --splitting_nvd                         32
% 2.71/0.99  --sub_typing                            true
% 2.71/0.99  --prep_gs_sim                           true
% 2.71/0.99  --prep_unflatten                        true
% 2.71/0.99  --prep_res_sim                          true
% 2.71/0.99  --prep_upred                            true
% 2.71/0.99  --prep_sem_filter                       exhaustive
% 2.71/0.99  --prep_sem_filter_out                   false
% 2.71/0.99  --pred_elim                             true
% 2.71/0.99  --res_sim_input                         true
% 2.71/0.99  --eq_ax_congr_red                       true
% 2.71/0.99  --pure_diseq_elim                       true
% 2.71/0.99  --brand_transform                       false
% 2.71/0.99  --non_eq_to_eq                          false
% 2.71/0.99  --prep_def_merge                        true
% 2.71/0.99  --prep_def_merge_prop_impl              false
% 2.71/0.99  --prep_def_merge_mbd                    true
% 2.71/0.99  --prep_def_merge_tr_red                 false
% 2.71/0.99  --prep_def_merge_tr_cl                  false
% 2.71/0.99  --smt_preprocessing                     true
% 2.71/0.99  --smt_ac_axioms                         fast
% 2.71/0.99  --preprocessed_out                      false
% 2.71/0.99  --preprocessed_stats                    false
% 2.71/0.99  
% 2.71/0.99  ------ Abstraction refinement Options
% 2.71/0.99  
% 2.71/0.99  --abstr_ref                             []
% 2.71/0.99  --abstr_ref_prep                        false
% 2.71/0.99  --abstr_ref_until_sat                   false
% 2.71/0.99  --abstr_ref_sig_restrict                funpre
% 2.71/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.71/0.99  --abstr_ref_under                       []
% 2.71/0.99  
% 2.71/0.99  ------ SAT Options
% 2.71/0.99  
% 2.71/0.99  --sat_mode                              false
% 2.71/0.99  --sat_fm_restart_options                ""
% 2.71/0.99  --sat_gr_def                            false
% 2.71/0.99  --sat_epr_types                         true
% 2.71/0.99  --sat_non_cyclic_types                  false
% 2.71/0.99  --sat_finite_models                     false
% 2.71/0.99  --sat_fm_lemmas                         false
% 2.71/0.99  --sat_fm_prep                           false
% 2.71/0.99  --sat_fm_uc_incr                        true
% 2.71/0.99  --sat_out_model                         small
% 2.71/0.99  --sat_out_clauses                       false
% 2.71/0.99  
% 2.71/0.99  ------ QBF Options
% 2.71/0.99  
% 2.71/0.99  --qbf_mode                              false
% 2.71/0.99  --qbf_elim_univ                         false
% 2.71/0.99  --qbf_dom_inst                          none
% 2.71/0.99  --qbf_dom_pre_inst                      false
% 2.71/0.99  --qbf_sk_in                             false
% 2.71/0.99  --qbf_pred_elim                         true
% 2.71/0.99  --qbf_split                             512
% 2.71/0.99  
% 2.71/0.99  ------ BMC1 Options
% 2.71/0.99  
% 2.71/0.99  --bmc1_incremental                      false
% 2.71/0.99  --bmc1_axioms                           reachable_all
% 2.71/0.99  --bmc1_min_bound                        0
% 2.71/0.99  --bmc1_max_bound                        -1
% 2.71/0.99  --bmc1_max_bound_default                -1
% 2.71/0.99  --bmc1_symbol_reachability              true
% 2.71/0.99  --bmc1_property_lemmas                  false
% 2.71/0.99  --bmc1_k_induction                      false
% 2.71/0.99  --bmc1_non_equiv_states                 false
% 2.71/0.99  --bmc1_deadlock                         false
% 2.71/0.99  --bmc1_ucm                              false
% 2.71/0.99  --bmc1_add_unsat_core                   none
% 2.71/0.99  --bmc1_unsat_core_children              false
% 2.71/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.71/0.99  --bmc1_out_stat                         full
% 2.71/0.99  --bmc1_ground_init                      false
% 2.71/0.99  --bmc1_pre_inst_next_state              false
% 2.71/0.99  --bmc1_pre_inst_state                   false
% 2.71/0.99  --bmc1_pre_inst_reach_state             false
% 2.71/0.99  --bmc1_out_unsat_core                   false
% 2.71/0.99  --bmc1_aig_witness_out                  false
% 2.71/0.99  --bmc1_verbose                          false
% 2.71/0.99  --bmc1_dump_clauses_tptp                false
% 2.71/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.71/0.99  --bmc1_dump_file                        -
% 2.71/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.71/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.71/0.99  --bmc1_ucm_extend_mode                  1
% 2.71/0.99  --bmc1_ucm_init_mode                    2
% 2.71/0.99  --bmc1_ucm_cone_mode                    none
% 2.71/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.71/0.99  --bmc1_ucm_relax_model                  4
% 2.71/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.71/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.71/0.99  --bmc1_ucm_layered_model                none
% 2.71/0.99  --bmc1_ucm_max_lemma_size               10
% 2.71/0.99  
% 2.71/0.99  ------ AIG Options
% 2.71/0.99  
% 2.71/0.99  --aig_mode                              false
% 2.71/0.99  
% 2.71/0.99  ------ Instantiation Options
% 2.71/0.99  
% 2.71/0.99  --instantiation_flag                    true
% 2.71/0.99  --inst_sos_flag                         false
% 2.71/0.99  --inst_sos_phase                        true
% 2.71/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.71/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.71/0.99  --inst_lit_sel_side                     num_symb
% 2.71/0.99  --inst_solver_per_active                1400
% 2.71/0.99  --inst_solver_calls_frac                1.
% 2.71/0.99  --inst_passive_queue_type               priority_queues
% 2.71/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.71/0.99  --inst_passive_queues_freq              [25;2]
% 2.71/0.99  --inst_dismatching                      true
% 2.71/0.99  --inst_eager_unprocessed_to_passive     true
% 2.71/0.99  --inst_prop_sim_given                   true
% 2.71/0.99  --inst_prop_sim_new                     false
% 2.71/0.99  --inst_subs_new                         false
% 2.71/0.99  --inst_eq_res_simp                      false
% 2.71/0.99  --inst_subs_given                       false
% 2.71/0.99  --inst_orphan_elimination               true
% 2.71/0.99  --inst_learning_loop_flag               true
% 2.71/0.99  --inst_learning_start                   3000
% 2.71/0.99  --inst_learning_factor                  2
% 2.71/0.99  --inst_start_prop_sim_after_learn       3
% 2.71/0.99  --inst_sel_renew                        solver
% 2.71/0.99  --inst_lit_activity_flag                true
% 2.71/0.99  --inst_restr_to_given                   false
% 2.71/0.99  --inst_activity_threshold               500
% 2.71/0.99  --inst_out_proof                        true
% 2.71/0.99  
% 2.71/0.99  ------ Resolution Options
% 2.71/0.99  
% 2.71/0.99  --resolution_flag                       true
% 2.71/0.99  --res_lit_sel                           adaptive
% 2.71/0.99  --res_lit_sel_side                      none
% 2.71/0.99  --res_ordering                          kbo
% 2.71/0.99  --res_to_prop_solver                    active
% 2.71/0.99  --res_prop_simpl_new                    false
% 2.71/0.99  --res_prop_simpl_given                  true
% 2.71/0.99  --res_passive_queue_type                priority_queues
% 2.71/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.71/0.99  --res_passive_queues_freq               [15;5]
% 2.71/0.99  --res_forward_subs                      full
% 2.71/0.99  --res_backward_subs                     full
% 2.71/0.99  --res_forward_subs_resolution           true
% 2.71/0.99  --res_backward_subs_resolution          true
% 2.71/0.99  --res_orphan_elimination                true
% 2.71/0.99  --res_time_limit                        2.
% 2.71/0.99  --res_out_proof                         true
% 2.71/0.99  
% 2.71/0.99  ------ Superposition Options
% 2.71/0.99  
% 2.71/0.99  --superposition_flag                    true
% 2.71/0.99  --sup_passive_queue_type                priority_queues
% 2.71/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.71/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.71/0.99  --demod_completeness_check              fast
% 2.71/0.99  --demod_use_ground                      true
% 2.71/0.99  --sup_to_prop_solver                    passive
% 2.71/0.99  --sup_prop_simpl_new                    true
% 2.71/0.99  --sup_prop_simpl_given                  true
% 2.71/0.99  --sup_fun_splitting                     false
% 2.71/0.99  --sup_smt_interval                      50000
% 2.71/0.99  
% 2.71/0.99  ------ Superposition Simplification Setup
% 2.71/0.99  
% 2.71/0.99  --sup_indices_passive                   []
% 2.71/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.71/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.99  --sup_full_bw                           [BwDemod]
% 2.71/0.99  --sup_immed_triv                        [TrivRules]
% 2.71/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.99  --sup_immed_bw_main                     []
% 2.71/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.71/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/0.99  
% 2.71/0.99  ------ Combination Options
% 2.71/0.99  
% 2.71/0.99  --comb_res_mult                         3
% 2.71/0.99  --comb_sup_mult                         2
% 2.71/0.99  --comb_inst_mult                        10
% 2.71/0.99  
% 2.71/0.99  ------ Debug Options
% 2.71/0.99  
% 2.71/0.99  --dbg_backtrace                         false
% 2.71/0.99  --dbg_dump_prop_clauses                 false
% 2.71/0.99  --dbg_dump_prop_clauses_file            -
% 2.71/0.99  --dbg_out_stat                          false
% 2.71/0.99  ------ Parsing...
% 2.71/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.71/0.99  
% 2.71/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.71/0.99  
% 2.71/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.71/0.99  
% 2.71/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.71/0.99  ------ Proving...
% 2.71/0.99  ------ Problem Properties 
% 2.71/0.99  
% 2.71/0.99  
% 2.71/0.99  clauses                                 11
% 2.71/0.99  conjectures                             1
% 2.71/0.99  EPR                                     2
% 2.71/0.99  Horn                                    10
% 2.71/0.99  unary                                   6
% 2.71/0.99  binary                                  5
% 2.71/0.99  lits                                    16
% 2.71/0.99  lits eq                                 6
% 2.71/0.99  fd_pure                                 0
% 2.71/0.99  fd_pseudo                               0
% 2.71/0.99  fd_cond                                 0
% 2.71/0.99  fd_pseudo_cond                          0
% 2.71/0.99  AC symbols                              0
% 2.71/0.99  
% 2.71/0.99  ------ Schedule dynamic 5 is on 
% 2.71/0.99  
% 2.71/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.71/0.99  
% 2.71/0.99  
% 2.71/0.99  ------ 
% 2.71/0.99  Current options:
% 2.71/0.99  ------ 
% 2.71/0.99  
% 2.71/0.99  ------ Input Options
% 2.71/0.99  
% 2.71/0.99  --out_options                           all
% 2.71/0.99  --tptp_safe_out                         true
% 2.71/0.99  --problem_path                          ""
% 2.71/0.99  --include_path                          ""
% 2.71/0.99  --clausifier                            res/vclausify_rel
% 2.71/0.99  --clausifier_options                    --mode clausify
% 2.71/0.99  --stdin                                 false
% 2.71/0.99  --stats_out                             all
% 2.71/0.99  
% 2.71/0.99  ------ General Options
% 2.71/0.99  
% 2.71/0.99  --fof                                   false
% 2.71/1.00  --time_out_real                         305.
% 2.71/1.00  --time_out_virtual                      -1.
% 2.71/1.00  --symbol_type_check                     false
% 2.71/1.00  --clausify_out                          false
% 2.71/1.00  --sig_cnt_out                           false
% 2.71/1.00  --trig_cnt_out                          false
% 2.71/1.00  --trig_cnt_out_tolerance                1.
% 2.71/1.00  --trig_cnt_out_sk_spl                   false
% 2.71/1.00  --abstr_cl_out                          false
% 2.71/1.00  
% 2.71/1.00  ------ Global Options
% 2.71/1.00  
% 2.71/1.00  --schedule                              default
% 2.71/1.00  --add_important_lit                     false
% 2.71/1.00  --prop_solver_per_cl                    1000
% 2.71/1.00  --min_unsat_core                        false
% 2.71/1.00  --soft_assumptions                      false
% 2.71/1.00  --soft_lemma_size                       3
% 2.71/1.00  --prop_impl_unit_size                   0
% 2.71/1.00  --prop_impl_unit                        []
% 2.71/1.00  --share_sel_clauses                     true
% 2.71/1.00  --reset_solvers                         false
% 2.71/1.00  --bc_imp_inh                            [conj_cone]
% 2.71/1.00  --conj_cone_tolerance                   3.
% 2.71/1.00  --extra_neg_conj                        none
% 2.71/1.00  --large_theory_mode                     true
% 2.71/1.00  --prolific_symb_bound                   200
% 2.71/1.00  --lt_threshold                          2000
% 2.71/1.00  --clause_weak_htbl                      true
% 2.71/1.00  --gc_record_bc_elim                     false
% 2.71/1.00  
% 2.71/1.00  ------ Preprocessing Options
% 2.71/1.00  
% 2.71/1.00  --preprocessing_flag                    true
% 2.71/1.00  --time_out_prep_mult                    0.1
% 2.71/1.00  --splitting_mode                        input
% 2.71/1.00  --splitting_grd                         true
% 2.71/1.00  --splitting_cvd                         false
% 2.71/1.00  --splitting_cvd_svl                     false
% 2.71/1.00  --splitting_nvd                         32
% 2.71/1.00  --sub_typing                            true
% 2.71/1.00  --prep_gs_sim                           true
% 2.71/1.00  --prep_unflatten                        true
% 2.71/1.00  --prep_res_sim                          true
% 2.71/1.00  --prep_upred                            true
% 2.71/1.00  --prep_sem_filter                       exhaustive
% 2.71/1.00  --prep_sem_filter_out                   false
% 2.71/1.00  --pred_elim                             true
% 2.71/1.00  --res_sim_input                         true
% 2.71/1.00  --eq_ax_congr_red                       true
% 2.71/1.00  --pure_diseq_elim                       true
% 2.71/1.00  --brand_transform                       false
% 2.71/1.00  --non_eq_to_eq                          false
% 2.71/1.00  --prep_def_merge                        true
% 2.71/1.00  --prep_def_merge_prop_impl              false
% 2.71/1.00  --prep_def_merge_mbd                    true
% 2.71/1.00  --prep_def_merge_tr_red                 false
% 2.71/1.00  --prep_def_merge_tr_cl                  false
% 2.71/1.00  --smt_preprocessing                     true
% 2.71/1.00  --smt_ac_axioms                         fast
% 2.71/1.00  --preprocessed_out                      false
% 2.71/1.00  --preprocessed_stats                    false
% 2.71/1.00  
% 2.71/1.00  ------ Abstraction refinement Options
% 2.71/1.00  
% 2.71/1.00  --abstr_ref                             []
% 2.71/1.00  --abstr_ref_prep                        false
% 2.71/1.00  --abstr_ref_until_sat                   false
% 2.71/1.00  --abstr_ref_sig_restrict                funpre
% 2.71/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.71/1.00  --abstr_ref_under                       []
% 2.71/1.00  
% 2.71/1.00  ------ SAT Options
% 2.71/1.00  
% 2.71/1.00  --sat_mode                              false
% 2.71/1.00  --sat_fm_restart_options                ""
% 2.71/1.00  --sat_gr_def                            false
% 2.71/1.00  --sat_epr_types                         true
% 2.71/1.00  --sat_non_cyclic_types                  false
% 2.71/1.00  --sat_finite_models                     false
% 2.71/1.00  --sat_fm_lemmas                         false
% 2.71/1.00  --sat_fm_prep                           false
% 2.71/1.00  --sat_fm_uc_incr                        true
% 2.71/1.00  --sat_out_model                         small
% 2.71/1.00  --sat_out_clauses                       false
% 2.71/1.00  
% 2.71/1.00  ------ QBF Options
% 2.71/1.00  
% 2.71/1.00  --qbf_mode                              false
% 2.71/1.00  --qbf_elim_univ                         false
% 2.71/1.00  --qbf_dom_inst                          none
% 2.71/1.00  --qbf_dom_pre_inst                      false
% 2.71/1.00  --qbf_sk_in                             false
% 2.71/1.00  --qbf_pred_elim                         true
% 2.71/1.00  --qbf_split                             512
% 2.71/1.00  
% 2.71/1.00  ------ BMC1 Options
% 2.71/1.00  
% 2.71/1.00  --bmc1_incremental                      false
% 2.71/1.00  --bmc1_axioms                           reachable_all
% 2.71/1.00  --bmc1_min_bound                        0
% 2.71/1.00  --bmc1_max_bound                        -1
% 2.71/1.00  --bmc1_max_bound_default                -1
% 2.71/1.00  --bmc1_symbol_reachability              true
% 2.71/1.00  --bmc1_property_lemmas                  false
% 2.71/1.00  --bmc1_k_induction                      false
% 2.71/1.00  --bmc1_non_equiv_states                 false
% 2.71/1.00  --bmc1_deadlock                         false
% 2.71/1.00  --bmc1_ucm                              false
% 2.71/1.00  --bmc1_add_unsat_core                   none
% 2.71/1.00  --bmc1_unsat_core_children              false
% 2.71/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.71/1.00  --bmc1_out_stat                         full
% 2.71/1.00  --bmc1_ground_init                      false
% 2.71/1.00  --bmc1_pre_inst_next_state              false
% 2.71/1.00  --bmc1_pre_inst_state                   false
% 2.71/1.00  --bmc1_pre_inst_reach_state             false
% 2.71/1.00  --bmc1_out_unsat_core                   false
% 2.71/1.00  --bmc1_aig_witness_out                  false
% 2.71/1.00  --bmc1_verbose                          false
% 2.71/1.00  --bmc1_dump_clauses_tptp                false
% 2.71/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.71/1.00  --bmc1_dump_file                        -
% 2.71/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.71/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.71/1.00  --bmc1_ucm_extend_mode                  1
% 2.71/1.00  --bmc1_ucm_init_mode                    2
% 2.71/1.00  --bmc1_ucm_cone_mode                    none
% 2.71/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.71/1.00  --bmc1_ucm_relax_model                  4
% 2.71/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.71/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.71/1.00  --bmc1_ucm_layered_model                none
% 2.71/1.00  --bmc1_ucm_max_lemma_size               10
% 2.71/1.00  
% 2.71/1.00  ------ AIG Options
% 2.71/1.00  
% 2.71/1.00  --aig_mode                              false
% 2.71/1.00  
% 2.71/1.00  ------ Instantiation Options
% 2.71/1.00  
% 2.71/1.00  --instantiation_flag                    true
% 2.71/1.00  --inst_sos_flag                         false
% 2.71/1.00  --inst_sos_phase                        true
% 2.71/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.71/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.71/1.00  --inst_lit_sel_side                     none
% 2.71/1.00  --inst_solver_per_active                1400
% 2.71/1.00  --inst_solver_calls_frac                1.
% 2.71/1.00  --inst_passive_queue_type               priority_queues
% 2.71/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.71/1.00  --inst_passive_queues_freq              [25;2]
% 2.71/1.00  --inst_dismatching                      true
% 2.71/1.00  --inst_eager_unprocessed_to_passive     true
% 2.71/1.00  --inst_prop_sim_given                   true
% 2.71/1.00  --inst_prop_sim_new                     false
% 2.71/1.00  --inst_subs_new                         false
% 2.71/1.00  --inst_eq_res_simp                      false
% 2.71/1.00  --inst_subs_given                       false
% 2.71/1.00  --inst_orphan_elimination               true
% 2.71/1.00  --inst_learning_loop_flag               true
% 2.71/1.00  --inst_learning_start                   3000
% 2.71/1.00  --inst_learning_factor                  2
% 2.71/1.00  --inst_start_prop_sim_after_learn       3
% 2.71/1.00  --inst_sel_renew                        solver
% 2.71/1.00  --inst_lit_activity_flag                true
% 2.71/1.00  --inst_restr_to_given                   false
% 2.71/1.00  --inst_activity_threshold               500
% 2.71/1.00  --inst_out_proof                        true
% 2.71/1.00  
% 2.71/1.00  ------ Resolution Options
% 2.71/1.00  
% 2.71/1.00  --resolution_flag                       false
% 2.71/1.00  --res_lit_sel                           adaptive
% 2.71/1.00  --res_lit_sel_side                      none
% 2.71/1.00  --res_ordering                          kbo
% 2.71/1.00  --res_to_prop_solver                    active
% 2.71/1.00  --res_prop_simpl_new                    false
% 2.71/1.00  --res_prop_simpl_given                  true
% 2.71/1.00  --res_passive_queue_type                priority_queues
% 2.71/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.71/1.00  --res_passive_queues_freq               [15;5]
% 2.71/1.00  --res_forward_subs                      full
% 2.71/1.00  --res_backward_subs                     full
% 2.71/1.00  --res_forward_subs_resolution           true
% 2.71/1.00  --res_backward_subs_resolution          true
% 2.71/1.00  --res_orphan_elimination                true
% 2.71/1.00  --res_time_limit                        2.
% 2.71/1.00  --res_out_proof                         true
% 2.71/1.00  
% 2.71/1.00  ------ Superposition Options
% 2.71/1.00  
% 2.71/1.00  --superposition_flag                    true
% 2.71/1.00  --sup_passive_queue_type                priority_queues
% 2.71/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.71/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.71/1.00  --demod_completeness_check              fast
% 2.71/1.00  --demod_use_ground                      true
% 2.71/1.00  --sup_to_prop_solver                    passive
% 2.71/1.00  --sup_prop_simpl_new                    true
% 2.71/1.00  --sup_prop_simpl_given                  true
% 2.71/1.00  --sup_fun_splitting                     false
% 2.71/1.00  --sup_smt_interval                      50000
% 2.71/1.00  
% 2.71/1.00  ------ Superposition Simplification Setup
% 2.71/1.00  
% 2.71/1.00  --sup_indices_passive                   []
% 2.71/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.71/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.71/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/1.00  --sup_full_bw                           [BwDemod]
% 2.71/1.00  --sup_immed_triv                        [TrivRules]
% 2.71/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/1.00  --sup_immed_bw_main                     []
% 2.71/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.71/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.71/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.71/1.00  
% 2.71/1.00  ------ Combination Options
% 2.71/1.00  
% 2.71/1.00  --comb_res_mult                         3
% 2.71/1.00  --comb_sup_mult                         2
% 2.71/1.00  --comb_inst_mult                        10
% 2.71/1.00  
% 2.71/1.00  ------ Debug Options
% 2.71/1.00  
% 2.71/1.00  --dbg_backtrace                         false
% 2.71/1.00  --dbg_dump_prop_clauses                 false
% 2.71/1.00  --dbg_dump_prop_clauses_file            -
% 2.71/1.00  --dbg_out_stat                          false
% 2.71/1.00  
% 2.71/1.00  
% 2.71/1.00  
% 2.71/1.00  
% 2.71/1.00  ------ Proving...
% 2.71/1.00  
% 2.71/1.00  
% 2.71/1.00  % SZS status Theorem for theBenchmark.p
% 2.71/1.00  
% 2.71/1.00   Resolution empty clause
% 2.71/1.00  
% 2.71/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.71/1.00  
% 2.71/1.00  fof(f8,axiom,(
% 2.71/1.00    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.00  
% 2.71/1.00  fof(f30,plain,(
% 2.71/1.00    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.71/1.00    inference(cnf_transformation,[],[f8])).
% 2.71/1.00  
% 2.71/1.00  fof(f6,axiom,(
% 2.71/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.00  
% 2.71/1.00  fof(f28,plain,(
% 2.71/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.71/1.00    inference(cnf_transformation,[],[f6])).
% 2.71/1.00  
% 2.71/1.00  fof(f38,plain,(
% 2.71/1.00    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 2.71/1.00    inference(definition_unfolding,[],[f30,f28])).
% 2.71/1.00  
% 2.71/1.00  fof(f9,axiom,(
% 2.71/1.00    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.00  
% 2.71/1.00  fof(f31,plain,(
% 2.71/1.00    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.71/1.00    inference(cnf_transformation,[],[f9])).
% 2.71/1.00  
% 2.71/1.00  fof(f2,axiom,(
% 2.71/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.00  
% 2.71/1.00  fof(f13,plain,(
% 2.71/1.00    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.71/1.00    inference(ennf_transformation,[],[f2])).
% 2.71/1.00  
% 2.71/1.00  fof(f23,plain,(
% 2.71/1.00    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.71/1.00    inference(cnf_transformation,[],[f13])).
% 2.71/1.00  
% 2.71/1.00  fof(f1,axiom,(
% 2.71/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.00  
% 2.71/1.00  fof(f16,plain,(
% 2.71/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.71/1.00    inference(nnf_transformation,[],[f1])).
% 2.71/1.00  
% 2.71/1.00  fof(f21,plain,(
% 2.71/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.71/1.00    inference(cnf_transformation,[],[f16])).
% 2.71/1.00  
% 2.71/1.00  fof(f34,plain,(
% 2.71/1.00    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.71/1.00    inference(definition_unfolding,[],[f21,f28])).
% 2.71/1.00  
% 2.71/1.00  fof(f4,axiom,(
% 2.71/1.00    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.00  
% 2.71/1.00  fof(f26,plain,(
% 2.71/1.00    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.71/1.00    inference(cnf_transformation,[],[f4])).
% 2.71/1.00  
% 2.71/1.00  fof(f7,axiom,(
% 2.71/1.00    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.00  
% 2.71/1.00  fof(f29,plain,(
% 2.71/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.71/1.00    inference(cnf_transformation,[],[f7])).
% 2.71/1.00  
% 2.71/1.00  fof(f37,plain,(
% 2.71/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 2.71/1.00    inference(definition_unfolding,[],[f29,f28,f28])).
% 2.71/1.00  
% 2.71/1.00  fof(f5,axiom,(
% 2.71/1.00    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 2.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.00  
% 2.71/1.00  fof(f27,plain,(
% 2.71/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 2.71/1.00    inference(cnf_transformation,[],[f5])).
% 2.71/1.00  
% 2.71/1.00  fof(f22,plain,(
% 2.71/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.71/1.00    inference(cnf_transformation,[],[f16])).
% 2.71/1.00  
% 2.71/1.00  fof(f33,plain,(
% 2.71/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.71/1.00    inference(definition_unfolding,[],[f22,f28])).
% 2.71/1.00  
% 2.71/1.00  fof(f10,conjecture,(
% 2.71/1.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.71/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.00  
% 2.71/1.00  fof(f11,negated_conjecture,(
% 2.71/1.00    ~! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.71/1.00    inference(negated_conjecture,[],[f10])).
% 2.71/1.00  
% 2.71/1.00  fof(f15,plain,(
% 2.71/1.00    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.71/1.00    inference(ennf_transformation,[],[f11])).
% 2.71/1.00  
% 2.71/1.00  fof(f19,plain,(
% 2.71/1.00    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),X1) => ~r1_xboole_0(k4_xboole_0(sK1,sK2),sK2)),
% 2.71/1.00    introduced(choice_axiom,[])).
% 2.71/1.00  
% 2.71/1.00  fof(f20,plain,(
% 2.71/1.00    ~r1_xboole_0(k4_xboole_0(sK1,sK2),sK2)),
% 2.71/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f15,f19])).
% 2.71/1.00  
% 2.71/1.00  fof(f32,plain,(
% 2.71/1.00    ~r1_xboole_0(k4_xboole_0(sK1,sK2),sK2)),
% 2.71/1.00    inference(cnf_transformation,[],[f20])).
% 2.71/1.00  
% 2.71/1.00  cnf(c_8,plain,
% 2.71/1.00      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 2.71/1.00      inference(cnf_transformation,[],[f38]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_9,plain,
% 2.71/1.00      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.71/1.00      inference(cnf_transformation,[],[f31]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_338,plain,
% 2.71/1.00      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 2.71/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_2,plain,
% 2.71/1.00      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 2.71/1.00      inference(cnf_transformation,[],[f23]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_341,plain,
% 2.71/1.00      ( r1_xboole_0(X0,X1) != iProver_top | r1_xboole_0(X1,X0) = iProver_top ),
% 2.71/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_836,plain,
% 2.71/1.00      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top ),
% 2.71/1.00      inference(superposition,[status(thm)],[c_338,c_341]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_1,plain,
% 2.71/1.00      ( ~ r1_xboole_0(X0,X1)
% 2.71/1.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 2.71/1.00      inference(cnf_transformation,[],[f34]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_342,plain,
% 2.71/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 2.71/1.00      | r1_xboole_0(X0,X1) != iProver_top ),
% 2.71/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_1983,plain,
% 2.71/1.00      ( k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 2.71/1.00      inference(superposition,[status(thm)],[c_836,c_342]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_5,plain,
% 2.71/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.71/1.00      inference(cnf_transformation,[],[f26]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_7,plain,
% 2.71/1.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
% 2.71/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_715,plain,
% 2.71/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(k4_xboole_0(X0,X0),X1) ),
% 2.71/1.00      inference(superposition,[status(thm)],[c_5,c_7]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_6,plain,
% 2.71/1.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 2.71/1.00      inference(cnf_transformation,[],[f27]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_766,plain,
% 2.71/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(k1_xboole_0,X1))) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
% 2.71/1.00      inference(demodulation,[status(thm)],[c_715,c_6]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_2232,plain,
% 2.71/1.00      ( k4_xboole_0(k1_xboole_0,k2_xboole_0(k1_xboole_0,X0)) = k1_xboole_0 ),
% 2.71/1.00      inference(superposition,[status(thm)],[c_1983,c_766]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_1982,plain,
% 2.71/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.71/1.00      inference(superposition,[status(thm)],[c_338,c_342]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_1987,plain,
% 2.71/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.71/1.00      inference(light_normalisation,[status(thm)],[c_1982,c_5]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_615,plain,
% 2.71/1.00      ( k2_xboole_0(k4_xboole_0(X0,X0),X0) = X0 ),
% 2.71/1.00      inference(superposition,[status(thm)],[c_5,c_8]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_2063,plain,
% 2.71/1.00      ( k2_xboole_0(k1_xboole_0,X0) = X0 ),
% 2.71/1.00      inference(demodulation,[status(thm)],[c_1987,c_615]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_2236,plain,
% 2.71/1.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.71/1.00      inference(light_normalisation,[status(thm)],[c_2232,c_2063]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_2358,plain,
% 2.71/1.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
% 2.71/1.00      inference(demodulation,[status(thm)],[c_2236,c_766]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_2360,plain,
% 2.71/1.00      ( k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
% 2.71/1.00      inference(light_normalisation,[status(thm)],[c_2358,c_5,c_1987]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_2405,plain,
% 2.71/1.00      ( k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = k1_xboole_0 ),
% 2.71/1.00      inference(superposition,[status(thm)],[c_8,c_2360]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_2598,plain,
% 2.71/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = k1_xboole_0 ),
% 2.71/1.00      inference(superposition,[status(thm)],[c_2405,c_7]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_2966,plain,
% 2.71/1.00      ( k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k4_xboole_0(X1,X0))) = X0 ),
% 2.71/1.00      inference(superposition,[status(thm)],[c_2598,c_8]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_3060,plain,
% 2.71/1.00      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 2.71/1.00      inference(superposition,[status(thm)],[c_2966,c_2063]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_3337,plain,
% 2.71/1.00      ( k4_xboole_0(k4_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 2.71/1.00      inference(superposition,[status(thm)],[c_3060,c_3060]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_0,plain,
% 2.71/1.00      ( r1_xboole_0(X0,X1)
% 2.71/1.00      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0 ),
% 2.71/1.00      inference(cnf_transformation,[],[f33]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_343,plain,
% 2.71/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k1_xboole_0
% 2.71/1.00      | r1_xboole_0(X0,X1) = iProver_top ),
% 2.71/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_4227,plain,
% 2.71/1.00      ( k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) != k1_xboole_0
% 2.71/1.00      | r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 2.71/1.00      inference(superposition,[status(thm)],[c_3337,c_343]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_2079,plain,
% 2.71/1.00      ( k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(X0,X1))) = k1_xboole_0 ),
% 2.71/1.00      inference(superposition,[status(thm)],[c_1987,c_6]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_4236,plain,
% 2.71/1.00      ( k1_xboole_0 != k1_xboole_0
% 2.71/1.00      | r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 2.71/1.00      inference(demodulation,[status(thm)],[c_4227,c_6,c_2079]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_4237,plain,
% 2.71/1.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 2.71/1.00      inference(equality_resolution_simp,[status(thm)],[c_4236]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_10,negated_conjecture,
% 2.71/1.00      ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
% 2.71/1.00      inference(cnf_transformation,[],[f32]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_337,plain,
% 2.71/1.00      ( r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) != iProver_top ),
% 2.71/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.71/1.00  
% 2.71/1.00  cnf(c_4883,plain,
% 2.71/1.00      ( $false ),
% 2.71/1.00      inference(superposition,[status(thm)],[c_4237,c_337]) ).
% 2.71/1.00  
% 2.71/1.00  
% 2.71/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.71/1.00  
% 2.71/1.00  ------                               Statistics
% 2.71/1.00  
% 2.71/1.00  ------ General
% 2.71/1.00  
% 2.71/1.00  abstr_ref_over_cycles:                  0
% 2.71/1.00  abstr_ref_under_cycles:                 0
% 2.71/1.00  gc_basic_clause_elim:                   0
% 2.71/1.00  forced_gc_time:                         0
% 2.71/1.00  parsing_time:                           0.008
% 2.71/1.00  unif_index_cands_time:                  0.
% 2.71/1.00  unif_index_add_time:                    0.
% 2.71/1.00  orderings_time:                         0.
% 2.71/1.00  out_proof_time:                         0.006
% 2.71/1.00  total_time:                             0.169
% 2.71/1.00  num_of_symbols:                         39
% 2.71/1.00  num_of_terms:                           6578
% 2.71/1.00  
% 2.71/1.00  ------ Preprocessing
% 2.71/1.00  
% 2.71/1.00  num_of_splits:                          0
% 2.71/1.00  num_of_split_atoms:                     0
% 2.71/1.00  num_of_reused_defs:                     0
% 2.71/1.00  num_eq_ax_congr_red:                    4
% 2.71/1.00  num_of_sem_filtered_clauses:            1
% 2.71/1.00  num_of_subtypes:                        0
% 2.71/1.00  monotx_restored_types:                  0
% 2.71/1.00  sat_num_of_epr_types:                   0
% 2.71/1.00  sat_num_of_non_cyclic_types:            0
% 2.71/1.00  sat_guarded_non_collapsed_types:        0
% 2.71/1.00  num_pure_diseq_elim:                    0
% 2.71/1.00  simp_replaced_by:                       0
% 2.71/1.00  res_preprocessed:                       46
% 2.71/1.00  prep_upred:                             0
% 2.71/1.00  prep_unflattend:                        1
% 2.71/1.00  smt_new_axioms:                         0
% 2.71/1.00  pred_elim_cands:                        2
% 2.71/1.00  pred_elim:                              0
% 2.71/1.00  pred_elim_cl:                           0
% 2.71/1.00  pred_elim_cycles:                       1
% 2.71/1.00  merged_defs:                            6
% 2.71/1.00  merged_defs_ncl:                        0
% 2.71/1.00  bin_hyper_res:                          6
% 2.71/1.00  prep_cycles:                            3
% 2.71/1.00  pred_elim_time:                         0.
% 2.71/1.00  splitting_time:                         0.
% 2.71/1.00  sem_filter_time:                        0.
% 2.71/1.00  monotx_time:                            0.
% 2.71/1.00  subtype_inf_time:                       0.
% 2.71/1.00  
% 2.71/1.00  ------ Problem properties
% 2.71/1.00  
% 2.71/1.00  clauses:                                11
% 2.71/1.00  conjectures:                            1
% 2.71/1.00  epr:                                    2
% 2.71/1.00  horn:                                   10
% 2.71/1.00  ground:                                 1
% 2.71/1.00  unary:                                  6
% 2.71/1.00  binary:                                 5
% 2.71/1.00  lits:                                   16
% 2.71/1.00  lits_eq:                                6
% 2.71/1.00  fd_pure:                                0
% 2.71/1.00  fd_pseudo:                              0
% 2.71/1.00  fd_cond:                                0
% 2.71/1.00  fd_pseudo_cond:                         0
% 2.71/1.00  ac_symbols:                             0
% 2.71/1.00  
% 2.71/1.00  ------ Propositional Solver
% 2.71/1.00  
% 2.71/1.00  prop_solver_calls:                      27
% 2.71/1.00  prop_fast_solver_calls:                 232
% 2.71/1.00  smt_solver_calls:                       0
% 2.71/1.00  smt_fast_solver_calls:                  0
% 2.71/1.00  prop_num_of_clauses:                    1721
% 2.71/1.00  prop_preprocess_simplified:             2681
% 2.71/1.00  prop_fo_subsumed:                       0
% 2.71/1.00  prop_solver_time:                       0.
% 2.71/1.00  smt_solver_time:                        0.
% 2.71/1.00  smt_fast_solver_time:                   0.
% 2.71/1.00  prop_fast_solver_time:                  0.
% 2.71/1.00  prop_unsat_core_time:                   0.
% 2.71/1.00  
% 2.71/1.00  ------ QBF
% 2.71/1.00  
% 2.71/1.00  qbf_q_res:                              0
% 2.71/1.00  qbf_num_tautologies:                    0
% 2.71/1.00  qbf_prep_cycles:                        0
% 2.71/1.00  
% 2.71/1.00  ------ BMC1
% 2.71/1.00  
% 2.71/1.00  bmc1_current_bound:                     -1
% 2.71/1.00  bmc1_last_solved_bound:                 -1
% 2.71/1.00  bmc1_unsat_core_size:                   -1
% 2.71/1.00  bmc1_unsat_core_parents_size:           -1
% 2.71/1.00  bmc1_merge_next_fun:                    0
% 2.71/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.71/1.00  
% 2.71/1.00  ------ Instantiation
% 2.71/1.00  
% 2.71/1.00  inst_num_of_clauses:                    495
% 2.71/1.00  inst_num_in_passive:                    109
% 2.71/1.00  inst_num_in_active:                     241
% 2.71/1.00  inst_num_in_unprocessed:                145
% 2.71/1.00  inst_num_of_loops:                      250
% 2.71/1.00  inst_num_of_learning_restarts:          0
% 2.71/1.00  inst_num_moves_active_passive:          4
% 2.71/1.00  inst_lit_activity:                      0
% 2.71/1.00  inst_lit_activity_moves:                0
% 2.71/1.00  inst_num_tautologies:                   0
% 2.71/1.00  inst_num_prop_implied:                  0
% 2.71/1.00  inst_num_existing_simplified:           0
% 2.71/1.00  inst_num_eq_res_simplified:             0
% 2.71/1.00  inst_num_child_elim:                    0
% 2.71/1.00  inst_num_of_dismatching_blockings:      50
% 2.71/1.00  inst_num_of_non_proper_insts:           395
% 2.71/1.00  inst_num_of_duplicates:                 0
% 2.71/1.00  inst_inst_num_from_inst_to_res:         0
% 2.71/1.00  inst_dismatching_checking_time:         0.
% 2.71/1.00  
% 2.71/1.00  ------ Resolution
% 2.71/1.00  
% 2.71/1.00  res_num_of_clauses:                     0
% 2.71/1.00  res_num_in_passive:                     0
% 2.71/1.00  res_num_in_active:                      0
% 2.71/1.00  res_num_of_loops:                       49
% 2.71/1.00  res_forward_subset_subsumed:            60
% 2.71/1.00  res_backward_subset_subsumed:           0
% 2.71/1.00  res_forward_subsumed:                   0
% 2.71/1.00  res_backward_subsumed:                  0
% 2.71/1.00  res_forward_subsumption_resolution:     0
% 2.71/1.00  res_backward_subsumption_resolution:    0
% 2.71/1.00  res_clause_to_clause_subsumption:       1608
% 2.71/1.00  res_orphan_elimination:                 0
% 2.71/1.00  res_tautology_del:                      62
% 2.71/1.00  res_num_eq_res_simplified:              0
% 2.71/1.00  res_num_sel_changes:                    0
% 2.71/1.00  res_moves_from_active_to_pass:          0
% 2.71/1.00  
% 2.71/1.00  ------ Superposition
% 2.71/1.00  
% 2.71/1.00  sup_time_total:                         0.
% 2.71/1.00  sup_time_generating:                    0.
% 2.71/1.00  sup_time_sim_full:                      0.
% 2.71/1.00  sup_time_sim_immed:                     0.
% 2.71/1.00  
% 2.71/1.00  sup_num_of_clauses:                     298
% 2.71/1.00  sup_num_in_active:                      34
% 2.71/1.00  sup_num_in_passive:                     264
% 2.71/1.00  sup_num_of_loops:                       49
% 2.71/1.00  sup_fw_superposition:                   456
% 2.71/1.00  sup_bw_superposition:                   401
% 2.71/1.00  sup_immediate_simplified:               425
% 2.71/1.00  sup_given_eliminated:                   2
% 2.71/1.00  comparisons_done:                       0
% 2.71/1.00  comparisons_avoided:                    0
% 2.71/1.00  
% 2.71/1.00  ------ Simplifications
% 2.71/1.00  
% 2.71/1.00  
% 2.71/1.00  sim_fw_subset_subsumed:                 5
% 2.71/1.00  sim_bw_subset_subsumed:                 0
% 2.71/1.00  sim_fw_subsumed:                        72
% 2.71/1.00  sim_bw_subsumed:                        5
% 2.71/1.00  sim_fw_subsumption_res:                 0
% 2.71/1.00  sim_bw_subsumption_res:                 0
% 2.71/1.00  sim_tautology_del:                      1
% 2.71/1.00  sim_eq_tautology_del:                   87
% 2.71/1.00  sim_eq_res_simp:                        3
% 2.71/1.00  sim_fw_demodulated:                     209
% 2.71/1.00  sim_bw_demodulated:                     21
% 2.71/1.00  sim_light_normalised:                   189
% 2.71/1.00  sim_joinable_taut:                      0
% 2.71/1.00  sim_joinable_simp:                      0
% 2.71/1.00  sim_ac_normalised:                      0
% 2.71/1.00  sim_smt_subsumption:                    0
% 2.71/1.00  
%------------------------------------------------------------------------------
