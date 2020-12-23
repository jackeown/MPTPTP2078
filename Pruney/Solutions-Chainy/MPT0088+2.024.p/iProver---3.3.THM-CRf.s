%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:35 EST 2020

% Result     : Theorem 6.63s
% Output     : CNFRefutation 6.63s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 115 expanded)
%              Number of clauses        :   28 (  44 expanded)
%              Number of leaves         :   10 (  28 expanded)
%              Depth                    :   17
%              Number of atoms          :   76 ( 158 expanded)
%              Number of equality atoms :   40 (  90 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
     => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
       => r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X1,k4_xboole_0(X0,X2))
      & r1_xboole_0(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

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

fof(f25,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f16,f23])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_5,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_483,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_5,c_3])).

cnf(c_9,negated_conjecture,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_266,plain,
    ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_270,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2235,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_266,c_270])).

cnf(c_6,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2647,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2235,c_6])).

cnf(c_4,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_2660,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_2647,c_4])).

cnf(c_2769,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[status(thm)],[c_2660,c_5])).

cnf(c_4658,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_483,c_2769])).

cnf(c_4664,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_4658,c_2769])).

cnf(c_19926,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
    inference(superposition,[status(thm)],[c_4664,c_6])).

cnf(c_19978,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X0) ),
    inference(demodulation,[status(thm)],[c_19926,c_6])).

cnf(c_24777,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[status(thm)],[c_3,c_19978])).

cnf(c_7,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_268,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_482,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_268])).

cnf(c_25051,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_24777,c_482])).

cnf(c_2,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_427,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
    | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_428,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) != iProver_top
    | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_8,negated_conjecture,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_11,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25051,c_428,c_11])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:16:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 6.63/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.63/1.48  
% 6.63/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.63/1.48  
% 6.63/1.48  ------  iProver source info
% 6.63/1.48  
% 6.63/1.48  git: date: 2020-06-30 10:37:57 +0100
% 6.63/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.63/1.48  git: non_committed_changes: false
% 6.63/1.48  git: last_make_outside_of_git: false
% 6.63/1.48  
% 6.63/1.48  ------ 
% 6.63/1.48  
% 6.63/1.48  ------ Input Options
% 6.63/1.48  
% 6.63/1.48  --out_options                           all
% 6.63/1.48  --tptp_safe_out                         true
% 6.63/1.48  --problem_path                          ""
% 6.63/1.48  --include_path                          ""
% 6.63/1.48  --clausifier                            res/vclausify_rel
% 6.63/1.48  --clausifier_options                    --mode clausify
% 6.63/1.48  --stdin                                 false
% 6.63/1.48  --stats_out                             all
% 6.63/1.48  
% 6.63/1.48  ------ General Options
% 6.63/1.48  
% 6.63/1.48  --fof                                   false
% 6.63/1.48  --time_out_real                         305.
% 6.63/1.48  --time_out_virtual                      -1.
% 6.63/1.48  --symbol_type_check                     false
% 6.63/1.48  --clausify_out                          false
% 6.63/1.48  --sig_cnt_out                           false
% 6.63/1.48  --trig_cnt_out                          false
% 6.63/1.48  --trig_cnt_out_tolerance                1.
% 6.63/1.48  --trig_cnt_out_sk_spl                   false
% 6.63/1.48  --abstr_cl_out                          false
% 6.63/1.48  
% 6.63/1.48  ------ Global Options
% 6.63/1.48  
% 6.63/1.48  --schedule                              default
% 6.63/1.48  --add_important_lit                     false
% 6.63/1.48  --prop_solver_per_cl                    1000
% 6.63/1.48  --min_unsat_core                        false
% 6.63/1.48  --soft_assumptions                      false
% 6.63/1.48  --soft_lemma_size                       3
% 6.63/1.48  --prop_impl_unit_size                   0
% 6.63/1.48  --prop_impl_unit                        []
% 6.63/1.48  --share_sel_clauses                     true
% 6.63/1.48  --reset_solvers                         false
% 6.63/1.48  --bc_imp_inh                            [conj_cone]
% 6.63/1.48  --conj_cone_tolerance                   3.
% 6.63/1.48  --extra_neg_conj                        none
% 6.63/1.48  --large_theory_mode                     true
% 6.63/1.48  --prolific_symb_bound                   200
% 6.63/1.48  --lt_threshold                          2000
% 6.63/1.48  --clause_weak_htbl                      true
% 6.63/1.48  --gc_record_bc_elim                     false
% 6.63/1.48  
% 6.63/1.48  ------ Preprocessing Options
% 6.63/1.48  
% 6.63/1.48  --preprocessing_flag                    true
% 6.63/1.48  --time_out_prep_mult                    0.1
% 6.63/1.48  --splitting_mode                        input
% 6.63/1.48  --splitting_grd                         true
% 6.63/1.48  --splitting_cvd                         false
% 6.63/1.48  --splitting_cvd_svl                     false
% 6.63/1.48  --splitting_nvd                         32
% 6.63/1.48  --sub_typing                            true
% 6.63/1.48  --prep_gs_sim                           true
% 6.63/1.48  --prep_unflatten                        true
% 6.63/1.48  --prep_res_sim                          true
% 6.63/1.48  --prep_upred                            true
% 6.63/1.48  --prep_sem_filter                       exhaustive
% 6.63/1.48  --prep_sem_filter_out                   false
% 6.63/1.48  --pred_elim                             true
% 6.63/1.48  --res_sim_input                         true
% 6.63/1.48  --eq_ax_congr_red                       true
% 6.63/1.48  --pure_diseq_elim                       true
% 6.63/1.48  --brand_transform                       false
% 6.63/1.48  --non_eq_to_eq                          false
% 6.63/1.48  --prep_def_merge                        true
% 6.63/1.48  --prep_def_merge_prop_impl              false
% 6.63/1.48  --prep_def_merge_mbd                    true
% 6.63/1.48  --prep_def_merge_tr_red                 false
% 6.63/1.48  --prep_def_merge_tr_cl                  false
% 6.63/1.48  --smt_preprocessing                     true
% 6.63/1.48  --smt_ac_axioms                         fast
% 6.63/1.48  --preprocessed_out                      false
% 6.63/1.48  --preprocessed_stats                    false
% 6.63/1.48  
% 6.63/1.48  ------ Abstraction refinement Options
% 6.63/1.48  
% 6.63/1.48  --abstr_ref                             []
% 6.63/1.48  --abstr_ref_prep                        false
% 6.63/1.48  --abstr_ref_until_sat                   false
% 6.63/1.48  --abstr_ref_sig_restrict                funpre
% 6.63/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.63/1.48  --abstr_ref_under                       []
% 6.63/1.48  
% 6.63/1.48  ------ SAT Options
% 6.63/1.48  
% 6.63/1.48  --sat_mode                              false
% 6.63/1.48  --sat_fm_restart_options                ""
% 6.63/1.48  --sat_gr_def                            false
% 6.63/1.48  --sat_epr_types                         true
% 6.63/1.48  --sat_non_cyclic_types                  false
% 6.63/1.48  --sat_finite_models                     false
% 6.63/1.48  --sat_fm_lemmas                         false
% 6.63/1.48  --sat_fm_prep                           false
% 6.63/1.48  --sat_fm_uc_incr                        true
% 6.63/1.48  --sat_out_model                         small
% 6.63/1.48  --sat_out_clauses                       false
% 6.63/1.48  
% 6.63/1.48  ------ QBF Options
% 6.63/1.48  
% 6.63/1.48  --qbf_mode                              false
% 6.63/1.48  --qbf_elim_univ                         false
% 6.63/1.48  --qbf_dom_inst                          none
% 6.63/1.48  --qbf_dom_pre_inst                      false
% 6.63/1.48  --qbf_sk_in                             false
% 6.63/1.48  --qbf_pred_elim                         true
% 6.63/1.48  --qbf_split                             512
% 6.63/1.48  
% 6.63/1.48  ------ BMC1 Options
% 6.63/1.48  
% 6.63/1.48  --bmc1_incremental                      false
% 6.63/1.48  --bmc1_axioms                           reachable_all
% 6.63/1.48  --bmc1_min_bound                        0
% 6.63/1.48  --bmc1_max_bound                        -1
% 6.63/1.48  --bmc1_max_bound_default                -1
% 6.63/1.48  --bmc1_symbol_reachability              true
% 6.63/1.48  --bmc1_property_lemmas                  false
% 6.63/1.48  --bmc1_k_induction                      false
% 6.63/1.48  --bmc1_non_equiv_states                 false
% 6.63/1.48  --bmc1_deadlock                         false
% 6.63/1.48  --bmc1_ucm                              false
% 6.63/1.48  --bmc1_add_unsat_core                   none
% 6.63/1.48  --bmc1_unsat_core_children              false
% 6.63/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.63/1.48  --bmc1_out_stat                         full
% 6.63/1.48  --bmc1_ground_init                      false
% 6.63/1.48  --bmc1_pre_inst_next_state              false
% 6.63/1.48  --bmc1_pre_inst_state                   false
% 6.63/1.48  --bmc1_pre_inst_reach_state             false
% 6.63/1.48  --bmc1_out_unsat_core                   false
% 6.63/1.48  --bmc1_aig_witness_out                  false
% 6.63/1.48  --bmc1_verbose                          false
% 6.63/1.48  --bmc1_dump_clauses_tptp                false
% 6.63/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.63/1.48  --bmc1_dump_file                        -
% 6.63/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.63/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.63/1.48  --bmc1_ucm_extend_mode                  1
% 6.63/1.48  --bmc1_ucm_init_mode                    2
% 6.63/1.48  --bmc1_ucm_cone_mode                    none
% 6.63/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.63/1.48  --bmc1_ucm_relax_model                  4
% 6.63/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.63/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.63/1.48  --bmc1_ucm_layered_model                none
% 6.63/1.48  --bmc1_ucm_max_lemma_size               10
% 6.63/1.48  
% 6.63/1.48  ------ AIG Options
% 6.63/1.48  
% 6.63/1.48  --aig_mode                              false
% 6.63/1.48  
% 6.63/1.48  ------ Instantiation Options
% 6.63/1.48  
% 6.63/1.48  --instantiation_flag                    true
% 6.63/1.48  --inst_sos_flag                         false
% 6.63/1.48  --inst_sos_phase                        true
% 6.63/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.63/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.63/1.48  --inst_lit_sel_side                     num_symb
% 6.63/1.48  --inst_solver_per_active                1400
% 6.63/1.48  --inst_solver_calls_frac                1.
% 6.63/1.48  --inst_passive_queue_type               priority_queues
% 6.63/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.63/1.48  --inst_passive_queues_freq              [25;2]
% 6.63/1.48  --inst_dismatching                      true
% 6.63/1.48  --inst_eager_unprocessed_to_passive     true
% 6.63/1.48  --inst_prop_sim_given                   true
% 6.63/1.48  --inst_prop_sim_new                     false
% 6.63/1.48  --inst_subs_new                         false
% 6.63/1.48  --inst_eq_res_simp                      false
% 6.63/1.48  --inst_subs_given                       false
% 6.63/1.48  --inst_orphan_elimination               true
% 6.63/1.48  --inst_learning_loop_flag               true
% 6.63/1.48  --inst_learning_start                   3000
% 6.63/1.48  --inst_learning_factor                  2
% 6.63/1.48  --inst_start_prop_sim_after_learn       3
% 6.63/1.48  --inst_sel_renew                        solver
% 6.63/1.48  --inst_lit_activity_flag                true
% 6.63/1.48  --inst_restr_to_given                   false
% 6.63/1.48  --inst_activity_threshold               500
% 6.63/1.48  --inst_out_proof                        true
% 6.63/1.48  
% 6.63/1.48  ------ Resolution Options
% 6.63/1.48  
% 6.63/1.48  --resolution_flag                       true
% 6.63/1.48  --res_lit_sel                           adaptive
% 6.63/1.48  --res_lit_sel_side                      none
% 6.63/1.48  --res_ordering                          kbo
% 6.63/1.48  --res_to_prop_solver                    active
% 6.63/1.48  --res_prop_simpl_new                    false
% 6.63/1.48  --res_prop_simpl_given                  true
% 6.63/1.48  --res_passive_queue_type                priority_queues
% 6.63/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.63/1.48  --res_passive_queues_freq               [15;5]
% 6.63/1.48  --res_forward_subs                      full
% 6.63/1.48  --res_backward_subs                     full
% 6.63/1.48  --res_forward_subs_resolution           true
% 6.63/1.48  --res_backward_subs_resolution          true
% 6.63/1.48  --res_orphan_elimination                true
% 6.63/1.48  --res_time_limit                        2.
% 6.63/1.48  --res_out_proof                         true
% 6.63/1.48  
% 6.63/1.48  ------ Superposition Options
% 6.63/1.48  
% 6.63/1.48  --superposition_flag                    true
% 6.63/1.48  --sup_passive_queue_type                priority_queues
% 6.63/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.63/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.63/1.48  --demod_completeness_check              fast
% 6.63/1.48  --demod_use_ground                      true
% 6.63/1.48  --sup_to_prop_solver                    passive
% 6.63/1.48  --sup_prop_simpl_new                    true
% 6.63/1.48  --sup_prop_simpl_given                  true
% 6.63/1.48  --sup_fun_splitting                     false
% 6.63/1.48  --sup_smt_interval                      50000
% 6.63/1.48  
% 6.63/1.48  ------ Superposition Simplification Setup
% 6.63/1.48  
% 6.63/1.48  --sup_indices_passive                   []
% 6.63/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.63/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.63/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.63/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.63/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.63/1.48  --sup_full_bw                           [BwDemod]
% 6.63/1.48  --sup_immed_triv                        [TrivRules]
% 6.63/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.63/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.63/1.48  --sup_immed_bw_main                     []
% 6.63/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.63/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.63/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.63/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.63/1.48  
% 6.63/1.48  ------ Combination Options
% 6.63/1.48  
% 6.63/1.48  --comb_res_mult                         3
% 6.63/1.48  --comb_sup_mult                         2
% 6.63/1.48  --comb_inst_mult                        10
% 6.63/1.48  
% 6.63/1.48  ------ Debug Options
% 6.63/1.48  
% 6.63/1.48  --dbg_backtrace                         false
% 6.63/1.48  --dbg_dump_prop_clauses                 false
% 6.63/1.48  --dbg_dump_prop_clauses_file            -
% 6.63/1.48  --dbg_out_stat                          false
% 6.63/1.48  ------ Parsing...
% 6.63/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.63/1.48  
% 6.63/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 6.63/1.48  
% 6.63/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.63/1.48  
% 6.63/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.63/1.48  ------ Proving...
% 6.63/1.48  ------ Problem Properties 
% 6.63/1.48  
% 6.63/1.48  
% 6.63/1.48  clauses                                 10
% 6.63/1.48  conjectures                             2
% 6.63/1.48  EPR                                     1
% 6.63/1.48  Horn                                    10
% 6.63/1.48  unary                                   7
% 6.63/1.48  binary                                  3
% 6.63/1.48  lits                                    13
% 6.63/1.48  lits eq                                 6
% 6.63/1.48  fd_pure                                 0
% 6.63/1.48  fd_pseudo                               0
% 6.63/1.48  fd_cond                                 0
% 6.63/1.48  fd_pseudo_cond                          0
% 6.63/1.48  AC symbols                              0
% 6.63/1.48  
% 6.63/1.48  ------ Schedule dynamic 5 is on 
% 6.63/1.48  
% 6.63/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.63/1.48  
% 6.63/1.48  
% 6.63/1.48  ------ 
% 6.63/1.48  Current options:
% 6.63/1.48  ------ 
% 6.63/1.48  
% 6.63/1.48  ------ Input Options
% 6.63/1.48  
% 6.63/1.48  --out_options                           all
% 6.63/1.48  --tptp_safe_out                         true
% 6.63/1.48  --problem_path                          ""
% 6.63/1.48  --include_path                          ""
% 6.63/1.48  --clausifier                            res/vclausify_rel
% 6.63/1.48  --clausifier_options                    --mode clausify
% 6.63/1.48  --stdin                                 false
% 6.63/1.48  --stats_out                             all
% 6.63/1.48  
% 6.63/1.48  ------ General Options
% 6.63/1.48  
% 6.63/1.48  --fof                                   false
% 6.63/1.48  --time_out_real                         305.
% 6.63/1.48  --time_out_virtual                      -1.
% 6.63/1.48  --symbol_type_check                     false
% 6.63/1.48  --clausify_out                          false
% 6.63/1.48  --sig_cnt_out                           false
% 6.63/1.48  --trig_cnt_out                          false
% 6.63/1.48  --trig_cnt_out_tolerance                1.
% 6.63/1.48  --trig_cnt_out_sk_spl                   false
% 6.63/1.48  --abstr_cl_out                          false
% 6.63/1.48  
% 6.63/1.48  ------ Global Options
% 6.63/1.48  
% 6.63/1.48  --schedule                              default
% 6.63/1.48  --add_important_lit                     false
% 6.63/1.48  --prop_solver_per_cl                    1000
% 6.63/1.48  --min_unsat_core                        false
% 6.63/1.48  --soft_assumptions                      false
% 6.63/1.48  --soft_lemma_size                       3
% 6.63/1.48  --prop_impl_unit_size                   0
% 6.63/1.48  --prop_impl_unit                        []
% 6.63/1.48  --share_sel_clauses                     true
% 6.63/1.48  --reset_solvers                         false
% 6.63/1.48  --bc_imp_inh                            [conj_cone]
% 6.63/1.48  --conj_cone_tolerance                   3.
% 6.63/1.48  --extra_neg_conj                        none
% 6.63/1.48  --large_theory_mode                     true
% 6.63/1.48  --prolific_symb_bound                   200
% 6.63/1.48  --lt_threshold                          2000
% 6.63/1.48  --clause_weak_htbl                      true
% 6.63/1.48  --gc_record_bc_elim                     false
% 6.63/1.48  
% 6.63/1.48  ------ Preprocessing Options
% 6.63/1.48  
% 6.63/1.48  --preprocessing_flag                    true
% 6.63/1.48  --time_out_prep_mult                    0.1
% 6.63/1.48  --splitting_mode                        input
% 6.63/1.48  --splitting_grd                         true
% 6.63/1.48  --splitting_cvd                         false
% 6.63/1.48  --splitting_cvd_svl                     false
% 6.63/1.48  --splitting_nvd                         32
% 6.63/1.48  --sub_typing                            true
% 6.63/1.48  --prep_gs_sim                           true
% 6.63/1.48  --prep_unflatten                        true
% 6.63/1.48  --prep_res_sim                          true
% 6.63/1.48  --prep_upred                            true
% 6.63/1.48  --prep_sem_filter                       exhaustive
% 6.63/1.48  --prep_sem_filter_out                   false
% 6.63/1.48  --pred_elim                             true
% 6.63/1.48  --res_sim_input                         true
% 6.63/1.48  --eq_ax_congr_red                       true
% 6.63/1.48  --pure_diseq_elim                       true
% 6.63/1.48  --brand_transform                       false
% 6.63/1.48  --non_eq_to_eq                          false
% 6.63/1.48  --prep_def_merge                        true
% 6.63/1.48  --prep_def_merge_prop_impl              false
% 6.63/1.48  --prep_def_merge_mbd                    true
% 6.63/1.48  --prep_def_merge_tr_red                 false
% 6.63/1.48  --prep_def_merge_tr_cl                  false
% 6.63/1.48  --smt_preprocessing                     true
% 6.63/1.48  --smt_ac_axioms                         fast
% 6.63/1.48  --preprocessed_out                      false
% 6.63/1.48  --preprocessed_stats                    false
% 6.63/1.48  
% 6.63/1.48  ------ Abstraction refinement Options
% 6.63/1.48  
% 6.63/1.48  --abstr_ref                             []
% 6.63/1.48  --abstr_ref_prep                        false
% 6.63/1.48  --abstr_ref_until_sat                   false
% 6.63/1.48  --abstr_ref_sig_restrict                funpre
% 6.63/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 6.63/1.48  --abstr_ref_under                       []
% 6.63/1.48  
% 6.63/1.48  ------ SAT Options
% 6.63/1.48  
% 6.63/1.48  --sat_mode                              false
% 6.63/1.48  --sat_fm_restart_options                ""
% 6.63/1.48  --sat_gr_def                            false
% 6.63/1.48  --sat_epr_types                         true
% 6.63/1.48  --sat_non_cyclic_types                  false
% 6.63/1.48  --sat_finite_models                     false
% 6.63/1.48  --sat_fm_lemmas                         false
% 6.63/1.48  --sat_fm_prep                           false
% 6.63/1.48  --sat_fm_uc_incr                        true
% 6.63/1.48  --sat_out_model                         small
% 6.63/1.48  --sat_out_clauses                       false
% 6.63/1.48  
% 6.63/1.48  ------ QBF Options
% 6.63/1.48  
% 6.63/1.48  --qbf_mode                              false
% 6.63/1.48  --qbf_elim_univ                         false
% 6.63/1.48  --qbf_dom_inst                          none
% 6.63/1.48  --qbf_dom_pre_inst                      false
% 6.63/1.48  --qbf_sk_in                             false
% 6.63/1.48  --qbf_pred_elim                         true
% 6.63/1.48  --qbf_split                             512
% 6.63/1.48  
% 6.63/1.48  ------ BMC1 Options
% 6.63/1.48  
% 6.63/1.48  --bmc1_incremental                      false
% 6.63/1.48  --bmc1_axioms                           reachable_all
% 6.63/1.48  --bmc1_min_bound                        0
% 6.63/1.48  --bmc1_max_bound                        -1
% 6.63/1.48  --bmc1_max_bound_default                -1
% 6.63/1.48  --bmc1_symbol_reachability              true
% 6.63/1.48  --bmc1_property_lemmas                  false
% 6.63/1.48  --bmc1_k_induction                      false
% 6.63/1.48  --bmc1_non_equiv_states                 false
% 6.63/1.48  --bmc1_deadlock                         false
% 6.63/1.48  --bmc1_ucm                              false
% 6.63/1.48  --bmc1_add_unsat_core                   none
% 6.63/1.48  --bmc1_unsat_core_children              false
% 6.63/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 6.63/1.48  --bmc1_out_stat                         full
% 6.63/1.48  --bmc1_ground_init                      false
% 6.63/1.48  --bmc1_pre_inst_next_state              false
% 6.63/1.48  --bmc1_pre_inst_state                   false
% 6.63/1.48  --bmc1_pre_inst_reach_state             false
% 6.63/1.48  --bmc1_out_unsat_core                   false
% 6.63/1.48  --bmc1_aig_witness_out                  false
% 6.63/1.48  --bmc1_verbose                          false
% 6.63/1.48  --bmc1_dump_clauses_tptp                false
% 6.63/1.48  --bmc1_dump_unsat_core_tptp             false
% 6.63/1.48  --bmc1_dump_file                        -
% 6.63/1.48  --bmc1_ucm_expand_uc_limit              128
% 6.63/1.48  --bmc1_ucm_n_expand_iterations          6
% 6.63/1.48  --bmc1_ucm_extend_mode                  1
% 6.63/1.48  --bmc1_ucm_init_mode                    2
% 6.63/1.48  --bmc1_ucm_cone_mode                    none
% 6.63/1.48  --bmc1_ucm_reduced_relation_type        0
% 6.63/1.48  --bmc1_ucm_relax_model                  4
% 6.63/1.48  --bmc1_ucm_full_tr_after_sat            true
% 6.63/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 6.63/1.48  --bmc1_ucm_layered_model                none
% 6.63/1.48  --bmc1_ucm_max_lemma_size               10
% 6.63/1.48  
% 6.63/1.48  ------ AIG Options
% 6.63/1.48  
% 6.63/1.48  --aig_mode                              false
% 6.63/1.48  
% 6.63/1.48  ------ Instantiation Options
% 6.63/1.48  
% 6.63/1.48  --instantiation_flag                    true
% 6.63/1.48  --inst_sos_flag                         false
% 6.63/1.48  --inst_sos_phase                        true
% 6.63/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.63/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.63/1.48  --inst_lit_sel_side                     none
% 6.63/1.48  --inst_solver_per_active                1400
% 6.63/1.48  --inst_solver_calls_frac                1.
% 6.63/1.48  --inst_passive_queue_type               priority_queues
% 6.63/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.63/1.48  --inst_passive_queues_freq              [25;2]
% 6.63/1.48  --inst_dismatching                      true
% 6.63/1.48  --inst_eager_unprocessed_to_passive     true
% 6.63/1.48  --inst_prop_sim_given                   true
% 6.63/1.48  --inst_prop_sim_new                     false
% 6.63/1.48  --inst_subs_new                         false
% 6.63/1.48  --inst_eq_res_simp                      false
% 6.63/1.48  --inst_subs_given                       false
% 6.63/1.48  --inst_orphan_elimination               true
% 6.63/1.48  --inst_learning_loop_flag               true
% 6.63/1.48  --inst_learning_start                   3000
% 6.63/1.48  --inst_learning_factor                  2
% 6.63/1.48  --inst_start_prop_sim_after_learn       3
% 6.63/1.48  --inst_sel_renew                        solver
% 6.63/1.48  --inst_lit_activity_flag                true
% 6.63/1.48  --inst_restr_to_given                   false
% 6.63/1.48  --inst_activity_threshold               500
% 6.63/1.48  --inst_out_proof                        true
% 6.63/1.48  
% 6.63/1.48  ------ Resolution Options
% 6.63/1.48  
% 6.63/1.48  --resolution_flag                       false
% 6.63/1.48  --res_lit_sel                           adaptive
% 6.63/1.48  --res_lit_sel_side                      none
% 6.63/1.48  --res_ordering                          kbo
% 6.63/1.48  --res_to_prop_solver                    active
% 6.63/1.48  --res_prop_simpl_new                    false
% 6.63/1.48  --res_prop_simpl_given                  true
% 6.63/1.48  --res_passive_queue_type                priority_queues
% 6.63/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.63/1.48  --res_passive_queues_freq               [15;5]
% 6.63/1.48  --res_forward_subs                      full
% 6.63/1.48  --res_backward_subs                     full
% 6.63/1.48  --res_forward_subs_resolution           true
% 6.63/1.48  --res_backward_subs_resolution          true
% 6.63/1.48  --res_orphan_elimination                true
% 6.63/1.48  --res_time_limit                        2.
% 6.63/1.48  --res_out_proof                         true
% 6.63/1.48  
% 6.63/1.48  ------ Superposition Options
% 6.63/1.48  
% 6.63/1.48  --superposition_flag                    true
% 6.63/1.48  --sup_passive_queue_type                priority_queues
% 6.63/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.63/1.48  --sup_passive_queues_freq               [8;1;4]
% 6.63/1.48  --demod_completeness_check              fast
% 6.63/1.48  --demod_use_ground                      true
% 6.63/1.48  --sup_to_prop_solver                    passive
% 6.63/1.48  --sup_prop_simpl_new                    true
% 6.63/1.48  --sup_prop_simpl_given                  true
% 6.63/1.48  --sup_fun_splitting                     false
% 6.63/1.48  --sup_smt_interval                      50000
% 6.63/1.48  
% 6.63/1.48  ------ Superposition Simplification Setup
% 6.63/1.48  
% 6.63/1.48  --sup_indices_passive                   []
% 6.63/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.63/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.63/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.63/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 6.63/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.63/1.48  --sup_full_bw                           [BwDemod]
% 6.63/1.48  --sup_immed_triv                        [TrivRules]
% 6.63/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.63/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.63/1.48  --sup_immed_bw_main                     []
% 6.63/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.63/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 6.63/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.63/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.63/1.48  
% 6.63/1.48  ------ Combination Options
% 6.63/1.48  
% 6.63/1.48  --comb_res_mult                         3
% 6.63/1.48  --comb_sup_mult                         2
% 6.63/1.48  --comb_inst_mult                        10
% 6.63/1.48  
% 6.63/1.48  ------ Debug Options
% 6.63/1.48  
% 6.63/1.48  --dbg_backtrace                         false
% 6.63/1.48  --dbg_dump_prop_clauses                 false
% 6.63/1.48  --dbg_dump_prop_clauses_file            -
% 6.63/1.48  --dbg_out_stat                          false
% 6.63/1.48  
% 6.63/1.48  
% 6.63/1.48  
% 6.63/1.48  
% 6.63/1.48  ------ Proving...
% 6.63/1.48  
% 6.63/1.48  
% 6.63/1.48  % SZS status Theorem for theBenchmark.p
% 6.63/1.48  
% 6.63/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 6.63/1.48  
% 6.63/1.48  fof(f3,axiom,(
% 6.63/1.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 6.63/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.63/1.48  
% 6.63/1.48  fof(f19,plain,(
% 6.63/1.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.63/1.48    inference(cnf_transformation,[],[f3])).
% 6.63/1.48  
% 6.63/1.48  fof(f5,axiom,(
% 6.63/1.48    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 6.63/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.63/1.48  
% 6.63/1.48  fof(f21,plain,(
% 6.63/1.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 6.63/1.48    inference(cnf_transformation,[],[f5])).
% 6.63/1.48  
% 6.63/1.48  fof(f9,conjecture,(
% 6.63/1.48    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 6.63/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.63/1.48  
% 6.63/1.48  fof(f10,negated_conjecture,(
% 6.63/1.48    ~! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X1,X2)) => r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 6.63/1.48    inference(negated_conjecture,[],[f9])).
% 6.63/1.48  
% 6.63/1.48  fof(f12,plain,(
% 6.63/1.48    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2)))),
% 6.63/1.48    inference(ennf_transformation,[],[f10])).
% 6.63/1.48  
% 6.63/1.48  fof(f14,plain,(
% 6.63/1.48    ? [X0,X1,X2] : (~r1_xboole_0(X1,k4_xboole_0(X0,X2)) & r1_xboole_0(X0,k4_xboole_0(X1,X2))) => (~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 6.63/1.48    introduced(choice_axiom,[])).
% 6.63/1.48  
% 6.63/1.48  fof(f15,plain,(
% 6.63/1.48    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) & r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 6.63/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 6.63/1.48  
% 6.63/1.48  fof(f25,plain,(
% 6.63/1.48    r1_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 6.63/1.48    inference(cnf_transformation,[],[f15])).
% 6.63/1.48  
% 6.63/1.48  fof(f1,axiom,(
% 6.63/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 6.63/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.63/1.48  
% 6.63/1.48  fof(f13,plain,(
% 6.63/1.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 6.63/1.48    inference(nnf_transformation,[],[f1])).
% 6.63/1.48  
% 6.63/1.48  fof(f16,plain,(
% 6.63/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 6.63/1.48    inference(cnf_transformation,[],[f13])).
% 6.63/1.48  
% 6.63/1.48  fof(f7,axiom,(
% 6.63/1.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.63/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.63/1.48  
% 6.63/1.48  fof(f23,plain,(
% 6.63/1.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.63/1.48    inference(cnf_transformation,[],[f7])).
% 6.63/1.48  
% 6.63/1.48  fof(f28,plain,(
% 6.63/1.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 6.63/1.48    inference(definition_unfolding,[],[f16,f23])).
% 6.63/1.48  
% 6.63/1.48  fof(f6,axiom,(
% 6.63/1.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.63/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.63/1.48  
% 6.63/1.48  fof(f22,plain,(
% 6.63/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.63/1.48    inference(cnf_transformation,[],[f6])).
% 6.63/1.48  
% 6.63/1.48  fof(f29,plain,(
% 6.63/1.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 6.63/1.48    inference(definition_unfolding,[],[f22,f23])).
% 6.63/1.48  
% 6.63/1.48  fof(f4,axiom,(
% 6.63/1.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 6.63/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.63/1.48  
% 6.63/1.48  fof(f20,plain,(
% 6.63/1.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.63/1.48    inference(cnf_transformation,[],[f4])).
% 6.63/1.48  
% 6.63/1.48  fof(f8,axiom,(
% 6.63/1.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 6.63/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.63/1.48  
% 6.63/1.48  fof(f24,plain,(
% 6.63/1.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 6.63/1.48    inference(cnf_transformation,[],[f8])).
% 6.63/1.48  
% 6.63/1.48  fof(f2,axiom,(
% 6.63/1.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 6.63/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.63/1.48  
% 6.63/1.48  fof(f11,plain,(
% 6.63/1.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 6.63/1.48    inference(ennf_transformation,[],[f2])).
% 6.63/1.48  
% 6.63/1.48  fof(f18,plain,(
% 6.63/1.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 6.63/1.48    inference(cnf_transformation,[],[f11])).
% 6.63/1.48  
% 6.63/1.48  fof(f26,plain,(
% 6.63/1.48    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK2))),
% 6.63/1.48    inference(cnf_transformation,[],[f15])).
% 6.63/1.48  
% 6.63/1.48  cnf(c_3,plain,
% 6.63/1.48      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 6.63/1.48      inference(cnf_transformation,[],[f19]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_5,plain,
% 6.63/1.48      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 6.63/1.48      inference(cnf_transformation,[],[f21]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_483,plain,
% 6.63/1.48      ( k2_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) = k2_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 6.63/1.48      inference(superposition,[status(thm)],[c_5,c_3]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_9,negated_conjecture,
% 6.63/1.48      ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
% 6.63/1.48      inference(cnf_transformation,[],[f25]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_266,plain,
% 6.63/1.48      ( r1_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = iProver_top ),
% 6.63/1.48      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_1,plain,
% 6.63/1.48      ( ~ r1_xboole_0(X0,X1)
% 6.63/1.48      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0 ),
% 6.63/1.48      inference(cnf_transformation,[],[f28]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_270,plain,
% 6.63/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_xboole_0
% 6.63/1.48      | r1_xboole_0(X0,X1) != iProver_top ),
% 6.63/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_2235,plain,
% 6.63/1.48      ( k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) = k1_xboole_0 ),
% 6.63/1.48      inference(superposition,[status(thm)],[c_266,c_270]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_6,plain,
% 6.63/1.48      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 6.63/1.48      inference(cnf_transformation,[],[f29]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_2647,plain,
% 6.63/1.48      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK0,k1_xboole_0) ),
% 6.63/1.48      inference(superposition,[status(thm)],[c_2235,c_6]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_4,plain,
% 6.63/1.48      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 6.63/1.48      inference(cnf_transformation,[],[f20]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_2660,plain,
% 6.63/1.48      ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = sK0 ),
% 6.63/1.48      inference(demodulation,[status(thm)],[c_2647,c_4]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_2769,plain,
% 6.63/1.48      ( k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),X0)) = k4_xboole_0(sK0,X0) ),
% 6.63/1.48      inference(superposition,[status(thm)],[c_2660,c_5]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_4658,plain,
% 6.63/1.48      ( k4_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,sK2),k4_xboole_0(X0,X1))) ),
% 6.63/1.48      inference(superposition,[status(thm)],[c_483,c_2769]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_4664,plain,
% 6.63/1.48      ( k4_xboole_0(sK0,k4_xboole_0(X0,k2_xboole_0(X1,k4_xboole_0(sK1,sK2)))) = k4_xboole_0(sK0,k4_xboole_0(X0,X1)) ),
% 6.63/1.48      inference(demodulation,[status(thm)],[c_4658,c_2769]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_19926,plain,
% 6.63/1.48      ( k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ),
% 6.63/1.48      inference(superposition,[status(thm)],[c_4664,c_6]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_19978,plain,
% 6.63/1.48      ( k4_xboole_0(sK0,k2_xboole_0(X0,k4_xboole_0(sK1,sK2))) = k4_xboole_0(sK0,X0) ),
% 6.63/1.48      inference(demodulation,[status(thm)],[c_19926,c_6]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_24777,plain,
% 6.63/1.48      ( k4_xboole_0(sK0,k2_xboole_0(sK2,sK1)) = k4_xboole_0(sK0,sK2) ),
% 6.63/1.48      inference(superposition,[status(thm)],[c_3,c_19978]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_7,plain,
% 6.63/1.48      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 6.63/1.48      inference(cnf_transformation,[],[f24]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_268,plain,
% 6.63/1.48      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 6.63/1.48      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_482,plain,
% 6.63/1.48      ( r1_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),X2) = iProver_top ),
% 6.63/1.48      inference(superposition,[status(thm)],[c_5,c_268]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_25051,plain,
% 6.63/1.48      ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) = iProver_top ),
% 6.63/1.48      inference(superposition,[status(thm)],[c_24777,c_482]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_2,plain,
% 6.63/1.48      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 6.63/1.48      inference(cnf_transformation,[],[f18]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_427,plain,
% 6.63/1.48      ( ~ r1_xboole_0(k4_xboole_0(sK0,sK2),sK1)
% 6.63/1.48      | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
% 6.63/1.48      inference(instantiation,[status(thm)],[c_2]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_428,plain,
% 6.63/1.48      ( r1_xboole_0(k4_xboole_0(sK0,sK2),sK1) != iProver_top
% 6.63/1.48      | r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = iProver_top ),
% 6.63/1.48      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_8,negated_conjecture,
% 6.63/1.48      ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) ),
% 6.63/1.48      inference(cnf_transformation,[],[f26]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(c_11,plain,
% 6.63/1.48      ( r1_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != iProver_top ),
% 6.63/1.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.63/1.48  
% 6.63/1.48  cnf(contradiction,plain,
% 6.63/1.48      ( $false ),
% 6.63/1.48      inference(minisat,[status(thm)],[c_25051,c_428,c_11]) ).
% 6.63/1.48  
% 6.63/1.48  
% 6.63/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 6.63/1.48  
% 6.63/1.48  ------                               Statistics
% 6.63/1.48  
% 6.63/1.48  ------ General
% 6.63/1.48  
% 6.63/1.48  abstr_ref_over_cycles:                  0
% 6.63/1.48  abstr_ref_under_cycles:                 0
% 6.63/1.48  gc_basic_clause_elim:                   0
% 6.63/1.48  forced_gc_time:                         0
% 6.63/1.48  parsing_time:                           0.009
% 6.63/1.48  unif_index_cands_time:                  0.
% 6.63/1.48  unif_index_add_time:                    0.
% 6.63/1.48  orderings_time:                         0.
% 6.63/1.48  out_proof_time:                         0.006
% 6.63/1.48  total_time:                             0.678
% 6.63/1.48  num_of_symbols:                         38
% 6.63/1.48  num_of_terms:                           29075
% 6.63/1.48  
% 6.63/1.48  ------ Preprocessing
% 6.63/1.48  
% 6.63/1.48  num_of_splits:                          0
% 6.63/1.48  num_of_split_atoms:                     0
% 6.63/1.48  num_of_reused_defs:                     0
% 6.63/1.48  num_eq_ax_congr_red:                    2
% 6.63/1.48  num_of_sem_filtered_clauses:            1
% 6.63/1.48  num_of_subtypes:                        0
% 6.63/1.48  monotx_restored_types:                  0
% 6.63/1.48  sat_num_of_epr_types:                   0
% 6.63/1.48  sat_num_of_non_cyclic_types:            0
% 6.63/1.48  sat_guarded_non_collapsed_types:        0
% 6.63/1.48  num_pure_diseq_elim:                    0
% 6.63/1.48  simp_replaced_by:                       0
% 6.63/1.48  res_preprocessed:                       41
% 6.63/1.48  prep_upred:                             0
% 6.63/1.48  prep_unflattend:                        0
% 6.63/1.48  smt_new_axioms:                         0
% 6.63/1.48  pred_elim_cands:                        1
% 6.63/1.48  pred_elim:                              0
% 6.63/1.48  pred_elim_cl:                           0
% 6.63/1.48  pred_elim_cycles:                       1
% 6.63/1.48  merged_defs:                            6
% 6.63/1.48  merged_defs_ncl:                        0
% 6.63/1.48  bin_hyper_res:                          6
% 6.63/1.48  prep_cycles:                            3
% 6.63/1.48  pred_elim_time:                         0.
% 6.63/1.48  splitting_time:                         0.
% 6.63/1.48  sem_filter_time:                        0.
% 6.63/1.48  monotx_time:                            0.
% 6.63/1.48  subtype_inf_time:                       0.
% 6.63/1.48  
% 6.63/1.48  ------ Problem properties
% 6.63/1.48  
% 6.63/1.48  clauses:                                10
% 6.63/1.48  conjectures:                            2
% 6.63/1.48  epr:                                    1
% 6.63/1.48  horn:                                   10
% 6.63/1.48  ground:                                 2
% 6.63/1.48  unary:                                  7
% 6.63/1.48  binary:                                 3
% 6.63/1.48  lits:                                   13
% 6.63/1.48  lits_eq:                                6
% 6.63/1.48  fd_pure:                                0
% 6.63/1.48  fd_pseudo:                              0
% 6.63/1.48  fd_cond:                                0
% 6.63/1.48  fd_pseudo_cond:                         0
% 6.63/1.48  ac_symbols:                             0
% 6.63/1.48  
% 6.63/1.48  ------ Propositional Solver
% 6.63/1.48  
% 6.63/1.48  prop_solver_calls:                      30
% 6.63/1.48  prop_fast_solver_calls:                 310
% 6.63/1.48  smt_solver_calls:                       0
% 6.63/1.48  smt_fast_solver_calls:                  0
% 6.63/1.48  prop_num_of_clauses:                    8958
% 6.63/1.48  prop_preprocess_simplified:             12313
% 6.63/1.48  prop_fo_subsumed:                       0
% 6.63/1.48  prop_solver_time:                       0.
% 6.63/1.48  smt_solver_time:                        0.
% 6.63/1.48  smt_fast_solver_time:                   0.
% 6.63/1.48  prop_fast_solver_time:                  0.
% 6.63/1.48  prop_unsat_core_time:                   0.001
% 6.63/1.48  
% 6.63/1.48  ------ QBF
% 6.63/1.48  
% 6.63/1.48  qbf_q_res:                              0
% 6.63/1.48  qbf_num_tautologies:                    0
% 6.63/1.48  qbf_prep_cycles:                        0
% 6.63/1.48  
% 6.63/1.48  ------ BMC1
% 6.63/1.48  
% 6.63/1.48  bmc1_current_bound:                     -1
% 6.63/1.48  bmc1_last_solved_bound:                 -1
% 6.63/1.48  bmc1_unsat_core_size:                   -1
% 6.63/1.48  bmc1_unsat_core_parents_size:           -1
% 6.63/1.48  bmc1_merge_next_fun:                    0
% 6.63/1.48  bmc1_unsat_core_clauses_time:           0.
% 6.63/1.48  
% 6.63/1.48  ------ Instantiation
% 6.63/1.48  
% 6.63/1.48  inst_num_of_clauses:                    2453
% 6.63/1.48  inst_num_in_passive:                    1500
% 6.63/1.48  inst_num_in_active:                     789
% 6.63/1.48  inst_num_in_unprocessed:                167
% 6.63/1.48  inst_num_of_loops:                      820
% 6.63/1.48  inst_num_of_learning_restarts:          0
% 6.63/1.48  inst_num_moves_active_passive:          26
% 6.63/1.48  inst_lit_activity:                      0
% 6.63/1.48  inst_lit_activity_moves:                0
% 6.63/1.48  inst_num_tautologies:                   0
% 6.63/1.48  inst_num_prop_implied:                  0
% 6.63/1.48  inst_num_existing_simplified:           0
% 6.63/1.48  inst_num_eq_res_simplified:             0
% 6.63/1.48  inst_num_child_elim:                    0
% 6.63/1.48  inst_num_of_dismatching_blockings:      716
% 6.63/1.48  inst_num_of_non_proper_insts:           2056
% 6.63/1.48  inst_num_of_duplicates:                 0
% 6.63/1.48  inst_inst_num_from_inst_to_res:         0
% 6.63/1.48  inst_dismatching_checking_time:         0.
% 6.63/1.48  
% 6.63/1.48  ------ Resolution
% 6.63/1.48  
% 6.63/1.48  res_num_of_clauses:                     0
% 6.63/1.48  res_num_in_passive:                     0
% 6.63/1.48  res_num_in_active:                      0
% 6.63/1.48  res_num_of_loops:                       44
% 6.63/1.48  res_forward_subset_subsumed:            163
% 6.63/1.48  res_backward_subset_subsumed:           10
% 6.63/1.48  res_forward_subsumed:                   0
% 6.63/1.48  res_backward_subsumed:                  0
% 6.63/1.48  res_forward_subsumption_resolution:     0
% 6.63/1.48  res_backward_subsumption_resolution:    0
% 6.63/1.48  res_clause_to_clause_subsumption:       15294
% 6.63/1.48  res_orphan_elimination:                 0
% 6.63/1.48  res_tautology_del:                      149
% 6.63/1.48  res_num_eq_res_simplified:              0
% 6.63/1.48  res_num_sel_changes:                    0
% 6.63/1.48  res_moves_from_active_to_pass:          0
% 6.63/1.48  
% 6.63/1.48  ------ Superposition
% 6.63/1.48  
% 6.63/1.48  sup_time_total:                         0.
% 6.63/1.48  sup_time_generating:                    0.
% 6.63/1.48  sup_time_sim_full:                      0.
% 6.63/1.48  sup_time_sim_immed:                     0.
% 6.63/1.48  
% 6.63/1.48  sup_num_of_clauses:                     1548
% 6.63/1.48  sup_num_in_active:                      136
% 6.63/1.48  sup_num_in_passive:                     1412
% 6.63/1.48  sup_num_of_loops:                       162
% 6.63/1.48  sup_fw_superposition:                   2149
% 6.63/1.48  sup_bw_superposition:                   2560
% 6.63/1.48  sup_immediate_simplified:               2207
% 6.63/1.48  sup_given_eliminated:                   3
% 6.63/1.48  comparisons_done:                       0
% 6.63/1.48  comparisons_avoided:                    0
% 6.63/1.48  
% 6.63/1.48  ------ Simplifications
% 6.63/1.48  
% 6.63/1.48  
% 6.63/1.48  sim_fw_subset_subsumed:                 4
% 6.63/1.48  sim_bw_subset_subsumed:                 0
% 6.63/1.48  sim_fw_subsumed:                        951
% 6.63/1.48  sim_bw_subsumed:                        22
% 6.63/1.48  sim_fw_subsumption_res:                 0
% 6.63/1.48  sim_bw_subsumption_res:                 0
% 6.63/1.48  sim_tautology_del:                      0
% 6.63/1.48  sim_eq_tautology_del:                   267
% 6.63/1.48  sim_eq_res_simp:                        10
% 6.63/1.48  sim_fw_demodulated:                     1117
% 6.63/1.48  sim_bw_demodulated:                     39
% 6.63/1.48  sim_light_normalised:                   744
% 6.63/1.48  sim_joinable_taut:                      0
% 6.63/1.48  sim_joinable_simp:                      0
% 6.63/1.48  sim_ac_normalised:                      0
% 6.63/1.48  sim_smt_subsumption:                    0
% 6.63/1.48  
%------------------------------------------------------------------------------
