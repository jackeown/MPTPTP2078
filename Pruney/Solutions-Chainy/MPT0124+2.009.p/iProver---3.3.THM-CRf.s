%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:26:13 EST 2020

% Result     : Theorem 19.78s
% Output     : CNFRefutation 19.78s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 136 expanded)
%              Number of clauses        :   35 (  60 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 191 expanded)
%              Number of equality atoms :   67 ( 137 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
     => k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X2,X1)
       => k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) != k4_xboole_0(X0,X2)
      & r1_tarski(X2,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) != k4_xboole_0(X0,X2)
        & r1_tarski(X2,X1) )
   => ( k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2)
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2)
    & r1_tarski(sK2,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).

fof(f39,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f43,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(sK0,sK2) ),
    inference(definition_unfolding,[],[f39,f34])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f34,f34])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f38,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_96,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_95,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1558,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_96,c_95])).

cnf(c_97,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_7367,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X1,X3) = k4_xboole_0(X0,X2) ),
    inference(resolution,[status(thm)],[c_1558,c_97])).

cnf(c_8,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_3216,plain,
    ( X0 != k4_xboole_0(X1,k4_xboole_0(X2,X3))
    | k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) = X0 ),
    inference(resolution,[status(thm)],[c_8,c_96])).

cnf(c_11,negated_conjecture,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_21092,plain,
    ( k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(resolution,[status(thm)],[c_3216,c_11])).

cnf(c_76000,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK2
    | sK0 != sK0 ),
    inference(resolution,[status(thm)],[c_7367,c_21092])).

cnf(c_76001,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_76000])).

cnf(c_4,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_247,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_250,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2083,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_247,c_250])).

cnf(c_5,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_47994,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[status(thm)],[c_2083,c_5])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_501,plain,
    ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_5,c_0])).

cnf(c_5160,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X2,X0),k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
    inference(superposition,[status(thm)],[c_501,c_8])).

cnf(c_48008,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X2),X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X2),X0))) ),
    inference(superposition,[status(thm)],[c_2083,c_5160])).

cnf(c_48052,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X2),X0))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_48008,c_2083])).

cnf(c_48094,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(demodulation,[status(thm)],[c_47994,c_48052])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_245,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1482,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_247,c_245])).

cnf(c_17377,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_1482,c_8])).

cnf(c_48113,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(demodulation,[status(thm)],[c_48094,c_8,c_2083,c_17377])).

cnf(c_12,negated_conjecture,
    ( r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_242,plain,
    ( r1_tarski(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1485,plain,
    ( k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = sK1 ),
    inference(superposition,[status(thm)],[c_242,c_245])).

cnf(c_24746,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[status(thm)],[c_1485,c_5])).

cnf(c_48493,plain,
    ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_48113,c_24746])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_76001,c_48493])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:28:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.78/3.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.78/3.00  
% 19.78/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.78/3.00  
% 19.78/3.00  ------  iProver source info
% 19.78/3.00  
% 19.78/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.78/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.78/3.00  git: non_committed_changes: false
% 19.78/3.00  git: last_make_outside_of_git: false
% 19.78/3.00  
% 19.78/3.00  ------ 
% 19.78/3.00  
% 19.78/3.00  ------ Input Options
% 19.78/3.00  
% 19.78/3.00  --out_options                           all
% 19.78/3.00  --tptp_safe_out                         true
% 19.78/3.00  --problem_path                          ""
% 19.78/3.00  --include_path                          ""
% 19.78/3.00  --clausifier                            res/vclausify_rel
% 19.78/3.00  --clausifier_options                    --mode clausify
% 19.78/3.00  --stdin                                 false
% 19.78/3.00  --stats_out                             sel
% 19.78/3.00  
% 19.78/3.00  ------ General Options
% 19.78/3.00  
% 19.78/3.00  --fof                                   false
% 19.78/3.00  --time_out_real                         604.99
% 19.78/3.00  --time_out_virtual                      -1.
% 19.78/3.00  --symbol_type_check                     false
% 19.78/3.00  --clausify_out                          false
% 19.78/3.00  --sig_cnt_out                           false
% 19.78/3.00  --trig_cnt_out                          false
% 19.78/3.00  --trig_cnt_out_tolerance                1.
% 19.78/3.00  --trig_cnt_out_sk_spl                   false
% 19.78/3.00  --abstr_cl_out                          false
% 19.78/3.00  
% 19.78/3.00  ------ Global Options
% 19.78/3.00  
% 19.78/3.00  --schedule                              none
% 19.78/3.00  --add_important_lit                     false
% 19.78/3.00  --prop_solver_per_cl                    1000
% 19.78/3.00  --min_unsat_core                        false
% 19.78/3.00  --soft_assumptions                      false
% 19.78/3.00  --soft_lemma_size                       3
% 19.78/3.00  --prop_impl_unit_size                   0
% 19.78/3.00  --prop_impl_unit                        []
% 19.78/3.00  --share_sel_clauses                     true
% 19.78/3.00  --reset_solvers                         false
% 19.78/3.00  --bc_imp_inh                            [conj_cone]
% 19.78/3.00  --conj_cone_tolerance                   3.
% 19.78/3.00  --extra_neg_conj                        none
% 19.78/3.00  --large_theory_mode                     true
% 19.78/3.00  --prolific_symb_bound                   200
% 19.78/3.00  --lt_threshold                          2000
% 19.78/3.00  --clause_weak_htbl                      true
% 19.78/3.00  --gc_record_bc_elim                     false
% 19.78/3.00  
% 19.78/3.00  ------ Preprocessing Options
% 19.78/3.00  
% 19.78/3.00  --preprocessing_flag                    true
% 19.78/3.00  --time_out_prep_mult                    0.1
% 19.78/3.00  --splitting_mode                        input
% 19.78/3.00  --splitting_grd                         true
% 19.78/3.00  --splitting_cvd                         false
% 19.78/3.00  --splitting_cvd_svl                     false
% 19.78/3.00  --splitting_nvd                         32
% 19.78/3.00  --sub_typing                            true
% 19.78/3.00  --prep_gs_sim                           false
% 19.78/3.00  --prep_unflatten                        true
% 19.78/3.00  --prep_res_sim                          true
% 19.78/3.00  --prep_upred                            true
% 19.78/3.00  --prep_sem_filter                       exhaustive
% 19.78/3.00  --prep_sem_filter_out                   false
% 19.78/3.00  --pred_elim                             false
% 19.78/3.00  --res_sim_input                         true
% 19.78/3.00  --eq_ax_congr_red                       true
% 19.78/3.00  --pure_diseq_elim                       true
% 19.78/3.00  --brand_transform                       false
% 19.78/3.00  --non_eq_to_eq                          false
% 19.78/3.00  --prep_def_merge                        true
% 19.78/3.00  --prep_def_merge_prop_impl              false
% 19.78/3.00  --prep_def_merge_mbd                    true
% 19.78/3.00  --prep_def_merge_tr_red                 false
% 19.78/3.00  --prep_def_merge_tr_cl                  false
% 19.78/3.00  --smt_preprocessing                     true
% 19.78/3.00  --smt_ac_axioms                         fast
% 19.78/3.00  --preprocessed_out                      false
% 19.78/3.00  --preprocessed_stats                    false
% 19.78/3.00  
% 19.78/3.00  ------ Abstraction refinement Options
% 19.78/3.00  
% 19.78/3.00  --abstr_ref                             []
% 19.78/3.00  --abstr_ref_prep                        false
% 19.78/3.00  --abstr_ref_until_sat                   false
% 19.78/3.00  --abstr_ref_sig_restrict                funpre
% 19.78/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.78/3.00  --abstr_ref_under                       []
% 19.78/3.00  
% 19.78/3.00  ------ SAT Options
% 19.78/3.00  
% 19.78/3.00  --sat_mode                              false
% 19.78/3.00  --sat_fm_restart_options                ""
% 19.78/3.00  --sat_gr_def                            false
% 19.78/3.00  --sat_epr_types                         true
% 19.78/3.00  --sat_non_cyclic_types                  false
% 19.78/3.00  --sat_finite_models                     false
% 19.78/3.00  --sat_fm_lemmas                         false
% 19.78/3.00  --sat_fm_prep                           false
% 19.78/3.01  --sat_fm_uc_incr                        true
% 19.78/3.01  --sat_out_model                         small
% 19.78/3.01  --sat_out_clauses                       false
% 19.78/3.01  
% 19.78/3.01  ------ QBF Options
% 19.78/3.01  
% 19.78/3.01  --qbf_mode                              false
% 19.78/3.01  --qbf_elim_univ                         false
% 19.78/3.01  --qbf_dom_inst                          none
% 19.78/3.01  --qbf_dom_pre_inst                      false
% 19.78/3.01  --qbf_sk_in                             false
% 19.78/3.01  --qbf_pred_elim                         true
% 19.78/3.01  --qbf_split                             512
% 19.78/3.01  
% 19.78/3.01  ------ BMC1 Options
% 19.78/3.01  
% 19.78/3.01  --bmc1_incremental                      false
% 19.78/3.01  --bmc1_axioms                           reachable_all
% 19.78/3.01  --bmc1_min_bound                        0
% 19.78/3.01  --bmc1_max_bound                        -1
% 19.78/3.01  --bmc1_max_bound_default                -1
% 19.78/3.01  --bmc1_symbol_reachability              true
% 19.78/3.01  --bmc1_property_lemmas                  false
% 19.78/3.01  --bmc1_k_induction                      false
% 19.78/3.01  --bmc1_non_equiv_states                 false
% 19.78/3.01  --bmc1_deadlock                         false
% 19.78/3.01  --bmc1_ucm                              false
% 19.78/3.01  --bmc1_add_unsat_core                   none
% 19.78/3.01  --bmc1_unsat_core_children              false
% 19.78/3.01  --bmc1_unsat_core_extrapolate_axioms    false
% 19.78/3.01  --bmc1_out_stat                         full
% 19.78/3.01  --bmc1_ground_init                      false
% 19.78/3.01  --bmc1_pre_inst_next_state              false
% 19.78/3.01  --bmc1_pre_inst_state                   false
% 19.78/3.01  --bmc1_pre_inst_reach_state             false
% 19.78/3.01  --bmc1_out_unsat_core                   false
% 19.78/3.01  --bmc1_aig_witness_out                  false
% 19.78/3.01  --bmc1_verbose                          false
% 19.78/3.01  --bmc1_dump_clauses_tptp                false
% 19.78/3.01  --bmc1_dump_unsat_core_tptp             false
% 19.78/3.01  --bmc1_dump_file                        -
% 19.78/3.01  --bmc1_ucm_expand_uc_limit              128
% 19.78/3.01  --bmc1_ucm_n_expand_iterations          6
% 19.78/3.01  --bmc1_ucm_extend_mode                  1
% 19.78/3.01  --bmc1_ucm_init_mode                    2
% 19.78/3.01  --bmc1_ucm_cone_mode                    none
% 19.78/3.01  --bmc1_ucm_reduced_relation_type        0
% 19.78/3.01  --bmc1_ucm_relax_model                  4
% 19.78/3.01  --bmc1_ucm_full_tr_after_sat            true
% 19.78/3.01  --bmc1_ucm_expand_neg_assumptions       false
% 19.78/3.01  --bmc1_ucm_layered_model                none
% 19.78/3.01  --bmc1_ucm_max_lemma_size               10
% 19.78/3.01  
% 19.78/3.01  ------ AIG Options
% 19.78/3.01  
% 19.78/3.01  --aig_mode                              false
% 19.78/3.01  
% 19.78/3.01  ------ Instantiation Options
% 19.78/3.01  
% 19.78/3.01  --instantiation_flag                    true
% 19.78/3.01  --inst_sos_flag                         false
% 19.78/3.01  --inst_sos_phase                        true
% 19.78/3.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.78/3.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.78/3.01  --inst_lit_sel_side                     num_symb
% 19.78/3.01  --inst_solver_per_active                1400
% 19.78/3.01  --inst_solver_calls_frac                1.
% 19.78/3.01  --inst_passive_queue_type               priority_queues
% 19.78/3.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.78/3.01  --inst_passive_queues_freq              [25;2]
% 19.78/3.01  --inst_dismatching                      true
% 19.78/3.01  --inst_eager_unprocessed_to_passive     true
% 19.78/3.01  --inst_prop_sim_given                   true
% 19.78/3.01  --inst_prop_sim_new                     false
% 19.78/3.01  --inst_subs_new                         false
% 19.78/3.01  --inst_eq_res_simp                      false
% 19.78/3.01  --inst_subs_given                       false
% 19.78/3.01  --inst_orphan_elimination               true
% 19.78/3.01  --inst_learning_loop_flag               true
% 19.78/3.01  --inst_learning_start                   3000
% 19.78/3.01  --inst_learning_factor                  2
% 19.78/3.01  --inst_start_prop_sim_after_learn       3
% 19.78/3.01  --inst_sel_renew                        solver
% 19.78/3.01  --inst_lit_activity_flag                true
% 19.78/3.01  --inst_restr_to_given                   false
% 19.78/3.01  --inst_activity_threshold               500
% 19.78/3.01  --inst_out_proof                        true
% 19.78/3.01  
% 19.78/3.01  ------ Resolution Options
% 19.78/3.01  
% 19.78/3.01  --resolution_flag                       true
% 19.78/3.01  --res_lit_sel                           adaptive
% 19.78/3.01  --res_lit_sel_side                      none
% 19.78/3.01  --res_ordering                          kbo
% 19.78/3.01  --res_to_prop_solver                    active
% 19.78/3.01  --res_prop_simpl_new                    false
% 19.78/3.01  --res_prop_simpl_given                  true
% 19.78/3.01  --res_passive_queue_type                priority_queues
% 19.78/3.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.78/3.01  --res_passive_queues_freq               [15;5]
% 19.78/3.01  --res_forward_subs                      full
% 19.78/3.01  --res_backward_subs                     full
% 19.78/3.01  --res_forward_subs_resolution           true
% 19.78/3.01  --res_backward_subs_resolution          true
% 19.78/3.01  --res_orphan_elimination                true
% 19.78/3.01  --res_time_limit                        2.
% 19.78/3.01  --res_out_proof                         true
% 19.78/3.01  
% 19.78/3.01  ------ Superposition Options
% 19.78/3.01  
% 19.78/3.01  --superposition_flag                    true
% 19.78/3.01  --sup_passive_queue_type                priority_queues
% 19.78/3.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.78/3.01  --sup_passive_queues_freq               [1;4]
% 19.78/3.01  --demod_completeness_check              fast
% 19.78/3.01  --demod_use_ground                      true
% 19.78/3.01  --sup_to_prop_solver                    passive
% 19.78/3.01  --sup_prop_simpl_new                    true
% 19.78/3.01  --sup_prop_simpl_given                  true
% 19.78/3.01  --sup_fun_splitting                     false
% 19.78/3.01  --sup_smt_interval                      50000
% 19.78/3.01  
% 19.78/3.01  ------ Superposition Simplification Setup
% 19.78/3.01  
% 19.78/3.01  --sup_indices_passive                   []
% 19.78/3.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.78/3.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.78/3.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.78/3.01  --sup_full_triv                         [TrivRules;PropSubs]
% 19.78/3.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.78/3.01  --sup_full_bw                           [BwDemod]
% 19.78/3.01  --sup_immed_triv                        [TrivRules]
% 19.78/3.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.78/3.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.78/3.01  --sup_immed_bw_main                     []
% 19.78/3.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.78/3.01  --sup_input_triv                        [Unflattening;TrivRules]
% 19.78/3.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.78/3.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.78/3.01  
% 19.78/3.01  ------ Combination Options
% 19.78/3.01  
% 19.78/3.01  --comb_res_mult                         3
% 19.78/3.01  --comb_sup_mult                         2
% 19.78/3.01  --comb_inst_mult                        10
% 19.78/3.01  
% 19.78/3.01  ------ Debug Options
% 19.78/3.01  
% 19.78/3.01  --dbg_backtrace                         false
% 19.78/3.01  --dbg_dump_prop_clauses                 false
% 19.78/3.01  --dbg_dump_prop_clauses_file            -
% 19.78/3.01  --dbg_out_stat                          false
% 19.78/3.01  ------ Parsing...
% 19.78/3.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.78/3.01  
% 19.78/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.78/3.01  
% 19.78/3.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.78/3.01  
% 19.78/3.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.78/3.01  ------ Proving...
% 19.78/3.01  ------ Problem Properties 
% 19.78/3.01  
% 19.78/3.01  
% 19.78/3.01  clauses                                 13
% 19.78/3.01  conjectures                             2
% 19.78/3.01  EPR                                     2
% 19.78/3.01  Horn                                    13
% 19.78/3.01  unary                                   7
% 19.78/3.01  binary                                  4
% 19.78/3.01  lits                                    21
% 19.78/3.01  lits eq                                 6
% 19.78/3.01  fd_pure                                 0
% 19.78/3.01  fd_pseudo                               0
% 19.78/3.01  fd_cond                                 0
% 19.78/3.01  fd_pseudo_cond                          0
% 19.78/3.01  AC symbols                              0
% 19.78/3.01  
% 19.78/3.01  ------ Input Options Time Limit: Unbounded
% 19.78/3.01  
% 19.78/3.01  
% 19.78/3.01  ------ 
% 19.78/3.01  Current options:
% 19.78/3.01  ------ 
% 19.78/3.01  
% 19.78/3.01  ------ Input Options
% 19.78/3.01  
% 19.78/3.01  --out_options                           all
% 19.78/3.01  --tptp_safe_out                         true
% 19.78/3.01  --problem_path                          ""
% 19.78/3.01  --include_path                          ""
% 19.78/3.01  --clausifier                            res/vclausify_rel
% 19.78/3.01  --clausifier_options                    --mode clausify
% 19.78/3.01  --stdin                                 false
% 19.78/3.01  --stats_out                             sel
% 19.78/3.01  
% 19.78/3.01  ------ General Options
% 19.78/3.01  
% 19.78/3.01  --fof                                   false
% 19.78/3.01  --time_out_real                         604.99
% 19.78/3.01  --time_out_virtual                      -1.
% 19.78/3.01  --symbol_type_check                     false
% 19.78/3.01  --clausify_out                          false
% 19.78/3.01  --sig_cnt_out                           false
% 19.78/3.01  --trig_cnt_out                          false
% 19.78/3.01  --trig_cnt_out_tolerance                1.
% 19.78/3.01  --trig_cnt_out_sk_spl                   false
% 19.78/3.01  --abstr_cl_out                          false
% 19.78/3.01  
% 19.78/3.01  ------ Global Options
% 19.78/3.01  
% 19.78/3.01  --schedule                              none
% 19.78/3.01  --add_important_lit                     false
% 19.78/3.01  --prop_solver_per_cl                    1000
% 19.78/3.01  --min_unsat_core                        false
% 19.78/3.01  --soft_assumptions                      false
% 19.78/3.01  --soft_lemma_size                       3
% 19.78/3.01  --prop_impl_unit_size                   0
% 19.78/3.01  --prop_impl_unit                        []
% 19.78/3.01  --share_sel_clauses                     true
% 19.78/3.01  --reset_solvers                         false
% 19.78/3.01  --bc_imp_inh                            [conj_cone]
% 19.78/3.01  --conj_cone_tolerance                   3.
% 19.78/3.01  --extra_neg_conj                        none
% 19.78/3.01  --large_theory_mode                     true
% 19.78/3.01  --prolific_symb_bound                   200
% 19.78/3.01  --lt_threshold                          2000
% 19.78/3.01  --clause_weak_htbl                      true
% 19.78/3.01  --gc_record_bc_elim                     false
% 19.78/3.01  
% 19.78/3.01  ------ Preprocessing Options
% 19.78/3.01  
% 19.78/3.01  --preprocessing_flag                    true
% 19.78/3.01  --time_out_prep_mult                    0.1
% 19.78/3.01  --splitting_mode                        input
% 19.78/3.01  --splitting_grd                         true
% 19.78/3.01  --splitting_cvd                         false
% 19.78/3.01  --splitting_cvd_svl                     false
% 19.78/3.01  --splitting_nvd                         32
% 19.78/3.01  --sub_typing                            true
% 19.78/3.01  --prep_gs_sim                           false
% 19.78/3.01  --prep_unflatten                        true
% 19.78/3.01  --prep_res_sim                          true
% 19.78/3.01  --prep_upred                            true
% 19.78/3.01  --prep_sem_filter                       exhaustive
% 19.78/3.01  --prep_sem_filter_out                   false
% 19.78/3.01  --pred_elim                             false
% 19.78/3.01  --res_sim_input                         true
% 19.78/3.01  --eq_ax_congr_red                       true
% 19.78/3.01  --pure_diseq_elim                       true
% 19.78/3.01  --brand_transform                       false
% 19.78/3.01  --non_eq_to_eq                          false
% 19.78/3.01  --prep_def_merge                        true
% 19.78/3.01  --prep_def_merge_prop_impl              false
% 19.78/3.01  --prep_def_merge_mbd                    true
% 19.78/3.01  --prep_def_merge_tr_red                 false
% 19.78/3.01  --prep_def_merge_tr_cl                  false
% 19.78/3.01  --smt_preprocessing                     true
% 19.78/3.01  --smt_ac_axioms                         fast
% 19.78/3.01  --preprocessed_out                      false
% 19.78/3.01  --preprocessed_stats                    false
% 19.78/3.01  
% 19.78/3.01  ------ Abstraction refinement Options
% 19.78/3.01  
% 19.78/3.01  --abstr_ref                             []
% 19.78/3.01  --abstr_ref_prep                        false
% 19.78/3.01  --abstr_ref_until_sat                   false
% 19.78/3.01  --abstr_ref_sig_restrict                funpre
% 19.78/3.01  --abstr_ref_af_restrict_to_split_sk     false
% 19.78/3.01  --abstr_ref_under                       []
% 19.78/3.01  
% 19.78/3.01  ------ SAT Options
% 19.78/3.01  
% 19.78/3.01  --sat_mode                              false
% 19.78/3.01  --sat_fm_restart_options                ""
% 19.78/3.01  --sat_gr_def                            false
% 19.78/3.01  --sat_epr_types                         true
% 19.78/3.01  --sat_non_cyclic_types                  false
% 19.78/3.01  --sat_finite_models                     false
% 19.78/3.01  --sat_fm_lemmas                         false
% 19.78/3.01  --sat_fm_prep                           false
% 19.78/3.01  --sat_fm_uc_incr                        true
% 19.78/3.01  --sat_out_model                         small
% 19.78/3.01  --sat_out_clauses                       false
% 19.78/3.01  
% 19.78/3.01  ------ QBF Options
% 19.78/3.01  
% 19.78/3.01  --qbf_mode                              false
% 19.78/3.01  --qbf_elim_univ                         false
% 19.78/3.01  --qbf_dom_inst                          none
% 19.78/3.01  --qbf_dom_pre_inst                      false
% 19.78/3.01  --qbf_sk_in                             false
% 19.78/3.01  --qbf_pred_elim                         true
% 19.78/3.01  --qbf_split                             512
% 19.78/3.01  
% 19.78/3.01  ------ BMC1 Options
% 19.78/3.01  
% 19.78/3.01  --bmc1_incremental                      false
% 19.78/3.01  --bmc1_axioms                           reachable_all
% 19.78/3.01  --bmc1_min_bound                        0
% 19.78/3.01  --bmc1_max_bound                        -1
% 19.78/3.01  --bmc1_max_bound_default                -1
% 19.78/3.01  --bmc1_symbol_reachability              true
% 19.78/3.01  --bmc1_property_lemmas                  false
% 19.78/3.01  --bmc1_k_induction                      false
% 19.78/3.01  --bmc1_non_equiv_states                 false
% 19.78/3.01  --bmc1_deadlock                         false
% 19.78/3.01  --bmc1_ucm                              false
% 19.78/3.01  --bmc1_add_unsat_core                   none
% 19.78/3.01  --bmc1_unsat_core_children              false
% 19.78/3.01  --bmc1_unsat_core_extrapolate_axioms    false
% 19.78/3.01  --bmc1_out_stat                         full
% 19.78/3.01  --bmc1_ground_init                      false
% 19.78/3.01  --bmc1_pre_inst_next_state              false
% 19.78/3.01  --bmc1_pre_inst_state                   false
% 19.78/3.01  --bmc1_pre_inst_reach_state             false
% 19.78/3.01  --bmc1_out_unsat_core                   false
% 19.78/3.01  --bmc1_aig_witness_out                  false
% 19.78/3.01  --bmc1_verbose                          false
% 19.78/3.01  --bmc1_dump_clauses_tptp                false
% 19.78/3.01  --bmc1_dump_unsat_core_tptp             false
% 19.78/3.01  --bmc1_dump_file                        -
% 19.78/3.01  --bmc1_ucm_expand_uc_limit              128
% 19.78/3.01  --bmc1_ucm_n_expand_iterations          6
% 19.78/3.01  --bmc1_ucm_extend_mode                  1
% 19.78/3.01  --bmc1_ucm_init_mode                    2
% 19.78/3.01  --bmc1_ucm_cone_mode                    none
% 19.78/3.01  --bmc1_ucm_reduced_relation_type        0
% 19.78/3.01  --bmc1_ucm_relax_model                  4
% 19.78/3.01  --bmc1_ucm_full_tr_after_sat            true
% 19.78/3.01  --bmc1_ucm_expand_neg_assumptions       false
% 19.78/3.01  --bmc1_ucm_layered_model                none
% 19.78/3.01  --bmc1_ucm_max_lemma_size               10
% 19.78/3.01  
% 19.78/3.01  ------ AIG Options
% 19.78/3.01  
% 19.78/3.01  --aig_mode                              false
% 19.78/3.01  
% 19.78/3.01  ------ Instantiation Options
% 19.78/3.01  
% 19.78/3.01  --instantiation_flag                    true
% 19.78/3.01  --inst_sos_flag                         false
% 19.78/3.01  --inst_sos_phase                        true
% 19.78/3.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.78/3.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.78/3.01  --inst_lit_sel_side                     num_symb
% 19.78/3.01  --inst_solver_per_active                1400
% 19.78/3.01  --inst_solver_calls_frac                1.
% 19.78/3.01  --inst_passive_queue_type               priority_queues
% 19.78/3.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.78/3.01  --inst_passive_queues_freq              [25;2]
% 19.78/3.01  --inst_dismatching                      true
% 19.78/3.01  --inst_eager_unprocessed_to_passive     true
% 19.78/3.01  --inst_prop_sim_given                   true
% 19.78/3.01  --inst_prop_sim_new                     false
% 19.78/3.01  --inst_subs_new                         false
% 19.78/3.01  --inst_eq_res_simp                      false
% 19.78/3.01  --inst_subs_given                       false
% 19.78/3.01  --inst_orphan_elimination               true
% 19.78/3.01  --inst_learning_loop_flag               true
% 19.78/3.01  --inst_learning_start                   3000
% 19.78/3.01  --inst_learning_factor                  2
% 19.78/3.01  --inst_start_prop_sim_after_learn       3
% 19.78/3.01  --inst_sel_renew                        solver
% 19.78/3.01  --inst_lit_activity_flag                true
% 19.78/3.01  --inst_restr_to_given                   false
% 19.78/3.01  --inst_activity_threshold               500
% 19.78/3.01  --inst_out_proof                        true
% 19.78/3.01  
% 19.78/3.01  ------ Resolution Options
% 19.78/3.01  
% 19.78/3.01  --resolution_flag                       true
% 19.78/3.01  --res_lit_sel                           adaptive
% 19.78/3.01  --res_lit_sel_side                      none
% 19.78/3.01  --res_ordering                          kbo
% 19.78/3.01  --res_to_prop_solver                    active
% 19.78/3.01  --res_prop_simpl_new                    false
% 19.78/3.01  --res_prop_simpl_given                  true
% 19.78/3.01  --res_passive_queue_type                priority_queues
% 19.78/3.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.78/3.01  --res_passive_queues_freq               [15;5]
% 19.78/3.01  --res_forward_subs                      full
% 19.78/3.01  --res_backward_subs                     full
% 19.78/3.01  --res_forward_subs_resolution           true
% 19.78/3.01  --res_backward_subs_resolution          true
% 19.78/3.01  --res_orphan_elimination                true
% 19.78/3.01  --res_time_limit                        2.
% 19.78/3.01  --res_out_proof                         true
% 19.78/3.01  
% 19.78/3.01  ------ Superposition Options
% 19.78/3.01  
% 19.78/3.01  --superposition_flag                    true
% 19.78/3.01  --sup_passive_queue_type                priority_queues
% 19.78/3.01  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.78/3.01  --sup_passive_queues_freq               [1;4]
% 19.78/3.01  --demod_completeness_check              fast
% 19.78/3.01  --demod_use_ground                      true
% 19.78/3.01  --sup_to_prop_solver                    passive
% 19.78/3.01  --sup_prop_simpl_new                    true
% 19.78/3.01  --sup_prop_simpl_given                  true
% 19.78/3.01  --sup_fun_splitting                     false
% 19.78/3.01  --sup_smt_interval                      50000
% 19.78/3.01  
% 19.78/3.01  ------ Superposition Simplification Setup
% 19.78/3.01  
% 19.78/3.01  --sup_indices_passive                   []
% 19.78/3.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.78/3.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.78/3.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.78/3.01  --sup_full_triv                         [TrivRules;PropSubs]
% 19.78/3.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.78/3.01  --sup_full_bw                           [BwDemod]
% 19.78/3.01  --sup_immed_triv                        [TrivRules]
% 19.78/3.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.78/3.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.78/3.01  --sup_immed_bw_main                     []
% 19.78/3.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.78/3.01  --sup_input_triv                        [Unflattening;TrivRules]
% 19.78/3.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.78/3.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.78/3.01  
% 19.78/3.01  ------ Combination Options
% 19.78/3.01  
% 19.78/3.01  --comb_res_mult                         3
% 19.78/3.01  --comb_sup_mult                         2
% 19.78/3.01  --comb_inst_mult                        10
% 19.78/3.01  
% 19.78/3.01  ------ Debug Options
% 19.78/3.01  
% 19.78/3.01  --dbg_backtrace                         false
% 19.78/3.01  --dbg_dump_prop_clauses                 false
% 19.78/3.01  --dbg_dump_prop_clauses_file            -
% 19.78/3.01  --dbg_out_stat                          false
% 19.78/3.01  
% 19.78/3.01  
% 19.78/3.01  
% 19.78/3.01  
% 19.78/3.01  ------ Proving...
% 19.78/3.01  
% 19.78/3.01  
% 19.78/3.01  % SZS status Theorem for theBenchmark.p
% 19.78/3.01  
% 19.78/3.01  % SZS output start CNFRefutation for theBenchmark.p
% 19.78/3.01  
% 19.78/3.01  fof(f10,axiom,(
% 19.78/3.01    ! [X0,X1,X2] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))),
% 19.78/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.78/3.01  
% 19.78/3.01  fof(f35,plain,(
% 19.78/3.01    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 19.78/3.01    inference(cnf_transformation,[],[f10])).
% 19.78/3.01  
% 19.78/3.01  fof(f9,axiom,(
% 19.78/3.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 19.78/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.78/3.01  
% 19.78/3.01  fof(f34,plain,(
% 19.78/3.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 19.78/3.01    inference(cnf_transformation,[],[f9])).
% 19.78/3.01  
% 19.78/3.01  fof(f42,plain,(
% 19.78/3.01    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2))) )),
% 19.78/3.01    inference(definition_unfolding,[],[f35,f34])).
% 19.78/3.01  
% 19.78/3.01  fof(f13,conjecture,(
% 19.78/3.01    ! [X0,X1,X2] : (r1_tarski(X2,X1) => k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,X2))),
% 19.78/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.78/3.01  
% 19.78/3.01  fof(f14,negated_conjecture,(
% 19.78/3.01    ~! [X0,X1,X2] : (r1_tarski(X2,X1) => k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,X2))),
% 19.78/3.01    inference(negated_conjecture,[],[f13])).
% 19.78/3.01  
% 19.78/3.01  fof(f23,plain,(
% 19.78/3.01    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) != k4_xboole_0(X0,X2) & r1_tarski(X2,X1))),
% 19.78/3.01    inference(ennf_transformation,[],[f14])).
% 19.78/3.01  
% 19.78/3.01  fof(f24,plain,(
% 19.78/3.01    ? [X0,X1,X2] : (k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,k4_xboole_0(X1,X2))) != k4_xboole_0(X0,X2) & r1_tarski(X2,X1)) => (k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2) & r1_tarski(sK2,sK1))),
% 19.78/3.01    introduced(choice_axiom,[])).
% 19.78/3.01  
% 19.78/3.01  fof(f25,plain,(
% 19.78/3.01    k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2) & r1_tarski(sK2,sK1)),
% 19.78/3.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f24])).
% 19.78/3.01  
% 19.78/3.01  fof(f39,plain,(
% 19.78/3.01    k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))) != k4_xboole_0(sK0,sK2)),
% 19.78/3.01    inference(cnf_transformation,[],[f25])).
% 19.78/3.01  
% 19.78/3.01  fof(f43,plain,(
% 19.78/3.01    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(sK0,sK2)),
% 19.78/3.01    inference(definition_unfolding,[],[f39,f34])).
% 19.78/3.01  
% 19.78/3.01  fof(f5,axiom,(
% 19.78/3.01    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 19.78/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.78/3.01  
% 19.78/3.01  fof(f30,plain,(
% 19.78/3.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 19.78/3.01    inference(cnf_transformation,[],[f5])).
% 19.78/3.01  
% 19.78/3.01  fof(f2,axiom,(
% 19.78/3.01    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 19.78/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.78/3.01  
% 19.78/3.01  fof(f15,plain,(
% 19.78/3.01    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 19.78/3.01    inference(ennf_transformation,[],[f2])).
% 19.78/3.01  
% 19.78/3.01  fof(f27,plain,(
% 19.78/3.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 19.78/3.01    inference(cnf_transformation,[],[f15])).
% 19.78/3.01  
% 19.78/3.01  fof(f6,axiom,(
% 19.78/3.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 19.78/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.78/3.01  
% 19.78/3.01  fof(f31,plain,(
% 19.78/3.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 19.78/3.01    inference(cnf_transformation,[],[f6])).
% 19.78/3.01  
% 19.78/3.01  fof(f1,axiom,(
% 19.78/3.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 19.78/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.78/3.01  
% 19.78/3.01  fof(f26,plain,(
% 19.78/3.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 19.78/3.01    inference(cnf_transformation,[],[f1])).
% 19.78/3.01  
% 19.78/3.01  fof(f40,plain,(
% 19.78/3.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 19.78/3.01    inference(definition_unfolding,[],[f26,f34,f34])).
% 19.78/3.01  
% 19.78/3.01  fof(f8,axiom,(
% 19.78/3.01    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 19.78/3.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.78/3.01  
% 19.78/3.01  fof(f21,plain,(
% 19.78/3.01    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 19.78/3.01    inference(ennf_transformation,[],[f8])).
% 19.78/3.01  
% 19.78/3.01  fof(f33,plain,(
% 19.78/3.01    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 19.78/3.01    inference(cnf_transformation,[],[f21])).
% 19.78/3.01  
% 19.78/3.01  fof(f38,plain,(
% 19.78/3.01    r1_tarski(sK2,sK1)),
% 19.78/3.01    inference(cnf_transformation,[],[f25])).
% 19.78/3.01  
% 19.78/3.01  cnf(c_96,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_95,plain,( X0 = X0 ),theory(equality) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_1558,plain,
% 19.78/3.01      ( X0 != X1 | X1 = X0 ),
% 19.78/3.01      inference(resolution,[status(thm)],[c_96,c_95]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_97,plain,
% 19.78/3.01      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 19.78/3.01      theory(equality) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_7367,plain,
% 19.78/3.01      ( X0 != X1 | X2 != X3 | k4_xboole_0(X1,X3) = k4_xboole_0(X0,X2) ),
% 19.78/3.01      inference(resolution,[status(thm)],[c_1558,c_97]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_8,plain,
% 19.78/3.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k4_xboole_0(X1,X2)) ),
% 19.78/3.01      inference(cnf_transformation,[],[f42]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_3216,plain,
% 19.78/3.01      ( X0 != k4_xboole_0(X1,k4_xboole_0(X2,X3))
% 19.78/3.01      | k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X1,X3))) = X0 ),
% 19.78/3.01      inference(resolution,[status(thm)],[c_8,c_96]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_11,negated_conjecture,
% 19.78/3.01      ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))) != k4_xboole_0(sK0,sK2) ),
% 19.78/3.01      inference(cnf_transformation,[],[f43]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_21092,plain,
% 19.78/3.01      ( k4_xboole_0(sK0,sK2) != k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
% 19.78/3.01      inference(resolution,[status(thm)],[c_3216,c_11]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_76000,plain,
% 19.78/3.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK2 | sK0 != sK0 ),
% 19.78/3.01      inference(resolution,[status(thm)],[c_7367,c_21092]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_76001,plain,
% 19.78/3.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) != sK2 ),
% 19.78/3.01      inference(equality_resolution_simp,[status(thm)],[c_76000]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_4,plain,
% 19.78/3.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 19.78/3.01      inference(cnf_transformation,[],[f30]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_247,plain,
% 19.78/3.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 19.78/3.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_1,plain,
% 19.78/3.01      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 19.78/3.01      inference(cnf_transformation,[],[f27]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_250,plain,
% 19.78/3.01      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 19.78/3.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_2083,plain,
% 19.78/3.01      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 19.78/3.01      inference(superposition,[status(thm)],[c_247,c_250]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_5,plain,
% 19.78/3.01      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
% 19.78/3.01      inference(cnf_transformation,[],[f31]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_47994,plain,
% 19.78/3.01      ( k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(X0,X0) ),
% 19.78/3.01      inference(superposition,[status(thm)],[c_2083,c_5]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_0,plain,
% 19.78/3.01      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.78/3.01      inference(cnf_transformation,[],[f40]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_501,plain,
% 19.78/3.01      ( k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X0,X1))) ),
% 19.78/3.01      inference(superposition,[status(thm)],[c_5,c_0]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_5160,plain,
% 19.78/3.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X2,X0),k4_xboole_0(X2,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(X2,X0))) ),
% 19.78/3.01      inference(superposition,[status(thm)],[c_501,c_8]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_48008,plain,
% 19.78/3.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X2),X0))) = k4_xboole_0(X0,k4_xboole_0(X1,k2_xboole_0(k4_xboole_0(X0,X2),X0))) ),
% 19.78/3.01      inference(superposition,[status(thm)],[c_2083,c_5160]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_48052,plain,
% 19.78/3.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,X2),X0))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.78/3.01      inference(demodulation,[status(thm)],[c_48008,c_2083]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_48094,plain,
% 19.78/3.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X0))) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
% 19.78/3.01      inference(demodulation,[status(thm)],[c_47994,c_48052]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_7,plain,
% 19.78/3.01      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ),
% 19.78/3.01      inference(cnf_transformation,[],[f33]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_245,plain,
% 19.78/3.01      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
% 19.78/3.01      | r1_tarski(X0,X1) != iProver_top ),
% 19.78/3.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_1482,plain,
% 19.78/3.01      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 19.78/3.01      inference(superposition,[status(thm)],[c_247,c_245]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_17377,plain,
% 19.78/3.01      ( k4_xboole_0(X0,k4_xboole_0(X1,X1)) = X0 ),
% 19.78/3.01      inference(superposition,[status(thm)],[c_1482,c_8]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_48113,plain,
% 19.78/3.01      ( k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
% 19.78/3.01      inference(demodulation,[status(thm)],[c_48094,c_8,c_2083,c_17377]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_12,negated_conjecture,
% 19.78/3.01      ( r1_tarski(sK2,sK1) ),
% 19.78/3.01      inference(cnf_transformation,[],[f38]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_242,plain,
% 19.78/3.01      ( r1_tarski(sK2,sK1) = iProver_top ),
% 19.78/3.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_1485,plain,
% 19.78/3.01      ( k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = sK1 ),
% 19.78/3.01      inference(superposition,[status(thm)],[c_242,c_245]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_24746,plain,
% 19.78/3.01      ( k4_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
% 19.78/3.01      inference(superposition,[status(thm)],[c_1485,c_5]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(c_48493,plain,
% 19.78/3.01      ( k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) = sK2 ),
% 19.78/3.01      inference(demodulation,[status(thm)],[c_48113,c_24746]) ).
% 19.78/3.01  
% 19.78/3.01  cnf(contradiction,plain,
% 19.78/3.01      ( $false ),
% 19.78/3.01      inference(minisat,[status(thm)],[c_76001,c_48493]) ).
% 19.78/3.01  
% 19.78/3.01  
% 19.78/3.01  % SZS output end CNFRefutation for theBenchmark.p
% 19.78/3.01  
% 19.78/3.01  ------                               Statistics
% 19.78/3.01  
% 19.78/3.01  ------ Selected
% 19.78/3.01  
% 19.78/3.01  total_time:                             2.488
% 19.78/3.01  
%------------------------------------------------------------------------------
