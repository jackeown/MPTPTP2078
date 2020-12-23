%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:36:12 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   44 (  62 expanded)
%              Number of clauses        :   24 (  27 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 126 expanded)
%              Number of equality atoms :   96 ( 125 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_tarski(X0) = X2
      | k1_tarski(X0) = X2
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k2_tarski(X0,X0) = X2
      | k2_tarski(X0,X0) = X2
      | k2_xboole_0(X1,X2) != k2_tarski(X0,X0) ) ),
    inference(definition_unfolding,[],[f33,f25,f25,f25])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
      | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0)
        | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
      & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0)
        & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 )
   => ( k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0)
      & k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0)
    & k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f35,plain,(
    k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    k4_xboole_0(k2_tarski(sK0,sK0),sK1) != k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f35,f25,f25])).

fof(f34,plain,(
    k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    k4_xboole_0(k2_tarski(sK0,sK0),sK1) != k1_xboole_0 ),
    inference(definition_unfolding,[],[f34,f25])).

cnf(c_7,plain,
    ( k2_tarski(X0,X0) = X1
    | k2_tarski(X0,X0) != k2_xboole_0(X2,X1)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_149,plain,
    ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(sK0,sK0),sK1)
    | k2_tarski(X0,X0) != k2_xboole_0(X1,k4_xboole_0(k2_tarski(sK0,sK0),sK1))
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_281,plain,
    ( k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),sK1)
    | k2_tarski(sK0,sK0) != k2_xboole_0(X0,k4_xboole_0(k2_tarski(sK0,sK0),sK1))
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_149])).

cnf(c_2143,plain,
    ( k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),sK1)
    | k2_tarski(sK0,sK0) != k2_xboole_0(k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)),k4_xboole_0(k2_tarski(sK0,sK0),sK1))
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_45,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_92,plain,
    ( k2_tarski(X0,X0) != X1
    | k2_tarski(X0,X0) = k2_xboole_0(X2,X3)
    | k2_xboole_0(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_109,plain,
    ( k2_tarski(X0,X0) != k2_tarski(X0,X0)
    | k2_tarski(X0,X0) = k2_xboole_0(X1,X2)
    | k2_xboole_0(X1,X2) != k2_tarski(X0,X0) ),
    inference(instantiation,[status(thm)],[c_92])).

cnf(c_142,plain,
    ( k2_tarski(X0,X0) != k2_tarski(X0,X0)
    | k2_tarski(X0,X0) = k2_xboole_0(k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),X1)),k4_xboole_0(k2_tarski(X0,X0),X1))
    | k2_xboole_0(k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),X1)),k4_xboole_0(k2_tarski(X0,X0),X1)) != k2_tarski(X0,X0) ),
    inference(instantiation,[status(thm)],[c_109])).

cnf(c_253,plain,
    ( k2_tarski(sK0,sK0) != k2_tarski(sK0,sK0)
    | k2_tarski(sK0,sK0) = k2_xboole_0(k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),X0)),k4_xboole_0(k2_tarski(sK0,sK0),X0))
    | k2_xboole_0(k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),X0)),k4_xboole_0(k2_tarski(sK0,sK0),X0)) != k2_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_142])).

cnf(c_2142,plain,
    ( k2_tarski(sK0,sK0) != k2_tarski(sK0,sK0)
    | k2_tarski(sK0,sK0) = k2_xboole_0(k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)),k4_xboole_0(k2_tarski(sK0,sK0),sK1))
    | k2_xboole_0(k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)),k4_xboole_0(k2_tarski(sK0,sK0),sK1)) != k2_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_253])).

cnf(c_6,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_187,plain,
    ( k2_xboole_0(k4_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X0,X1),X2)),k4_xboole_0(k2_tarski(X0,X1),X2)) = k2_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1164,plain,
    ( k2_xboole_0(k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)),k4_xboole_0(k2_tarski(sK0,sK0),sK1)) = k2_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_187])).

cnf(c_44,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_110,plain,
    ( k2_tarski(X0,X0) = k2_tarski(X0,X0) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_553,plain,
    ( k2_tarski(sK0,sK0) = k2_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_110])).

cnf(c_91,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK0),sK1) != X0
    | k4_xboole_0(k2_tarski(sK0,sK0),sK1) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_116,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK0),sK1) != k4_xboole_0(k2_tarski(sK0,sK0),sK1)
    | k4_xboole_0(k2_tarski(sK0,sK0),sK1) = k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_91])).

cnf(c_96,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK0),sK1) = k4_xboole_0(k2_tarski(sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_44])).

cnf(c_90,plain,
    ( k2_tarski(sK0,sK0) != X0
    | k4_xboole_0(k2_tarski(sK0,sK0),sK1) != X0
    | k4_xboole_0(k2_tarski(sK0,sK0),sK1) = k2_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_95,plain,
    ( k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK0),sK1)
    | k4_xboole_0(k2_tarski(sK0,sK0),sK1) = k2_tarski(sK0,sK0)
    | k4_xboole_0(k2_tarski(sK0,sK0),sK1) != k4_xboole_0(k2_tarski(sK0,sK0),sK1) ),
    inference(instantiation,[status(thm)],[c_90])).

cnf(c_15,negated_conjecture,
    ( k4_xboole_0(k2_tarski(sK0,sK0),sK1) != k2_tarski(sK0,sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_16,negated_conjecture,
    ( k4_xboole_0(k2_tarski(sK0,sK0),sK1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f47])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2143,c_2142,c_1164,c_553,c_116,c_96,c_95,c_15,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:05:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.32/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.01  
% 2.32/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.32/1.01  
% 2.32/1.01  ------  iProver source info
% 2.32/1.01  
% 2.32/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.32/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.32/1.01  git: non_committed_changes: false
% 2.32/1.01  git: last_make_outside_of_git: false
% 2.32/1.01  
% 2.32/1.01  ------ 
% 2.32/1.01  
% 2.32/1.01  ------ Input Options
% 2.32/1.01  
% 2.32/1.01  --out_options                           all
% 2.32/1.01  --tptp_safe_out                         true
% 2.32/1.01  --problem_path                          ""
% 2.32/1.01  --include_path                          ""
% 2.32/1.01  --clausifier                            res/vclausify_rel
% 2.32/1.01  --clausifier_options                    --mode clausify
% 2.32/1.01  --stdin                                 false
% 2.32/1.01  --stats_out                             all
% 2.32/1.01  
% 2.32/1.01  ------ General Options
% 2.32/1.01  
% 2.32/1.01  --fof                                   false
% 2.32/1.01  --time_out_real                         305.
% 2.32/1.01  --time_out_virtual                      -1.
% 2.32/1.01  --symbol_type_check                     false
% 2.32/1.01  --clausify_out                          false
% 2.32/1.01  --sig_cnt_out                           false
% 2.32/1.01  --trig_cnt_out                          false
% 2.32/1.01  --trig_cnt_out_tolerance                1.
% 2.32/1.01  --trig_cnt_out_sk_spl                   false
% 2.32/1.01  --abstr_cl_out                          false
% 2.32/1.01  
% 2.32/1.01  ------ Global Options
% 2.32/1.01  
% 2.32/1.01  --schedule                              default
% 2.32/1.01  --add_important_lit                     false
% 2.32/1.01  --prop_solver_per_cl                    1000
% 2.32/1.01  --min_unsat_core                        false
% 2.32/1.01  --soft_assumptions                      false
% 2.32/1.01  --soft_lemma_size                       3
% 2.32/1.01  --prop_impl_unit_size                   0
% 2.32/1.01  --prop_impl_unit                        []
% 2.32/1.01  --share_sel_clauses                     true
% 2.32/1.01  --reset_solvers                         false
% 2.32/1.01  --bc_imp_inh                            [conj_cone]
% 2.32/1.01  --conj_cone_tolerance                   3.
% 2.32/1.01  --extra_neg_conj                        none
% 2.32/1.01  --large_theory_mode                     true
% 2.32/1.01  --prolific_symb_bound                   200
% 2.32/1.01  --lt_threshold                          2000
% 2.32/1.01  --clause_weak_htbl                      true
% 2.32/1.01  --gc_record_bc_elim                     false
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing Options
% 2.32/1.01  
% 2.32/1.01  --preprocessing_flag                    true
% 2.32/1.01  --time_out_prep_mult                    0.1
% 2.32/1.01  --splitting_mode                        input
% 2.32/1.01  --splitting_grd                         true
% 2.32/1.01  --splitting_cvd                         false
% 2.32/1.01  --splitting_cvd_svl                     false
% 2.32/1.01  --splitting_nvd                         32
% 2.32/1.01  --sub_typing                            true
% 2.32/1.01  --prep_gs_sim                           true
% 2.32/1.01  --prep_unflatten                        true
% 2.32/1.01  --prep_res_sim                          true
% 2.32/1.01  --prep_upred                            true
% 2.32/1.01  --prep_sem_filter                       exhaustive
% 2.32/1.01  --prep_sem_filter_out                   false
% 2.32/1.01  --pred_elim                             true
% 2.32/1.01  --res_sim_input                         true
% 2.32/1.01  --eq_ax_congr_red                       true
% 2.32/1.01  --pure_diseq_elim                       true
% 2.32/1.01  --brand_transform                       false
% 2.32/1.01  --non_eq_to_eq                          false
% 2.32/1.01  --prep_def_merge                        true
% 2.32/1.01  --prep_def_merge_prop_impl              false
% 2.32/1.01  --prep_def_merge_mbd                    true
% 2.32/1.01  --prep_def_merge_tr_red                 false
% 2.32/1.01  --prep_def_merge_tr_cl                  false
% 2.32/1.01  --smt_preprocessing                     true
% 2.32/1.01  --smt_ac_axioms                         fast
% 2.32/1.01  --preprocessed_out                      false
% 2.32/1.01  --preprocessed_stats                    false
% 2.32/1.01  
% 2.32/1.01  ------ Abstraction refinement Options
% 2.32/1.01  
% 2.32/1.01  --abstr_ref                             []
% 2.32/1.01  --abstr_ref_prep                        false
% 2.32/1.01  --abstr_ref_until_sat                   false
% 2.32/1.01  --abstr_ref_sig_restrict                funpre
% 2.32/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/1.01  --abstr_ref_under                       []
% 2.32/1.01  
% 2.32/1.01  ------ SAT Options
% 2.32/1.01  
% 2.32/1.01  --sat_mode                              false
% 2.32/1.01  --sat_fm_restart_options                ""
% 2.32/1.01  --sat_gr_def                            false
% 2.32/1.01  --sat_epr_types                         true
% 2.32/1.01  --sat_non_cyclic_types                  false
% 2.32/1.01  --sat_finite_models                     false
% 2.32/1.01  --sat_fm_lemmas                         false
% 2.32/1.01  --sat_fm_prep                           false
% 2.32/1.01  --sat_fm_uc_incr                        true
% 2.32/1.01  --sat_out_model                         small
% 2.32/1.01  --sat_out_clauses                       false
% 2.32/1.01  
% 2.32/1.01  ------ QBF Options
% 2.32/1.01  
% 2.32/1.01  --qbf_mode                              false
% 2.32/1.01  --qbf_elim_univ                         false
% 2.32/1.01  --qbf_dom_inst                          none
% 2.32/1.01  --qbf_dom_pre_inst                      false
% 2.32/1.01  --qbf_sk_in                             false
% 2.32/1.01  --qbf_pred_elim                         true
% 2.32/1.01  --qbf_split                             512
% 2.32/1.01  
% 2.32/1.01  ------ BMC1 Options
% 2.32/1.01  
% 2.32/1.01  --bmc1_incremental                      false
% 2.32/1.01  --bmc1_axioms                           reachable_all
% 2.32/1.01  --bmc1_min_bound                        0
% 2.32/1.01  --bmc1_max_bound                        -1
% 2.32/1.01  --bmc1_max_bound_default                -1
% 2.32/1.01  --bmc1_symbol_reachability              true
% 2.32/1.01  --bmc1_property_lemmas                  false
% 2.32/1.01  --bmc1_k_induction                      false
% 2.32/1.01  --bmc1_non_equiv_states                 false
% 2.32/1.01  --bmc1_deadlock                         false
% 2.32/1.01  --bmc1_ucm                              false
% 2.32/1.01  --bmc1_add_unsat_core                   none
% 2.32/1.01  --bmc1_unsat_core_children              false
% 2.32/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/1.01  --bmc1_out_stat                         full
% 2.32/1.01  --bmc1_ground_init                      false
% 2.32/1.01  --bmc1_pre_inst_next_state              false
% 2.32/1.01  --bmc1_pre_inst_state                   false
% 2.32/1.01  --bmc1_pre_inst_reach_state             false
% 2.32/1.01  --bmc1_out_unsat_core                   false
% 2.32/1.01  --bmc1_aig_witness_out                  false
% 2.32/1.01  --bmc1_verbose                          false
% 2.32/1.01  --bmc1_dump_clauses_tptp                false
% 2.32/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.32/1.01  --bmc1_dump_file                        -
% 2.32/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.32/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.32/1.01  --bmc1_ucm_extend_mode                  1
% 2.32/1.01  --bmc1_ucm_init_mode                    2
% 2.32/1.01  --bmc1_ucm_cone_mode                    none
% 2.32/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.32/1.01  --bmc1_ucm_relax_model                  4
% 2.32/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.32/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/1.01  --bmc1_ucm_layered_model                none
% 2.32/1.01  --bmc1_ucm_max_lemma_size               10
% 2.32/1.01  
% 2.32/1.01  ------ AIG Options
% 2.32/1.01  
% 2.32/1.01  --aig_mode                              false
% 2.32/1.01  
% 2.32/1.01  ------ Instantiation Options
% 2.32/1.01  
% 2.32/1.01  --instantiation_flag                    true
% 2.32/1.01  --inst_sos_flag                         false
% 2.32/1.01  --inst_sos_phase                        true
% 2.32/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/1.01  --inst_lit_sel_side                     num_symb
% 2.32/1.01  --inst_solver_per_active                1400
% 2.32/1.01  --inst_solver_calls_frac                1.
% 2.32/1.01  --inst_passive_queue_type               priority_queues
% 2.32/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/1.01  --inst_passive_queues_freq              [25;2]
% 2.32/1.01  --inst_dismatching                      true
% 2.32/1.01  --inst_eager_unprocessed_to_passive     true
% 2.32/1.01  --inst_prop_sim_given                   true
% 2.32/1.01  --inst_prop_sim_new                     false
% 2.32/1.01  --inst_subs_new                         false
% 2.32/1.01  --inst_eq_res_simp                      false
% 2.32/1.01  --inst_subs_given                       false
% 2.32/1.01  --inst_orphan_elimination               true
% 2.32/1.01  --inst_learning_loop_flag               true
% 2.32/1.01  --inst_learning_start                   3000
% 2.32/1.01  --inst_learning_factor                  2
% 2.32/1.01  --inst_start_prop_sim_after_learn       3
% 2.32/1.01  --inst_sel_renew                        solver
% 2.32/1.01  --inst_lit_activity_flag                true
% 2.32/1.01  --inst_restr_to_given                   false
% 2.32/1.01  --inst_activity_threshold               500
% 2.32/1.01  --inst_out_proof                        true
% 2.32/1.01  
% 2.32/1.01  ------ Resolution Options
% 2.32/1.01  
% 2.32/1.01  --resolution_flag                       true
% 2.32/1.01  --res_lit_sel                           adaptive
% 2.32/1.01  --res_lit_sel_side                      none
% 2.32/1.01  --res_ordering                          kbo
% 2.32/1.01  --res_to_prop_solver                    active
% 2.32/1.01  --res_prop_simpl_new                    false
% 2.32/1.01  --res_prop_simpl_given                  true
% 2.32/1.01  --res_passive_queue_type                priority_queues
% 2.32/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/1.01  --res_passive_queues_freq               [15;5]
% 2.32/1.01  --res_forward_subs                      full
% 2.32/1.01  --res_backward_subs                     full
% 2.32/1.01  --res_forward_subs_resolution           true
% 2.32/1.01  --res_backward_subs_resolution          true
% 2.32/1.01  --res_orphan_elimination                true
% 2.32/1.01  --res_time_limit                        2.
% 2.32/1.01  --res_out_proof                         true
% 2.32/1.01  
% 2.32/1.01  ------ Superposition Options
% 2.32/1.01  
% 2.32/1.01  --superposition_flag                    true
% 2.32/1.01  --sup_passive_queue_type                priority_queues
% 2.32/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.32/1.01  --demod_completeness_check              fast
% 2.32/1.01  --demod_use_ground                      true
% 2.32/1.01  --sup_to_prop_solver                    passive
% 2.32/1.01  --sup_prop_simpl_new                    true
% 2.32/1.01  --sup_prop_simpl_given                  true
% 2.32/1.01  --sup_fun_splitting                     false
% 2.32/1.01  --sup_smt_interval                      50000
% 2.32/1.01  
% 2.32/1.01  ------ Superposition Simplification Setup
% 2.32/1.01  
% 2.32/1.01  --sup_indices_passive                   []
% 2.32/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.01  --sup_full_bw                           [BwDemod]
% 2.32/1.01  --sup_immed_triv                        [TrivRules]
% 2.32/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.01  --sup_immed_bw_main                     []
% 2.32/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.01  
% 2.32/1.01  ------ Combination Options
% 2.32/1.01  
% 2.32/1.01  --comb_res_mult                         3
% 2.32/1.01  --comb_sup_mult                         2
% 2.32/1.01  --comb_inst_mult                        10
% 2.32/1.01  
% 2.32/1.01  ------ Debug Options
% 2.32/1.01  
% 2.32/1.01  --dbg_backtrace                         false
% 2.32/1.01  --dbg_dump_prop_clauses                 false
% 2.32/1.01  --dbg_dump_prop_clauses_file            -
% 2.32/1.01  --dbg_out_stat                          false
% 2.32/1.01  ------ Parsing...
% 2.32/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  pe_s  pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 2.32/1.01  ------ Proving...
% 2.32/1.01  ------ Problem Properties 
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  clauses                                 13
% 2.32/1.01  conjectures                             2
% 2.32/1.01  EPR                                     0
% 2.32/1.01  Horn                                    9
% 2.32/1.01  unary                                   9
% 2.32/1.01  binary                                  0
% 2.32/1.01  lits                                    21
% 2.32/1.01  lits eq                                 21
% 2.32/1.01  fd_pure                                 0
% 2.32/1.01  fd_pseudo                               0
% 2.32/1.01  fd_cond                                 0
% 2.32/1.01  fd_pseudo_cond                          4
% 2.32/1.01  AC symbols                              0
% 2.32/1.01  
% 2.32/1.01  ------ Schedule dynamic 5 is on 
% 2.32/1.01  
% 2.32/1.01  ------ pure equality problem: resolution off 
% 2.32/1.01  
% 2.32/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  ------ 
% 2.32/1.01  Current options:
% 2.32/1.01  ------ 
% 2.32/1.01  
% 2.32/1.01  ------ Input Options
% 2.32/1.01  
% 2.32/1.01  --out_options                           all
% 2.32/1.01  --tptp_safe_out                         true
% 2.32/1.01  --problem_path                          ""
% 2.32/1.01  --include_path                          ""
% 2.32/1.01  --clausifier                            res/vclausify_rel
% 2.32/1.01  --clausifier_options                    --mode clausify
% 2.32/1.01  --stdin                                 false
% 2.32/1.01  --stats_out                             all
% 2.32/1.01  
% 2.32/1.01  ------ General Options
% 2.32/1.01  
% 2.32/1.01  --fof                                   false
% 2.32/1.01  --time_out_real                         305.
% 2.32/1.01  --time_out_virtual                      -1.
% 2.32/1.01  --symbol_type_check                     false
% 2.32/1.01  --clausify_out                          false
% 2.32/1.01  --sig_cnt_out                           false
% 2.32/1.01  --trig_cnt_out                          false
% 2.32/1.01  --trig_cnt_out_tolerance                1.
% 2.32/1.01  --trig_cnt_out_sk_spl                   false
% 2.32/1.01  --abstr_cl_out                          false
% 2.32/1.01  
% 2.32/1.01  ------ Global Options
% 2.32/1.01  
% 2.32/1.01  --schedule                              default
% 2.32/1.01  --add_important_lit                     false
% 2.32/1.01  --prop_solver_per_cl                    1000
% 2.32/1.01  --min_unsat_core                        false
% 2.32/1.01  --soft_assumptions                      false
% 2.32/1.01  --soft_lemma_size                       3
% 2.32/1.01  --prop_impl_unit_size                   0
% 2.32/1.01  --prop_impl_unit                        []
% 2.32/1.01  --share_sel_clauses                     true
% 2.32/1.01  --reset_solvers                         false
% 2.32/1.01  --bc_imp_inh                            [conj_cone]
% 2.32/1.01  --conj_cone_tolerance                   3.
% 2.32/1.01  --extra_neg_conj                        none
% 2.32/1.01  --large_theory_mode                     true
% 2.32/1.01  --prolific_symb_bound                   200
% 2.32/1.01  --lt_threshold                          2000
% 2.32/1.01  --clause_weak_htbl                      true
% 2.32/1.01  --gc_record_bc_elim                     false
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing Options
% 2.32/1.01  
% 2.32/1.01  --preprocessing_flag                    true
% 2.32/1.01  --time_out_prep_mult                    0.1
% 2.32/1.01  --splitting_mode                        input
% 2.32/1.01  --splitting_grd                         true
% 2.32/1.01  --splitting_cvd                         false
% 2.32/1.01  --splitting_cvd_svl                     false
% 2.32/1.01  --splitting_nvd                         32
% 2.32/1.01  --sub_typing                            true
% 2.32/1.01  --prep_gs_sim                           true
% 2.32/1.01  --prep_unflatten                        true
% 2.32/1.01  --prep_res_sim                          true
% 2.32/1.01  --prep_upred                            true
% 2.32/1.01  --prep_sem_filter                       exhaustive
% 2.32/1.01  --prep_sem_filter_out                   false
% 2.32/1.01  --pred_elim                             true
% 2.32/1.01  --res_sim_input                         true
% 2.32/1.01  --eq_ax_congr_red                       true
% 2.32/1.01  --pure_diseq_elim                       true
% 2.32/1.01  --brand_transform                       false
% 2.32/1.01  --non_eq_to_eq                          false
% 2.32/1.01  --prep_def_merge                        true
% 2.32/1.01  --prep_def_merge_prop_impl              false
% 2.32/1.01  --prep_def_merge_mbd                    true
% 2.32/1.01  --prep_def_merge_tr_red                 false
% 2.32/1.01  --prep_def_merge_tr_cl                  false
% 2.32/1.01  --smt_preprocessing                     true
% 2.32/1.01  --smt_ac_axioms                         fast
% 2.32/1.01  --preprocessed_out                      false
% 2.32/1.01  --preprocessed_stats                    false
% 2.32/1.01  
% 2.32/1.01  ------ Abstraction refinement Options
% 2.32/1.01  
% 2.32/1.01  --abstr_ref                             []
% 2.32/1.01  --abstr_ref_prep                        false
% 2.32/1.01  --abstr_ref_until_sat                   false
% 2.32/1.01  --abstr_ref_sig_restrict                funpre
% 2.32/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.32/1.01  --abstr_ref_under                       []
% 2.32/1.01  
% 2.32/1.01  ------ SAT Options
% 2.32/1.01  
% 2.32/1.01  --sat_mode                              false
% 2.32/1.01  --sat_fm_restart_options                ""
% 2.32/1.01  --sat_gr_def                            false
% 2.32/1.01  --sat_epr_types                         true
% 2.32/1.01  --sat_non_cyclic_types                  false
% 2.32/1.01  --sat_finite_models                     false
% 2.32/1.01  --sat_fm_lemmas                         false
% 2.32/1.01  --sat_fm_prep                           false
% 2.32/1.01  --sat_fm_uc_incr                        true
% 2.32/1.01  --sat_out_model                         small
% 2.32/1.01  --sat_out_clauses                       false
% 2.32/1.01  
% 2.32/1.01  ------ QBF Options
% 2.32/1.01  
% 2.32/1.01  --qbf_mode                              false
% 2.32/1.01  --qbf_elim_univ                         false
% 2.32/1.01  --qbf_dom_inst                          none
% 2.32/1.01  --qbf_dom_pre_inst                      false
% 2.32/1.01  --qbf_sk_in                             false
% 2.32/1.01  --qbf_pred_elim                         true
% 2.32/1.01  --qbf_split                             512
% 2.32/1.01  
% 2.32/1.01  ------ BMC1 Options
% 2.32/1.01  
% 2.32/1.01  --bmc1_incremental                      false
% 2.32/1.01  --bmc1_axioms                           reachable_all
% 2.32/1.01  --bmc1_min_bound                        0
% 2.32/1.01  --bmc1_max_bound                        -1
% 2.32/1.01  --bmc1_max_bound_default                -1
% 2.32/1.01  --bmc1_symbol_reachability              true
% 2.32/1.01  --bmc1_property_lemmas                  false
% 2.32/1.01  --bmc1_k_induction                      false
% 2.32/1.01  --bmc1_non_equiv_states                 false
% 2.32/1.01  --bmc1_deadlock                         false
% 2.32/1.01  --bmc1_ucm                              false
% 2.32/1.01  --bmc1_add_unsat_core                   none
% 2.32/1.01  --bmc1_unsat_core_children              false
% 2.32/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.32/1.01  --bmc1_out_stat                         full
% 2.32/1.01  --bmc1_ground_init                      false
% 2.32/1.01  --bmc1_pre_inst_next_state              false
% 2.32/1.01  --bmc1_pre_inst_state                   false
% 2.32/1.01  --bmc1_pre_inst_reach_state             false
% 2.32/1.01  --bmc1_out_unsat_core                   false
% 2.32/1.01  --bmc1_aig_witness_out                  false
% 2.32/1.01  --bmc1_verbose                          false
% 2.32/1.01  --bmc1_dump_clauses_tptp                false
% 2.32/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.32/1.01  --bmc1_dump_file                        -
% 2.32/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.32/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.32/1.01  --bmc1_ucm_extend_mode                  1
% 2.32/1.01  --bmc1_ucm_init_mode                    2
% 2.32/1.01  --bmc1_ucm_cone_mode                    none
% 2.32/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.32/1.01  --bmc1_ucm_relax_model                  4
% 2.32/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.32/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.32/1.01  --bmc1_ucm_layered_model                none
% 2.32/1.01  --bmc1_ucm_max_lemma_size               10
% 2.32/1.01  
% 2.32/1.01  ------ AIG Options
% 2.32/1.01  
% 2.32/1.01  --aig_mode                              false
% 2.32/1.01  
% 2.32/1.01  ------ Instantiation Options
% 2.32/1.01  
% 2.32/1.01  --instantiation_flag                    true
% 2.32/1.01  --inst_sos_flag                         false
% 2.32/1.01  --inst_sos_phase                        true
% 2.32/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.32/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.32/1.01  --inst_lit_sel_side                     none
% 2.32/1.01  --inst_solver_per_active                1400
% 2.32/1.01  --inst_solver_calls_frac                1.
% 2.32/1.01  --inst_passive_queue_type               priority_queues
% 2.32/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.32/1.01  --inst_passive_queues_freq              [25;2]
% 2.32/1.01  --inst_dismatching                      true
% 2.32/1.01  --inst_eager_unprocessed_to_passive     true
% 2.32/1.01  --inst_prop_sim_given                   true
% 2.32/1.01  --inst_prop_sim_new                     false
% 2.32/1.01  --inst_subs_new                         false
% 2.32/1.01  --inst_eq_res_simp                      false
% 2.32/1.01  --inst_subs_given                       false
% 2.32/1.01  --inst_orphan_elimination               true
% 2.32/1.01  --inst_learning_loop_flag               true
% 2.32/1.01  --inst_learning_start                   3000
% 2.32/1.01  --inst_learning_factor                  2
% 2.32/1.01  --inst_start_prop_sim_after_learn       3
% 2.32/1.01  --inst_sel_renew                        solver
% 2.32/1.01  --inst_lit_activity_flag                true
% 2.32/1.01  --inst_restr_to_given                   false
% 2.32/1.01  --inst_activity_threshold               500
% 2.32/1.01  --inst_out_proof                        true
% 2.32/1.01  
% 2.32/1.01  ------ Resolution Options
% 2.32/1.01  
% 2.32/1.01  --resolution_flag                       false
% 2.32/1.01  --res_lit_sel                           adaptive
% 2.32/1.01  --res_lit_sel_side                      none
% 2.32/1.01  --res_ordering                          kbo
% 2.32/1.01  --res_to_prop_solver                    active
% 2.32/1.01  --res_prop_simpl_new                    false
% 2.32/1.01  --res_prop_simpl_given                  true
% 2.32/1.01  --res_passive_queue_type                priority_queues
% 2.32/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.32/1.01  --res_passive_queues_freq               [15;5]
% 2.32/1.01  --res_forward_subs                      full
% 2.32/1.01  --res_backward_subs                     full
% 2.32/1.01  --res_forward_subs_resolution           true
% 2.32/1.01  --res_backward_subs_resolution          true
% 2.32/1.01  --res_orphan_elimination                true
% 2.32/1.01  --res_time_limit                        2.
% 2.32/1.01  --res_out_proof                         true
% 2.32/1.01  
% 2.32/1.01  ------ Superposition Options
% 2.32/1.01  
% 2.32/1.01  --superposition_flag                    true
% 2.32/1.01  --sup_passive_queue_type                priority_queues
% 2.32/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.32/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.32/1.01  --demod_completeness_check              fast
% 2.32/1.01  --demod_use_ground                      true
% 2.32/1.01  --sup_to_prop_solver                    passive
% 2.32/1.01  --sup_prop_simpl_new                    true
% 2.32/1.01  --sup_prop_simpl_given                  true
% 2.32/1.01  --sup_fun_splitting                     false
% 2.32/1.01  --sup_smt_interval                      50000
% 2.32/1.01  
% 2.32/1.01  ------ Superposition Simplification Setup
% 2.32/1.01  
% 2.32/1.01  --sup_indices_passive                   []
% 2.32/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.32/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.32/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.01  --sup_full_bw                           [BwDemod]
% 2.32/1.01  --sup_immed_triv                        [TrivRules]
% 2.32/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.32/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.01  --sup_immed_bw_main                     []
% 2.32/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.32/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.32/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.32/1.01  
% 2.32/1.01  ------ Combination Options
% 2.32/1.01  
% 2.32/1.01  --comb_res_mult                         3
% 2.32/1.01  --comb_sup_mult                         2
% 2.32/1.01  --comb_inst_mult                        10
% 2.32/1.01  
% 2.32/1.01  ------ Debug Options
% 2.32/1.01  
% 2.32/1.01  --dbg_backtrace                         false
% 2.32/1.01  --dbg_dump_prop_clauses                 false
% 2.32/1.01  --dbg_dump_prop_clauses_file            -
% 2.32/1.01  --dbg_out_stat                          false
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  ------ Proving...
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  % SZS status Theorem for theBenchmark.p
% 2.32/1.01  
% 2.32/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.32/1.01  
% 2.32/1.01  fof(f10,axiom,(
% 2.32/1.01    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 2.32/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f13,plain,(
% 2.32/1.01    ! [X0,X1,X2] : ((k1_xboole_0 = X2 & k1_tarski(X0) = X1) | (k1_tarski(X0) = X2 & k1_xboole_0 = X1) | (k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | k2_xboole_0(X1,X2) != k1_tarski(X0))),
% 2.32/1.01    inference(ennf_transformation,[],[f10])).
% 2.32/1.01  
% 2.32/1.01  fof(f33,plain,(
% 2.32/1.01    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_tarski(X0) = X2 | k1_tarski(X0) = X2 | k2_xboole_0(X1,X2) != k1_tarski(X0)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f13])).
% 2.32/1.01  
% 2.32/1.01  fof(f9,axiom,(
% 2.32/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.32/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f25,plain,(
% 2.32/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f9])).
% 2.32/1.01  
% 2.32/1.01  fof(f38,plain,(
% 2.32/1.01    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k2_tarski(X0,X0) = X2 | k2_tarski(X0,X0) = X2 | k2_xboole_0(X1,X2) != k2_tarski(X0,X0)) )),
% 2.32/1.01    inference(definition_unfolding,[],[f33,f25,f25,f25])).
% 2.32/1.01  
% 2.32/1.01  fof(f8,axiom,(
% 2.32/1.01    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.32/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f24,plain,(
% 2.32/1.01    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.32/1.01    inference(cnf_transformation,[],[f8])).
% 2.32/1.01  
% 2.32/1.01  fof(f7,axiom,(
% 2.32/1.01    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.32/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f23,plain,(
% 2.32/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.32/1.01    inference(cnf_transformation,[],[f7])).
% 2.32/1.01  
% 2.32/1.01  fof(f37,plain,(
% 2.32/1.01    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 2.32/1.01    inference(definition_unfolding,[],[f24,f23])).
% 2.32/1.01  
% 2.32/1.01  fof(f11,conjecture,(
% 2.32/1.01    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)),
% 2.32/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.32/1.01  
% 2.32/1.01  fof(f12,negated_conjecture,(
% 2.32/1.01    ~! [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) = k1_tarski(X0) | k4_xboole_0(k1_tarski(X0),X1) = k1_xboole_0)),
% 2.32/1.01    inference(negated_conjecture,[],[f11])).
% 2.32/1.01  
% 2.32/1.01  fof(f14,plain,(
% 2.32/1.01    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0)),
% 2.32/1.01    inference(ennf_transformation,[],[f12])).
% 2.32/1.01  
% 2.32/1.01  fof(f15,plain,(
% 2.32/1.01    ? [X0,X1] : (k4_xboole_0(k1_tarski(X0),X1) != k1_tarski(X0) & k4_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) => (k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0) & k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0)),
% 2.32/1.01    introduced(choice_axiom,[])).
% 2.32/1.01  
% 2.32/1.01  fof(f16,plain,(
% 2.32/1.01    k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0) & k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0),
% 2.32/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 2.32/1.01  
% 2.32/1.01  fof(f35,plain,(
% 2.32/1.01    k4_xboole_0(k1_tarski(sK0),sK1) != k1_tarski(sK0)),
% 2.32/1.01    inference(cnf_transformation,[],[f16])).
% 2.32/1.01  
% 2.32/1.01  fof(f46,plain,(
% 2.32/1.01    k4_xboole_0(k2_tarski(sK0,sK0),sK1) != k2_tarski(sK0,sK0)),
% 2.32/1.01    inference(definition_unfolding,[],[f35,f25,f25])).
% 2.32/1.01  
% 2.32/1.01  fof(f34,plain,(
% 2.32/1.01    k4_xboole_0(k1_tarski(sK0),sK1) != k1_xboole_0),
% 2.32/1.01    inference(cnf_transformation,[],[f16])).
% 2.32/1.01  
% 2.32/1.01  fof(f47,plain,(
% 2.32/1.01    k4_xboole_0(k2_tarski(sK0,sK0),sK1) != k1_xboole_0),
% 2.32/1.01    inference(definition_unfolding,[],[f34,f25])).
% 2.32/1.01  
% 2.32/1.01  cnf(c_7,plain,
% 2.32/1.01      ( k2_tarski(X0,X0) = X1
% 2.32/1.01      | k2_tarski(X0,X0) != k2_xboole_0(X2,X1)
% 2.32/1.01      | k1_xboole_0 = X1 ),
% 2.32/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_149,plain,
% 2.32/1.01      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(sK0,sK0),sK1)
% 2.32/1.01      | k2_tarski(X0,X0) != k2_xboole_0(X1,k4_xboole_0(k2_tarski(sK0,sK0),sK1))
% 2.32/1.01      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),sK1) ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_281,plain,
% 2.32/1.01      ( k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),sK1)
% 2.32/1.01      | k2_tarski(sK0,sK0) != k2_xboole_0(X0,k4_xboole_0(k2_tarski(sK0,sK0),sK1))
% 2.32/1.01      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),sK1) ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_149]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_2143,plain,
% 2.32/1.01      ( k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),sK1)
% 2.32/1.01      | k2_tarski(sK0,sK0) != k2_xboole_0(k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)),k4_xboole_0(k2_tarski(sK0,sK0),sK1))
% 2.32/1.01      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),sK1) ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_281]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_45,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_92,plain,
% 2.32/1.01      ( k2_tarski(X0,X0) != X1
% 2.32/1.01      | k2_tarski(X0,X0) = k2_xboole_0(X2,X3)
% 2.32/1.01      | k2_xboole_0(X2,X3) != X1 ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_45]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_109,plain,
% 2.32/1.01      ( k2_tarski(X0,X0) != k2_tarski(X0,X0)
% 2.32/1.01      | k2_tarski(X0,X0) = k2_xboole_0(X1,X2)
% 2.32/1.01      | k2_xboole_0(X1,X2) != k2_tarski(X0,X0) ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_92]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_142,plain,
% 2.32/1.01      ( k2_tarski(X0,X0) != k2_tarski(X0,X0)
% 2.32/1.01      | k2_tarski(X0,X0) = k2_xboole_0(k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),X1)),k4_xboole_0(k2_tarski(X0,X0),X1))
% 2.32/1.01      | k2_xboole_0(k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),X1)),k4_xboole_0(k2_tarski(X0,X0),X1)) != k2_tarski(X0,X0) ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_109]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_253,plain,
% 2.32/1.01      ( k2_tarski(sK0,sK0) != k2_tarski(sK0,sK0)
% 2.32/1.01      | k2_tarski(sK0,sK0) = k2_xboole_0(k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),X0)),k4_xboole_0(k2_tarski(sK0,sK0),X0))
% 2.32/1.01      | k2_xboole_0(k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),X0)),k4_xboole_0(k2_tarski(sK0,sK0),X0)) != k2_tarski(sK0,sK0) ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_142]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_2142,plain,
% 2.32/1.01      ( k2_tarski(sK0,sK0) != k2_tarski(sK0,sK0)
% 2.32/1.01      | k2_tarski(sK0,sK0) = k2_xboole_0(k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)),k4_xboole_0(k2_tarski(sK0,sK0),sK1))
% 2.32/1.01      | k2_xboole_0(k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)),k4_xboole_0(k2_tarski(sK0,sK0),sK1)) != k2_tarski(sK0,sK0) ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_253]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_6,plain,
% 2.32/1.01      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 2.32/1.01      inference(cnf_transformation,[],[f37]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_187,plain,
% 2.32/1.01      ( k2_xboole_0(k4_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X0,X1),X2)),k4_xboole_0(k2_tarski(X0,X1),X2)) = k2_tarski(X0,X1) ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_1164,plain,
% 2.32/1.01      ( k2_xboole_0(k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),sK1)),k4_xboole_0(k2_tarski(sK0,sK0),sK1)) = k2_tarski(sK0,sK0) ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_187]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_44,plain,( X0 = X0 ),theory(equality) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_110,plain,
% 2.32/1.01      ( k2_tarski(X0,X0) = k2_tarski(X0,X0) ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_44]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_553,plain,
% 2.32/1.01      ( k2_tarski(sK0,sK0) = k2_tarski(sK0,sK0) ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_110]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_91,plain,
% 2.32/1.01      ( k4_xboole_0(k2_tarski(sK0,sK0),sK1) != X0
% 2.32/1.01      | k4_xboole_0(k2_tarski(sK0,sK0),sK1) = k1_xboole_0
% 2.32/1.01      | k1_xboole_0 != X0 ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_45]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_116,plain,
% 2.32/1.01      ( k4_xboole_0(k2_tarski(sK0,sK0),sK1) != k4_xboole_0(k2_tarski(sK0,sK0),sK1)
% 2.32/1.01      | k4_xboole_0(k2_tarski(sK0,sK0),sK1) = k1_xboole_0
% 2.32/1.01      | k1_xboole_0 != k4_xboole_0(k2_tarski(sK0,sK0),sK1) ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_91]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_96,plain,
% 2.32/1.01      ( k4_xboole_0(k2_tarski(sK0,sK0),sK1) = k4_xboole_0(k2_tarski(sK0,sK0),sK1) ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_44]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_90,plain,
% 2.32/1.01      ( k2_tarski(sK0,sK0) != X0
% 2.32/1.01      | k4_xboole_0(k2_tarski(sK0,sK0),sK1) != X0
% 2.32/1.01      | k4_xboole_0(k2_tarski(sK0,sK0),sK1) = k2_tarski(sK0,sK0) ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_45]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_95,plain,
% 2.32/1.01      ( k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK0),sK1)
% 2.32/1.01      | k4_xboole_0(k2_tarski(sK0,sK0),sK1) = k2_tarski(sK0,sK0)
% 2.32/1.01      | k4_xboole_0(k2_tarski(sK0,sK0),sK1) != k4_xboole_0(k2_tarski(sK0,sK0),sK1) ),
% 2.32/1.01      inference(instantiation,[status(thm)],[c_90]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_15,negated_conjecture,
% 2.32/1.01      ( k4_xboole_0(k2_tarski(sK0,sK0),sK1) != k2_tarski(sK0,sK0) ),
% 2.32/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(c_16,negated_conjecture,
% 2.32/1.01      ( k4_xboole_0(k2_tarski(sK0,sK0),sK1) != k1_xboole_0 ),
% 2.32/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.32/1.01  
% 2.32/1.01  cnf(contradiction,plain,
% 2.32/1.01      ( $false ),
% 2.32/1.01      inference(minisat,
% 2.32/1.01                [status(thm)],
% 2.32/1.01                [c_2143,c_2142,c_1164,c_553,c_116,c_96,c_95,c_15,c_16]) ).
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.32/1.01  
% 2.32/1.01  ------                               Statistics
% 2.32/1.01  
% 2.32/1.01  ------ General
% 2.32/1.01  
% 2.32/1.01  abstr_ref_over_cycles:                  0
% 2.32/1.01  abstr_ref_under_cycles:                 0
% 2.32/1.01  gc_basic_clause_elim:                   0
% 2.32/1.01  forced_gc_time:                         0
% 2.32/1.01  parsing_time:                           0.036
% 2.32/1.01  unif_index_cands_time:                  0.
% 2.32/1.01  unif_index_add_time:                    0.
% 2.32/1.01  orderings_time:                         0.
% 2.32/1.01  out_proof_time:                         0.006
% 2.32/1.01  total_time:                             0.201
% 2.32/1.01  num_of_symbols:                         37
% 2.32/1.01  num_of_terms:                           3049
% 2.32/1.01  
% 2.32/1.01  ------ Preprocessing
% 2.32/1.01  
% 2.32/1.01  num_of_splits:                          0
% 2.32/1.01  num_of_split_atoms:                     0
% 2.32/1.01  num_of_reused_defs:                     0
% 2.32/1.01  num_eq_ax_congr_red:                    0
% 2.32/1.01  num_of_sem_filtered_clauses:            0
% 2.32/1.01  num_of_subtypes:                        0
% 2.32/1.01  monotx_restored_types:                  0
% 2.32/1.01  sat_num_of_epr_types:                   0
% 2.32/1.01  sat_num_of_non_cyclic_types:            0
% 2.32/1.01  sat_guarded_non_collapsed_types:        0
% 2.32/1.01  num_pure_diseq_elim:                    0
% 2.32/1.01  simp_replaced_by:                       0
% 2.32/1.01  res_preprocessed:                       44
% 2.32/1.01  prep_upred:                             0
% 2.32/1.01  prep_unflattend:                        0
% 2.32/1.01  smt_new_axioms:                         0
% 2.32/1.01  pred_elim_cands:                        0
% 2.32/1.01  pred_elim:                              0
% 2.32/1.01  pred_elim_cl:                           0
% 2.32/1.01  pred_elim_cycles:                       0
% 2.32/1.01  merged_defs:                            0
% 2.32/1.01  merged_defs_ncl:                        0
% 2.32/1.01  bin_hyper_res:                          0
% 2.32/1.01  prep_cycles:                            3
% 2.32/1.01  pred_elim_time:                         0.
% 2.32/1.01  splitting_time:                         0.
% 2.32/1.01  sem_filter_time:                        0.
% 2.32/1.01  monotx_time:                            0.001
% 2.32/1.01  subtype_inf_time:                       0.
% 2.32/1.01  
% 2.32/1.01  ------ Problem properties
% 2.32/1.01  
% 2.32/1.01  clauses:                                13
% 2.32/1.01  conjectures:                            2
% 2.32/1.01  epr:                                    0
% 2.32/1.01  horn:                                   9
% 2.32/1.01  ground:                                 2
% 2.32/1.01  unary:                                  9
% 2.32/1.01  binary:                                 0
% 2.32/1.01  lits:                                   21
% 2.32/1.01  lits_eq:                                21
% 2.32/1.01  fd_pure:                                0
% 2.32/1.01  fd_pseudo:                              0
% 2.32/1.01  fd_cond:                                0
% 2.32/1.01  fd_pseudo_cond:                         4
% 2.32/1.01  ac_symbols:                             0
% 2.32/1.01  
% 2.32/1.01  ------ Propositional Solver
% 2.32/1.01  
% 2.32/1.01  prop_solver_calls:                      24
% 2.32/1.01  prop_fast_solver_calls:                 228
% 2.32/1.01  smt_solver_calls:                       0
% 2.32/1.01  smt_fast_solver_calls:                  0
% 2.32/1.01  prop_num_of_clauses:                    697
% 2.32/1.01  prop_preprocess_simplified:             1925
% 2.32/1.01  prop_fo_subsumed:                       4
% 2.32/1.01  prop_solver_time:                       0.
% 2.32/1.01  smt_solver_time:                        0.
% 2.32/1.01  smt_fast_solver_time:                   0.
% 2.32/1.01  prop_fast_solver_time:                  0.
% 2.32/1.01  prop_unsat_core_time:                   0.
% 2.32/1.01  
% 2.32/1.01  ------ QBF
% 2.32/1.01  
% 2.32/1.01  qbf_q_res:                              0
% 2.32/1.01  qbf_num_tautologies:                    0
% 2.32/1.01  qbf_prep_cycles:                        0
% 2.32/1.01  
% 2.32/1.01  ------ BMC1
% 2.32/1.01  
% 2.32/1.01  bmc1_current_bound:                     -1
% 2.32/1.01  bmc1_last_solved_bound:                 -1
% 2.32/1.01  bmc1_unsat_core_size:                   -1
% 2.32/1.01  bmc1_unsat_core_parents_size:           -1
% 2.32/1.01  bmc1_merge_next_fun:                    0
% 2.32/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.32/1.01  
% 2.32/1.01  ------ Instantiation
% 2.32/1.01  
% 2.32/1.01  inst_num_of_clauses:                    356
% 2.32/1.01  inst_num_in_passive:                    175
% 2.32/1.01  inst_num_in_active:                     154
% 2.32/1.01  inst_num_in_unprocessed:                26
% 2.32/1.01  inst_num_of_loops:                      166
% 2.32/1.01  inst_num_of_learning_restarts:          0
% 2.32/1.01  inst_num_moves_active_passive:          7
% 2.32/1.01  inst_lit_activity:                      0
% 2.32/1.01  inst_lit_activity_moves:                0
% 2.32/1.01  inst_num_tautologies:                   0
% 2.32/1.01  inst_num_prop_implied:                  0
% 2.32/1.01  inst_num_existing_simplified:           0
% 2.32/1.01  inst_num_eq_res_simplified:             0
% 2.32/1.01  inst_num_child_elim:                    0
% 2.32/1.01  inst_num_of_dismatching_blockings:      121
% 2.32/1.01  inst_num_of_non_proper_insts:           306
% 2.32/1.01  inst_num_of_duplicates:                 0
% 2.32/1.01  inst_inst_num_from_inst_to_res:         0
% 2.32/1.01  inst_dismatching_checking_time:         0.
% 2.32/1.01  
% 2.32/1.01  ------ Resolution
% 2.32/1.01  
% 2.32/1.01  res_num_of_clauses:                     0
% 2.32/1.01  res_num_in_passive:                     0
% 2.32/1.01  res_num_in_active:                      0
% 2.32/1.01  res_num_of_loops:                       47
% 2.32/1.01  res_forward_subset_subsumed:            39
% 2.32/1.01  res_backward_subset_subsumed:           0
% 2.32/1.01  res_forward_subsumed:                   0
% 2.32/1.01  res_backward_subsumed:                  0
% 2.32/1.01  res_forward_subsumption_resolution:     0
% 2.32/1.01  res_backward_subsumption_resolution:    0
% 2.32/1.01  res_clause_to_clause_subsumption:       765
% 2.32/1.01  res_orphan_elimination:                 0
% 2.32/1.01  res_tautology_del:                      32
% 2.32/1.01  res_num_eq_res_simplified:              0
% 2.32/1.01  res_num_sel_changes:                    0
% 2.32/1.01  res_moves_from_active_to_pass:          0
% 2.32/1.01  
% 2.32/1.01  ------ Superposition
% 2.32/1.01  
% 2.32/1.01  sup_time_total:                         0.
% 2.32/1.01  sup_time_generating:                    0.
% 2.32/1.01  sup_time_sim_full:                      0.
% 2.32/1.01  sup_time_sim_immed:                     0.
% 2.32/1.01  
% 2.32/1.01  sup_num_of_clauses:                     102
% 2.32/1.01  sup_num_in_active:                      31
% 2.32/1.01  sup_num_in_passive:                     71
% 2.32/1.01  sup_num_of_loops:                       32
% 2.32/1.01  sup_fw_superposition:                   267
% 2.32/1.01  sup_bw_superposition:                   205
% 2.32/1.01  sup_immediate_simplified:               143
% 2.32/1.01  sup_given_eliminated:                   0
% 2.32/1.01  comparisons_done:                       0
% 2.32/1.01  comparisons_avoided:                    0
% 2.32/1.01  
% 2.32/1.01  ------ Simplifications
% 2.32/1.01  
% 2.32/1.01  
% 2.32/1.01  sim_fw_subset_subsumed:                 0
% 2.32/1.01  sim_bw_subset_subsumed:                 0
% 2.32/1.01  sim_fw_subsumed:                        53
% 2.32/1.01  sim_bw_subsumed:                        1
% 2.32/1.01  sim_fw_subsumption_res:                 0
% 2.32/1.01  sim_bw_subsumption_res:                 0
% 2.32/1.01  sim_tautology_del:                      14
% 2.32/1.01  sim_eq_tautology_del:                   28
% 2.32/1.01  sim_eq_res_simp:                        0
% 2.32/1.01  sim_fw_demodulated:                     40
% 2.32/1.01  sim_bw_demodulated:                     4
% 2.32/1.01  sim_light_normalised:                   67
% 2.32/1.01  sim_joinable_taut:                      0
% 2.32/1.01  sim_joinable_simp:                      0
% 2.32/1.01  sim_ac_normalised:                      0
% 2.32/1.01  sim_smt_subsumption:                    0
% 2.32/1.01  
%------------------------------------------------------------------------------
