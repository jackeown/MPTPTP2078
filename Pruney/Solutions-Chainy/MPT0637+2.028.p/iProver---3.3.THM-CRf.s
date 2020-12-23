%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:50:00 EST 2020

% Result     : Theorem 11.59s
% Output     : CNFRefutation 11.59s
% Verified   : 
% Statistics : Number of formulae       :   61 (  89 expanded)
%              Number of clauses        :   28 (  34 expanded)
%              Number of leaves         :   11 (  19 expanded)
%              Depth                    :   13
%              Number of atoms          :   93 ( 136 expanded)
%              Number of equality atoms :   59 (  74 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    3 (   1 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f128,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f83,f84])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f123,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f77,f84])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f34,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f34])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f39])).

fof(f103,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f31,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f100,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f31])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f137,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f98,f84])).

fof(f99,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f31])).

fof(f35,conjecture,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,negated_conjecture,(
    ~ ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f35])).

fof(f47,plain,(
    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f36])).

fof(f58,plain,
    ( ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))
   => k6_relat_1(k3_xboole_0(sK2,sK3)) != k5_relat_1(k6_relat_1(sK3),k6_relat_1(sK2)) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    k6_relat_1(k3_xboole_0(sK2,sK3)) != k5_relat_1(k6_relat_1(sK3),k6_relat_1(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f47,f58])).

fof(f104,plain,(
    k6_relat_1(k3_xboole_0(sK2,sK3)) != k5_relat_1(k6_relat_1(sK3),k6_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f59])).

fof(f138,plain,(
    k6_relat_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != k5_relat_1(k6_relat_1(sK3),k6_relat_1(sK2)) ),
    inference(definition_unfolding,[],[f104,f84])).

cnf(c_23,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_17,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1151,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3255,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_23,c_1151])).

cnf(c_39,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_41,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_373,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | k5_relat_1(X0,k6_relat_1(X1)) = X0
    | k6_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_39,c_41])).

cnf(c_374,plain,
    ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
    | k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_1143,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_37,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1214,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1143,c_37])).

cnf(c_40,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_367,plain,
    ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
    | k6_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_41])).

cnf(c_368,plain,
    ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_1215,plain,
    ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1214,c_368])).

cnf(c_30562,plain,
    ( k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,X1)) = k6_relat_1(k4_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_3255,c_1215])).

cnf(c_36,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1))) = k7_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_385,plain,
    ( k7_relat_1(X0,k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1))) = k7_relat_1(X0,X1)
    | k6_relat_1(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_41])).

cnf(c_386,plain,
    ( k7_relat_1(k6_relat_1(X0),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_38,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1211,plain,
    ( k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(light_normalisation,[status(thm)],[c_386,c_38])).

cnf(c_40761,plain,
    ( k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(superposition,[status(thm)],[c_30562,c_1211])).

cnf(c_42,negated_conjecture,
    ( k6_relat_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != k5_relat_1(k6_relat_1(sK3),k6_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_1196,plain,
    ( k6_relat_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != k7_relat_1(k6_relat_1(sK2),sK3) ),
    inference(demodulation,[status(thm)],[c_42,c_368])).

cnf(c_44398,plain,
    ( k7_relat_1(k6_relat_1(sK2),sK3) != k7_relat_1(k6_relat_1(sK2),sK3) ),
    inference(demodulation,[status(thm)],[c_40761,c_1196])).

cnf(c_663,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_5184,plain,
    ( k7_relat_1(k6_relat_1(sK2),sK3) = k7_relat_1(k6_relat_1(sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_663])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_44398,c_5184])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.59/2.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.59/2.01  
% 11.59/2.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.59/2.01  
% 11.59/2.01  ------  iProver source info
% 11.59/2.01  
% 11.59/2.01  git: date: 2020-06-30 10:37:57 +0100
% 11.59/2.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.59/2.01  git: non_committed_changes: false
% 11.59/2.01  git: last_make_outside_of_git: false
% 11.59/2.01  
% 11.59/2.01  ------ 
% 11.59/2.01  
% 11.59/2.01  ------ Input Options
% 11.59/2.01  
% 11.59/2.01  --out_options                           all
% 11.59/2.01  --tptp_safe_out                         true
% 11.59/2.01  --problem_path                          ""
% 11.59/2.01  --include_path                          ""
% 11.59/2.01  --clausifier                            res/vclausify_rel
% 11.59/2.01  --clausifier_options                    --mode clausify
% 11.59/2.01  --stdin                                 false
% 11.59/2.01  --stats_out                             all
% 11.59/2.01  
% 11.59/2.01  ------ General Options
% 11.59/2.01  
% 11.59/2.01  --fof                                   false
% 11.59/2.01  --time_out_real                         305.
% 11.59/2.01  --time_out_virtual                      -1.
% 11.59/2.01  --symbol_type_check                     false
% 11.59/2.01  --clausify_out                          false
% 11.59/2.01  --sig_cnt_out                           false
% 11.59/2.01  --trig_cnt_out                          false
% 11.59/2.01  --trig_cnt_out_tolerance                1.
% 11.59/2.01  --trig_cnt_out_sk_spl                   false
% 11.59/2.01  --abstr_cl_out                          false
% 11.59/2.01  
% 11.59/2.01  ------ Global Options
% 11.59/2.01  
% 11.59/2.01  --schedule                              default
% 11.59/2.01  --add_important_lit                     false
% 11.59/2.01  --prop_solver_per_cl                    1000
% 11.59/2.01  --min_unsat_core                        false
% 11.59/2.01  --soft_assumptions                      false
% 11.59/2.01  --soft_lemma_size                       3
% 11.59/2.01  --prop_impl_unit_size                   0
% 11.59/2.01  --prop_impl_unit                        []
% 11.59/2.01  --share_sel_clauses                     true
% 11.59/2.01  --reset_solvers                         false
% 11.59/2.01  --bc_imp_inh                            [conj_cone]
% 11.59/2.01  --conj_cone_tolerance                   3.
% 11.59/2.01  --extra_neg_conj                        none
% 11.59/2.01  --large_theory_mode                     true
% 11.59/2.01  --prolific_symb_bound                   200
% 11.59/2.01  --lt_threshold                          2000
% 11.59/2.01  --clause_weak_htbl                      true
% 11.59/2.01  --gc_record_bc_elim                     false
% 11.59/2.01  
% 11.59/2.01  ------ Preprocessing Options
% 11.59/2.01  
% 11.59/2.01  --preprocessing_flag                    true
% 11.59/2.01  --time_out_prep_mult                    0.1
% 11.59/2.01  --splitting_mode                        input
% 11.59/2.01  --splitting_grd                         true
% 11.59/2.01  --splitting_cvd                         false
% 11.59/2.01  --splitting_cvd_svl                     false
% 11.59/2.01  --splitting_nvd                         32
% 11.59/2.01  --sub_typing                            true
% 11.59/2.01  --prep_gs_sim                           true
% 11.59/2.01  --prep_unflatten                        true
% 11.59/2.01  --prep_res_sim                          true
% 11.59/2.01  --prep_upred                            true
% 11.59/2.01  --prep_sem_filter                       exhaustive
% 11.59/2.01  --prep_sem_filter_out                   false
% 11.59/2.01  --pred_elim                             true
% 11.59/2.01  --res_sim_input                         true
% 11.59/2.01  --eq_ax_congr_red                       true
% 11.59/2.01  --pure_diseq_elim                       true
% 11.59/2.01  --brand_transform                       false
% 11.59/2.01  --non_eq_to_eq                          false
% 11.59/2.01  --prep_def_merge                        true
% 11.59/2.01  --prep_def_merge_prop_impl              false
% 11.59/2.01  --prep_def_merge_mbd                    true
% 11.59/2.01  --prep_def_merge_tr_red                 false
% 11.59/2.01  --prep_def_merge_tr_cl                  false
% 11.59/2.01  --smt_preprocessing                     true
% 11.59/2.01  --smt_ac_axioms                         fast
% 11.59/2.01  --preprocessed_out                      false
% 11.59/2.01  --preprocessed_stats                    false
% 11.59/2.01  
% 11.59/2.01  ------ Abstraction refinement Options
% 11.59/2.01  
% 11.59/2.01  --abstr_ref                             []
% 11.59/2.01  --abstr_ref_prep                        false
% 11.59/2.01  --abstr_ref_until_sat                   false
% 11.59/2.01  --abstr_ref_sig_restrict                funpre
% 11.59/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.59/2.01  --abstr_ref_under                       []
% 11.59/2.01  
% 11.59/2.01  ------ SAT Options
% 11.59/2.01  
% 11.59/2.01  --sat_mode                              false
% 11.59/2.01  --sat_fm_restart_options                ""
% 11.59/2.01  --sat_gr_def                            false
% 11.59/2.01  --sat_epr_types                         true
% 11.59/2.01  --sat_non_cyclic_types                  false
% 11.59/2.01  --sat_finite_models                     false
% 11.59/2.01  --sat_fm_lemmas                         false
% 11.59/2.01  --sat_fm_prep                           false
% 11.59/2.01  --sat_fm_uc_incr                        true
% 11.59/2.01  --sat_out_model                         small
% 11.59/2.01  --sat_out_clauses                       false
% 11.59/2.01  
% 11.59/2.01  ------ QBF Options
% 11.59/2.01  
% 11.59/2.01  --qbf_mode                              false
% 11.59/2.01  --qbf_elim_univ                         false
% 11.59/2.01  --qbf_dom_inst                          none
% 11.59/2.01  --qbf_dom_pre_inst                      false
% 11.59/2.01  --qbf_sk_in                             false
% 11.59/2.01  --qbf_pred_elim                         true
% 11.59/2.01  --qbf_split                             512
% 11.59/2.01  
% 11.59/2.01  ------ BMC1 Options
% 11.59/2.01  
% 11.59/2.01  --bmc1_incremental                      false
% 11.59/2.01  --bmc1_axioms                           reachable_all
% 11.59/2.01  --bmc1_min_bound                        0
% 11.59/2.01  --bmc1_max_bound                        -1
% 11.59/2.01  --bmc1_max_bound_default                -1
% 11.59/2.01  --bmc1_symbol_reachability              true
% 11.59/2.01  --bmc1_property_lemmas                  false
% 11.59/2.01  --bmc1_k_induction                      false
% 11.59/2.01  --bmc1_non_equiv_states                 false
% 11.59/2.01  --bmc1_deadlock                         false
% 11.59/2.01  --bmc1_ucm                              false
% 11.59/2.01  --bmc1_add_unsat_core                   none
% 11.59/2.01  --bmc1_unsat_core_children              false
% 11.59/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.59/2.01  --bmc1_out_stat                         full
% 11.59/2.01  --bmc1_ground_init                      false
% 11.59/2.01  --bmc1_pre_inst_next_state              false
% 11.59/2.01  --bmc1_pre_inst_state                   false
% 11.59/2.01  --bmc1_pre_inst_reach_state             false
% 11.59/2.01  --bmc1_out_unsat_core                   false
% 11.59/2.01  --bmc1_aig_witness_out                  false
% 11.59/2.01  --bmc1_verbose                          false
% 11.59/2.01  --bmc1_dump_clauses_tptp                false
% 11.59/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.59/2.01  --bmc1_dump_file                        -
% 11.59/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.59/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.59/2.01  --bmc1_ucm_extend_mode                  1
% 11.59/2.01  --bmc1_ucm_init_mode                    2
% 11.59/2.01  --bmc1_ucm_cone_mode                    none
% 11.59/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.59/2.01  --bmc1_ucm_relax_model                  4
% 11.59/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.59/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.59/2.01  --bmc1_ucm_layered_model                none
% 11.59/2.01  --bmc1_ucm_max_lemma_size               10
% 11.59/2.01  
% 11.59/2.01  ------ AIG Options
% 11.59/2.01  
% 11.59/2.01  --aig_mode                              false
% 11.59/2.01  
% 11.59/2.01  ------ Instantiation Options
% 11.59/2.01  
% 11.59/2.01  --instantiation_flag                    true
% 11.59/2.01  --inst_sos_flag                         false
% 11.59/2.01  --inst_sos_phase                        true
% 11.59/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.59/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.59/2.01  --inst_lit_sel_side                     num_symb
% 11.59/2.01  --inst_solver_per_active                1400
% 11.59/2.01  --inst_solver_calls_frac                1.
% 11.59/2.01  --inst_passive_queue_type               priority_queues
% 11.59/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.59/2.01  --inst_passive_queues_freq              [25;2]
% 11.59/2.01  --inst_dismatching                      true
% 11.59/2.01  --inst_eager_unprocessed_to_passive     true
% 11.59/2.01  --inst_prop_sim_given                   true
% 11.59/2.01  --inst_prop_sim_new                     false
% 11.59/2.01  --inst_subs_new                         false
% 11.59/2.01  --inst_eq_res_simp                      false
% 11.59/2.01  --inst_subs_given                       false
% 11.59/2.01  --inst_orphan_elimination               true
% 11.59/2.01  --inst_learning_loop_flag               true
% 11.59/2.01  --inst_learning_start                   3000
% 11.59/2.01  --inst_learning_factor                  2
% 11.59/2.01  --inst_start_prop_sim_after_learn       3
% 11.59/2.01  --inst_sel_renew                        solver
% 11.59/2.01  --inst_lit_activity_flag                true
% 11.59/2.01  --inst_restr_to_given                   false
% 11.59/2.01  --inst_activity_threshold               500
% 11.59/2.01  --inst_out_proof                        true
% 11.59/2.01  
% 11.59/2.01  ------ Resolution Options
% 11.59/2.01  
% 11.59/2.01  --resolution_flag                       true
% 11.59/2.01  --res_lit_sel                           adaptive
% 11.59/2.01  --res_lit_sel_side                      none
% 11.59/2.01  --res_ordering                          kbo
% 11.59/2.01  --res_to_prop_solver                    active
% 11.59/2.01  --res_prop_simpl_new                    false
% 11.59/2.01  --res_prop_simpl_given                  true
% 11.59/2.01  --res_passive_queue_type                priority_queues
% 11.59/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.59/2.01  --res_passive_queues_freq               [15;5]
% 11.59/2.01  --res_forward_subs                      full
% 11.59/2.01  --res_backward_subs                     full
% 11.59/2.01  --res_forward_subs_resolution           true
% 11.59/2.01  --res_backward_subs_resolution          true
% 11.59/2.01  --res_orphan_elimination                true
% 11.59/2.01  --res_time_limit                        2.
% 11.59/2.01  --res_out_proof                         true
% 11.59/2.01  
% 11.59/2.01  ------ Superposition Options
% 11.59/2.01  
% 11.59/2.01  --superposition_flag                    true
% 11.59/2.01  --sup_passive_queue_type                priority_queues
% 11.59/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.59/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.59/2.01  --demod_completeness_check              fast
% 11.59/2.01  --demod_use_ground                      true
% 11.59/2.01  --sup_to_prop_solver                    passive
% 11.59/2.01  --sup_prop_simpl_new                    true
% 11.59/2.01  --sup_prop_simpl_given                  true
% 11.59/2.01  --sup_fun_splitting                     false
% 11.59/2.01  --sup_smt_interval                      50000
% 11.59/2.01  
% 11.59/2.01  ------ Superposition Simplification Setup
% 11.59/2.01  
% 11.59/2.01  --sup_indices_passive                   []
% 11.59/2.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.59/2.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.59/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.59/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.59/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.59/2.01  --sup_full_bw                           [BwDemod]
% 11.59/2.01  --sup_immed_triv                        [TrivRules]
% 11.59/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.59/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.59/2.01  --sup_immed_bw_main                     []
% 11.59/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.59/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.59/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.59/2.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.59/2.01  
% 11.59/2.01  ------ Combination Options
% 11.59/2.01  
% 11.59/2.01  --comb_res_mult                         3
% 11.59/2.01  --comb_sup_mult                         2
% 11.59/2.01  --comb_inst_mult                        10
% 11.59/2.01  
% 11.59/2.01  ------ Debug Options
% 11.59/2.01  
% 11.59/2.01  --dbg_backtrace                         false
% 11.59/2.01  --dbg_dump_prop_clauses                 false
% 11.59/2.01  --dbg_dump_prop_clauses_file            -
% 11.59/2.01  --dbg_out_stat                          false
% 11.59/2.01  ------ Parsing...
% 11.59/2.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.59/2.01  
% 11.59/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.59/2.01  
% 11.59/2.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.59/2.01  
% 11.59/2.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.59/2.01  ------ Proving...
% 11.59/2.01  ------ Problem Properties 
% 11.59/2.01  
% 11.59/2.01  
% 11.59/2.01  clauses                                 42
% 11.59/2.01  conjectures                             1
% 11.59/2.01  EPR                                     1
% 11.59/2.01  Horn                                    39
% 11.59/2.01  unary                                   28
% 11.59/2.01  binary                                  8
% 11.59/2.01  lits                                    63
% 11.59/2.01  lits eq                                 38
% 11.59/2.01  fd_pure                                 0
% 11.59/2.01  fd_pseudo                               0
% 11.59/2.01  fd_cond                                 1
% 11.59/2.01  fd_pseudo_cond                          5
% 11.59/2.01  AC symbols                              0
% 11.59/2.01  
% 11.59/2.01  ------ Schedule dynamic 5 is on 
% 11.59/2.01  
% 11.59/2.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.59/2.01  
% 11.59/2.01  
% 11.59/2.01  ------ 
% 11.59/2.01  Current options:
% 11.59/2.01  ------ 
% 11.59/2.01  
% 11.59/2.01  ------ Input Options
% 11.59/2.01  
% 11.59/2.01  --out_options                           all
% 11.59/2.01  --tptp_safe_out                         true
% 11.59/2.01  --problem_path                          ""
% 11.59/2.01  --include_path                          ""
% 11.59/2.01  --clausifier                            res/vclausify_rel
% 11.59/2.01  --clausifier_options                    --mode clausify
% 11.59/2.01  --stdin                                 false
% 11.59/2.01  --stats_out                             all
% 11.59/2.01  
% 11.59/2.01  ------ General Options
% 11.59/2.01  
% 11.59/2.01  --fof                                   false
% 11.59/2.01  --time_out_real                         305.
% 11.59/2.01  --time_out_virtual                      -1.
% 11.59/2.01  --symbol_type_check                     false
% 11.59/2.01  --clausify_out                          false
% 11.59/2.01  --sig_cnt_out                           false
% 11.59/2.01  --trig_cnt_out                          false
% 11.59/2.01  --trig_cnt_out_tolerance                1.
% 11.59/2.01  --trig_cnt_out_sk_spl                   false
% 11.59/2.01  --abstr_cl_out                          false
% 11.59/2.01  
% 11.59/2.01  ------ Global Options
% 11.59/2.01  
% 11.59/2.01  --schedule                              default
% 11.59/2.01  --add_important_lit                     false
% 11.59/2.01  --prop_solver_per_cl                    1000
% 11.59/2.01  --min_unsat_core                        false
% 11.59/2.01  --soft_assumptions                      false
% 11.59/2.01  --soft_lemma_size                       3
% 11.59/2.01  --prop_impl_unit_size                   0
% 11.59/2.01  --prop_impl_unit                        []
% 11.59/2.01  --share_sel_clauses                     true
% 11.59/2.01  --reset_solvers                         false
% 11.59/2.01  --bc_imp_inh                            [conj_cone]
% 11.59/2.01  --conj_cone_tolerance                   3.
% 11.59/2.01  --extra_neg_conj                        none
% 11.59/2.01  --large_theory_mode                     true
% 11.59/2.01  --prolific_symb_bound                   200
% 11.59/2.01  --lt_threshold                          2000
% 11.59/2.01  --clause_weak_htbl                      true
% 11.59/2.01  --gc_record_bc_elim                     false
% 11.59/2.01  
% 11.59/2.01  ------ Preprocessing Options
% 11.59/2.01  
% 11.59/2.01  --preprocessing_flag                    true
% 11.59/2.01  --time_out_prep_mult                    0.1
% 11.59/2.01  --splitting_mode                        input
% 11.59/2.01  --splitting_grd                         true
% 11.59/2.01  --splitting_cvd                         false
% 11.59/2.01  --splitting_cvd_svl                     false
% 11.59/2.01  --splitting_nvd                         32
% 11.59/2.01  --sub_typing                            true
% 11.59/2.01  --prep_gs_sim                           true
% 11.59/2.01  --prep_unflatten                        true
% 11.59/2.01  --prep_res_sim                          true
% 11.59/2.01  --prep_upred                            true
% 11.59/2.01  --prep_sem_filter                       exhaustive
% 11.59/2.01  --prep_sem_filter_out                   false
% 11.59/2.01  --pred_elim                             true
% 11.59/2.01  --res_sim_input                         true
% 11.59/2.01  --eq_ax_congr_red                       true
% 11.59/2.01  --pure_diseq_elim                       true
% 11.59/2.01  --brand_transform                       false
% 11.59/2.01  --non_eq_to_eq                          false
% 11.59/2.01  --prep_def_merge                        true
% 11.59/2.01  --prep_def_merge_prop_impl              false
% 11.59/2.01  --prep_def_merge_mbd                    true
% 11.59/2.01  --prep_def_merge_tr_red                 false
% 11.59/2.01  --prep_def_merge_tr_cl                  false
% 11.59/2.01  --smt_preprocessing                     true
% 11.59/2.01  --smt_ac_axioms                         fast
% 11.59/2.01  --preprocessed_out                      false
% 11.59/2.01  --preprocessed_stats                    false
% 11.59/2.01  
% 11.59/2.01  ------ Abstraction refinement Options
% 11.59/2.01  
% 11.59/2.01  --abstr_ref                             []
% 11.59/2.01  --abstr_ref_prep                        false
% 11.59/2.01  --abstr_ref_until_sat                   false
% 11.59/2.01  --abstr_ref_sig_restrict                funpre
% 11.59/2.01  --abstr_ref_af_restrict_to_split_sk     false
% 11.59/2.01  --abstr_ref_under                       []
% 11.59/2.01  
% 11.59/2.01  ------ SAT Options
% 11.59/2.01  
% 11.59/2.01  --sat_mode                              false
% 11.59/2.01  --sat_fm_restart_options                ""
% 11.59/2.01  --sat_gr_def                            false
% 11.59/2.01  --sat_epr_types                         true
% 11.59/2.01  --sat_non_cyclic_types                  false
% 11.59/2.01  --sat_finite_models                     false
% 11.59/2.01  --sat_fm_lemmas                         false
% 11.59/2.01  --sat_fm_prep                           false
% 11.59/2.01  --sat_fm_uc_incr                        true
% 11.59/2.01  --sat_out_model                         small
% 11.59/2.01  --sat_out_clauses                       false
% 11.59/2.01  
% 11.59/2.01  ------ QBF Options
% 11.59/2.01  
% 11.59/2.01  --qbf_mode                              false
% 11.59/2.01  --qbf_elim_univ                         false
% 11.59/2.01  --qbf_dom_inst                          none
% 11.59/2.01  --qbf_dom_pre_inst                      false
% 11.59/2.01  --qbf_sk_in                             false
% 11.59/2.01  --qbf_pred_elim                         true
% 11.59/2.01  --qbf_split                             512
% 11.59/2.01  
% 11.59/2.01  ------ BMC1 Options
% 11.59/2.01  
% 11.59/2.01  --bmc1_incremental                      false
% 11.59/2.01  --bmc1_axioms                           reachable_all
% 11.59/2.01  --bmc1_min_bound                        0
% 11.59/2.01  --bmc1_max_bound                        -1
% 11.59/2.01  --bmc1_max_bound_default                -1
% 11.59/2.01  --bmc1_symbol_reachability              true
% 11.59/2.01  --bmc1_property_lemmas                  false
% 11.59/2.01  --bmc1_k_induction                      false
% 11.59/2.01  --bmc1_non_equiv_states                 false
% 11.59/2.01  --bmc1_deadlock                         false
% 11.59/2.01  --bmc1_ucm                              false
% 11.59/2.01  --bmc1_add_unsat_core                   none
% 11.59/2.01  --bmc1_unsat_core_children              false
% 11.59/2.01  --bmc1_unsat_core_extrapolate_axioms    false
% 11.59/2.01  --bmc1_out_stat                         full
% 11.59/2.01  --bmc1_ground_init                      false
% 11.59/2.01  --bmc1_pre_inst_next_state              false
% 11.59/2.01  --bmc1_pre_inst_state                   false
% 11.59/2.01  --bmc1_pre_inst_reach_state             false
% 11.59/2.01  --bmc1_out_unsat_core                   false
% 11.59/2.01  --bmc1_aig_witness_out                  false
% 11.59/2.01  --bmc1_verbose                          false
% 11.59/2.01  --bmc1_dump_clauses_tptp                false
% 11.59/2.01  --bmc1_dump_unsat_core_tptp             false
% 11.59/2.01  --bmc1_dump_file                        -
% 11.59/2.01  --bmc1_ucm_expand_uc_limit              128
% 11.59/2.01  --bmc1_ucm_n_expand_iterations          6
% 11.59/2.01  --bmc1_ucm_extend_mode                  1
% 11.59/2.01  --bmc1_ucm_init_mode                    2
% 11.59/2.01  --bmc1_ucm_cone_mode                    none
% 11.59/2.01  --bmc1_ucm_reduced_relation_type        0
% 11.59/2.01  --bmc1_ucm_relax_model                  4
% 11.59/2.01  --bmc1_ucm_full_tr_after_sat            true
% 11.59/2.01  --bmc1_ucm_expand_neg_assumptions       false
% 11.59/2.01  --bmc1_ucm_layered_model                none
% 11.59/2.01  --bmc1_ucm_max_lemma_size               10
% 11.59/2.01  
% 11.59/2.01  ------ AIG Options
% 11.59/2.01  
% 11.59/2.01  --aig_mode                              false
% 11.59/2.01  
% 11.59/2.01  ------ Instantiation Options
% 11.59/2.01  
% 11.59/2.01  --instantiation_flag                    true
% 11.59/2.01  --inst_sos_flag                         false
% 11.59/2.01  --inst_sos_phase                        true
% 11.59/2.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.59/2.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.59/2.01  --inst_lit_sel_side                     none
% 11.59/2.01  --inst_solver_per_active                1400
% 11.59/2.01  --inst_solver_calls_frac                1.
% 11.59/2.01  --inst_passive_queue_type               priority_queues
% 11.59/2.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.59/2.01  --inst_passive_queues_freq              [25;2]
% 11.59/2.01  --inst_dismatching                      true
% 11.59/2.01  --inst_eager_unprocessed_to_passive     true
% 11.59/2.01  --inst_prop_sim_given                   true
% 11.59/2.01  --inst_prop_sim_new                     false
% 11.59/2.01  --inst_subs_new                         false
% 11.59/2.01  --inst_eq_res_simp                      false
% 11.59/2.01  --inst_subs_given                       false
% 11.59/2.01  --inst_orphan_elimination               true
% 11.59/2.01  --inst_learning_loop_flag               true
% 11.59/2.01  --inst_learning_start                   3000
% 11.59/2.01  --inst_learning_factor                  2
% 11.59/2.01  --inst_start_prop_sim_after_learn       3
% 11.59/2.01  --inst_sel_renew                        solver
% 11.59/2.01  --inst_lit_activity_flag                true
% 11.59/2.01  --inst_restr_to_given                   false
% 11.59/2.01  --inst_activity_threshold               500
% 11.59/2.01  --inst_out_proof                        true
% 11.59/2.01  
% 11.59/2.01  ------ Resolution Options
% 11.59/2.01  
% 11.59/2.01  --resolution_flag                       false
% 11.59/2.01  --res_lit_sel                           adaptive
% 11.59/2.01  --res_lit_sel_side                      none
% 11.59/2.01  --res_ordering                          kbo
% 11.59/2.01  --res_to_prop_solver                    active
% 11.59/2.01  --res_prop_simpl_new                    false
% 11.59/2.01  --res_prop_simpl_given                  true
% 11.59/2.01  --res_passive_queue_type                priority_queues
% 11.59/2.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.59/2.01  --res_passive_queues_freq               [15;5]
% 11.59/2.01  --res_forward_subs                      full
% 11.59/2.01  --res_backward_subs                     full
% 11.59/2.01  --res_forward_subs_resolution           true
% 11.59/2.01  --res_backward_subs_resolution          true
% 11.59/2.01  --res_orphan_elimination                true
% 11.59/2.01  --res_time_limit                        2.
% 11.59/2.01  --res_out_proof                         true
% 11.59/2.01  
% 11.59/2.01  ------ Superposition Options
% 11.59/2.01  
% 11.59/2.01  --superposition_flag                    true
% 11.59/2.01  --sup_passive_queue_type                priority_queues
% 11.59/2.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.59/2.01  --sup_passive_queues_freq               [8;1;4]
% 11.59/2.01  --demod_completeness_check              fast
% 11.59/2.01  --demod_use_ground                      true
% 11.59/2.01  --sup_to_prop_solver                    passive
% 11.59/2.01  --sup_prop_simpl_new                    true
% 11.59/2.01  --sup_prop_simpl_given                  true
% 11.59/2.01  --sup_fun_splitting                     false
% 11.59/2.01  --sup_smt_interval                      50000
% 11.59/2.01  
% 11.59/2.01  ------ Superposition Simplification Setup
% 11.59/2.01  
% 11.59/2.01  --sup_indices_passive                   []
% 11.59/2.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.59/2.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.59/2.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.59/2.01  --sup_full_triv                         [TrivRules;PropSubs]
% 11.59/2.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.59/2.01  --sup_full_bw                           [BwDemod]
% 11.59/2.01  --sup_immed_triv                        [TrivRules]
% 11.59/2.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.59/2.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.59/2.01  --sup_immed_bw_main                     []
% 11.59/2.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.59/2.01  --sup_input_triv                        [Unflattening;TrivRules]
% 11.59/2.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.59/2.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.59/2.01  
% 11.59/2.01  ------ Combination Options
% 11.59/2.01  
% 11.59/2.01  --comb_res_mult                         3
% 11.59/2.01  --comb_sup_mult                         2
% 11.59/2.01  --comb_inst_mult                        10
% 11.59/2.01  
% 11.59/2.01  ------ Debug Options
% 11.59/2.01  
% 11.59/2.01  --dbg_backtrace                         false
% 11.59/2.01  --dbg_dump_prop_clauses                 false
% 11.59/2.01  --dbg_dump_prop_clauses_file            -
% 11.59/2.01  --dbg_out_stat                          false
% 11.59/2.01  
% 11.59/2.01  
% 11.59/2.01  
% 11.59/2.01  
% 11.59/2.01  ------ Proving...
% 11.59/2.01  
% 11.59/2.01  
% 11.59/2.01  % SZS status Theorem for theBenchmark.p
% 11.59/2.01  
% 11.59/2.01  % SZS output start CNFRefutation for theBenchmark.p
% 11.59/2.01  
% 11.59/2.01  fof(f18,axiom,(
% 11.59/2.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.59/2.01  
% 11.59/2.01  fof(f83,plain,(
% 11.59/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.59/2.01    inference(cnf_transformation,[],[f18])).
% 11.59/2.01  
% 11.59/2.01  fof(f19,axiom,(
% 11.59/2.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.59/2.01  
% 11.59/2.01  fof(f84,plain,(
% 11.59/2.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.59/2.01    inference(cnf_transformation,[],[f19])).
% 11.59/2.01  
% 11.59/2.01  fof(f128,plain,(
% 11.59/2.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.59/2.01    inference(definition_unfolding,[],[f83,f84])).
% 11.59/2.01  
% 11.59/2.01  fof(f12,axiom,(
% 11.59/2.01    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 11.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.59/2.01  
% 11.59/2.01  fof(f77,plain,(
% 11.59/2.01    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 11.59/2.01    inference(cnf_transformation,[],[f12])).
% 11.59/2.01  
% 11.59/2.01  fof(f123,plain,(
% 11.59/2.01    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 11.59/2.01    inference(definition_unfolding,[],[f77,f84])).
% 11.59/2.01  
% 11.59/2.01  fof(f32,axiom,(
% 11.59/2.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 11.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.59/2.01  
% 11.59/2.01  fof(f44,plain,(
% 11.59/2.01    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.59/2.01    inference(ennf_transformation,[],[f32])).
% 11.59/2.01  
% 11.59/2.01  fof(f45,plain,(
% 11.59/2.01    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 11.59/2.01    inference(flattening,[],[f44])).
% 11.59/2.01  
% 11.59/2.01  fof(f101,plain,(
% 11.59/2.01    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 11.59/2.01    inference(cnf_transformation,[],[f45])).
% 11.59/2.01  
% 11.59/2.01  fof(f34,axiom,(
% 11.59/2.01    ! [X0] : (v5_relat_1(k6_relat_1(X0),X0) & v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 11.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.59/2.01  
% 11.59/2.01  fof(f39,plain,(
% 11.59/2.01    ! [X0] : (v4_relat_1(k6_relat_1(X0),X0) & v1_relat_1(k6_relat_1(X0)))),
% 11.59/2.01    inference(pure_predicate_removal,[],[f34])).
% 11.59/2.01  
% 11.59/2.01  fof(f40,plain,(
% 11.59/2.01    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 11.59/2.01    inference(pure_predicate_removal,[],[f39])).
% 11.59/2.01  
% 11.59/2.01  fof(f103,plain,(
% 11.59/2.01    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 11.59/2.01    inference(cnf_transformation,[],[f40])).
% 11.59/2.01  
% 11.59/2.01  fof(f31,axiom,(
% 11.59/2.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.59/2.01  
% 11.59/2.01  fof(f100,plain,(
% 11.59/2.01    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 11.59/2.01    inference(cnf_transformation,[],[f31])).
% 11.59/2.01  
% 11.59/2.01  fof(f33,axiom,(
% 11.59/2.01    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 11.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.59/2.01  
% 11.59/2.01  fof(f46,plain,(
% 11.59/2.01    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 11.59/2.01    inference(ennf_transformation,[],[f33])).
% 11.59/2.01  
% 11.59/2.01  fof(f102,plain,(
% 11.59/2.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 11.59/2.01    inference(cnf_transformation,[],[f46])).
% 11.59/2.01  
% 11.59/2.01  fof(f30,axiom,(
% 11.59/2.01    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 11.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.59/2.01  
% 11.59/2.01  fof(f43,plain,(
% 11.59/2.01    ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.59/2.01    inference(ennf_transformation,[],[f30])).
% 11.59/2.01  
% 11.59/2.01  fof(f98,plain,(
% 11.59/2.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 11.59/2.01    inference(cnf_transformation,[],[f43])).
% 11.59/2.01  
% 11.59/2.01  fof(f137,plain,(
% 11.59/2.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k7_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 11.59/2.01    inference(definition_unfolding,[],[f98,f84])).
% 11.59/2.01  
% 11.59/2.01  fof(f99,plain,(
% 11.59/2.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 11.59/2.01    inference(cnf_transformation,[],[f31])).
% 11.59/2.01  
% 11.59/2.01  fof(f35,conjecture,(
% 11.59/2.01    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 11.59/2.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.59/2.01  
% 11.59/2.01  fof(f36,negated_conjecture,(
% 11.59/2.01    ~! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 11.59/2.01    inference(negated_conjecture,[],[f35])).
% 11.59/2.01  
% 11.59/2.01  fof(f47,plain,(
% 11.59/2.01    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))),
% 11.59/2.01    inference(ennf_transformation,[],[f36])).
% 11.59/2.01  
% 11.59/2.01  fof(f58,plain,(
% 11.59/2.01    ? [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) != k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) => k6_relat_1(k3_xboole_0(sK2,sK3)) != k5_relat_1(k6_relat_1(sK3),k6_relat_1(sK2))),
% 11.59/2.01    introduced(choice_axiom,[])).
% 11.59/2.01  
% 11.59/2.01  fof(f59,plain,(
% 11.59/2.01    k6_relat_1(k3_xboole_0(sK2,sK3)) != k5_relat_1(k6_relat_1(sK3),k6_relat_1(sK2))),
% 11.59/2.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f47,f58])).
% 11.59/2.01  
% 11.59/2.01  fof(f104,plain,(
% 11.59/2.01    k6_relat_1(k3_xboole_0(sK2,sK3)) != k5_relat_1(k6_relat_1(sK3),k6_relat_1(sK2))),
% 11.59/2.01    inference(cnf_transformation,[],[f59])).
% 11.59/2.01  
% 11.59/2.01  fof(f138,plain,(
% 11.59/2.01    k6_relat_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != k5_relat_1(k6_relat_1(sK3),k6_relat_1(sK2))),
% 11.59/2.01    inference(definition_unfolding,[],[f104,f84])).
% 11.59/2.01  
% 11.59/2.01  cnf(c_23,plain,
% 11.59/2.01      ( k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 11.59/2.01      inference(cnf_transformation,[],[f128]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_17,plain,
% 11.59/2.01      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
% 11.59/2.01      inference(cnf_transformation,[],[f123]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1151,plain,
% 11.59/2.01      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) = iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_3255,plain,
% 11.59/2.01      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_23,c_1151]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_39,plain,
% 11.59/2.01      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 11.59/2.01      | ~ v1_relat_1(X0)
% 11.59/2.01      | k5_relat_1(X0,k6_relat_1(X1)) = X0 ),
% 11.59/2.01      inference(cnf_transformation,[],[f101]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_41,plain,
% 11.59/2.01      ( v1_relat_1(k6_relat_1(X0)) ),
% 11.59/2.01      inference(cnf_transformation,[],[f103]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_373,plain,
% 11.59/2.01      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 11.59/2.01      | k5_relat_1(X0,k6_relat_1(X1)) = X0
% 11.59/2.01      | k6_relat_1(X2) != X0 ),
% 11.59/2.01      inference(resolution_lifted,[status(thm)],[c_39,c_41]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_374,plain,
% 11.59/2.01      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
% 11.59/2.01      | k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0) ),
% 11.59/2.01      inference(unflattening,[status(thm)],[c_373]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1143,plain,
% 11.59/2.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 11.59/2.01      | r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) != iProver_top ),
% 11.59/2.01      inference(predicate_to_equality,[status(thm)],[c_374]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_37,plain,
% 11.59/2.01      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 11.59/2.01      inference(cnf_transformation,[],[f100]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1214,plain,
% 11.59/2.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k6_relat_1(X0)
% 11.59/2.01      | r1_tarski(X0,X1) != iProver_top ),
% 11.59/2.01      inference(light_normalisation,[status(thm)],[c_1143,c_37]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_40,plain,
% 11.59/2.01      ( ~ v1_relat_1(X0)
% 11.59/2.01      | k5_relat_1(k6_relat_1(X1),X0) = k7_relat_1(X0,X1) ),
% 11.59/2.01      inference(cnf_transformation,[],[f102]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_367,plain,
% 11.59/2.01      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
% 11.59/2.01      | k6_relat_1(X2) != X1 ),
% 11.59/2.01      inference(resolution_lifted,[status(thm)],[c_40,c_41]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_368,plain,
% 11.59/2.01      ( k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
% 11.59/2.01      inference(unflattening,[status(thm)],[c_367]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1215,plain,
% 11.59/2.01      ( k7_relat_1(k6_relat_1(X0),X1) = k6_relat_1(X1)
% 11.59/2.01      | r1_tarski(X1,X0) != iProver_top ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_1214,c_368]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_30562,plain,
% 11.59/2.01      ( k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,X1)) = k6_relat_1(k4_xboole_0(X0,X1)) ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_3255,c_1215]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_36,plain,
% 11.59/2.01      ( ~ v1_relat_1(X0)
% 11.59/2.01      | k7_relat_1(X0,k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1))) = k7_relat_1(X0,X1) ),
% 11.59/2.01      inference(cnf_transformation,[],[f137]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_385,plain,
% 11.59/2.01      ( k7_relat_1(X0,k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),X1))) = k7_relat_1(X0,X1)
% 11.59/2.01      | k6_relat_1(X2) != X0 ),
% 11.59/2.01      inference(resolution_lifted,[status(thm)],[c_36,c_41]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_386,plain,
% 11.59/2.01      ( k7_relat_1(k6_relat_1(X0),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),k4_xboole_0(k1_relat_1(k6_relat_1(X0)),X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 11.59/2.01      inference(unflattening,[status(thm)],[c_385]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_38,plain,
% 11.59/2.01      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 11.59/2.01      inference(cnf_transformation,[],[f99]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1211,plain,
% 11.59/2.01      ( k7_relat_1(k6_relat_1(X0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 11.59/2.01      inference(light_normalisation,[status(thm)],[c_386,c_38]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_40761,plain,
% 11.59/2.01      ( k6_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k7_relat_1(k6_relat_1(X0),X1) ),
% 11.59/2.01      inference(superposition,[status(thm)],[c_30562,c_1211]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_42,negated_conjecture,
% 11.59/2.01      ( k6_relat_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != k5_relat_1(k6_relat_1(sK3),k6_relat_1(sK2)) ),
% 11.59/2.01      inference(cnf_transformation,[],[f138]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_1196,plain,
% 11.59/2.01      ( k6_relat_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))) != k7_relat_1(k6_relat_1(sK2),sK3) ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_42,c_368]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_44398,plain,
% 11.59/2.01      ( k7_relat_1(k6_relat_1(sK2),sK3) != k7_relat_1(k6_relat_1(sK2),sK3) ),
% 11.59/2.01      inference(demodulation,[status(thm)],[c_40761,c_1196]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_663,plain,( X0 = X0 ),theory(equality) ).
% 11.59/2.01  
% 11.59/2.01  cnf(c_5184,plain,
% 11.59/2.01      ( k7_relat_1(k6_relat_1(sK2),sK3) = k7_relat_1(k6_relat_1(sK2),sK3) ),
% 11.59/2.01      inference(instantiation,[status(thm)],[c_663]) ).
% 11.59/2.01  
% 11.59/2.01  cnf(contradiction,plain,
% 11.59/2.01      ( $false ),
% 11.59/2.01      inference(minisat,[status(thm)],[c_44398,c_5184]) ).
% 11.59/2.01  
% 11.59/2.01  
% 11.59/2.01  % SZS output end CNFRefutation for theBenchmark.p
% 11.59/2.01  
% 11.59/2.01  ------                               Statistics
% 11.59/2.01  
% 11.59/2.01  ------ General
% 11.59/2.01  
% 11.59/2.01  abstr_ref_over_cycles:                  0
% 11.59/2.01  abstr_ref_under_cycles:                 0
% 11.59/2.01  gc_basic_clause_elim:                   0
% 11.59/2.01  forced_gc_time:                         0
% 11.59/2.01  parsing_time:                           0.01
% 11.59/2.01  unif_index_cands_time:                  0.
% 11.59/2.01  unif_index_add_time:                    0.
% 11.59/2.01  orderings_time:                         0.
% 11.59/2.01  out_proof_time:                         0.008
% 11.59/2.01  total_time:                             1.384
% 11.59/2.01  num_of_symbols:                         48
% 11.59/2.01  num_of_terms:                           73233
% 11.59/2.01  
% 11.59/2.01  ------ Preprocessing
% 11.59/2.01  
% 11.59/2.01  num_of_splits:                          0
% 11.59/2.01  num_of_split_atoms:                     0
% 11.59/2.01  num_of_reused_defs:                     0
% 11.59/2.01  num_eq_ax_congr_red:                    22
% 11.59/2.01  num_of_sem_filtered_clauses:            1
% 11.59/2.01  num_of_subtypes:                        0
% 11.59/2.01  monotx_restored_types:                  0
% 11.59/2.01  sat_num_of_epr_types:                   0
% 11.59/2.01  sat_num_of_non_cyclic_types:            0
% 11.59/2.01  sat_guarded_non_collapsed_types:        0
% 11.59/2.01  num_pure_diseq_elim:                    0
% 11.59/2.01  simp_replaced_by:                       0
% 11.59/2.01  res_preprocessed:                       194
% 11.59/2.01  prep_upred:                             0
% 11.59/2.01  prep_unflattend:                        20
% 11.59/2.01  smt_new_axioms:                         0
% 11.59/2.01  pred_elim_cands:                        3
% 11.59/2.01  pred_elim:                              1
% 11.59/2.01  pred_elim_cl:                           1
% 11.59/2.01  pred_elim_cycles:                       6
% 11.59/2.01  merged_defs:                            8
% 11.59/2.01  merged_defs_ncl:                        0
% 11.59/2.01  bin_hyper_res:                          8
% 11.59/2.01  prep_cycles:                            4
% 11.59/2.01  pred_elim_time:                         0.004
% 11.59/2.01  splitting_time:                         0.
% 11.59/2.01  sem_filter_time:                        0.
% 11.59/2.01  monotx_time:                            0.
% 11.59/2.01  subtype_inf_time:                       0.
% 11.59/2.01  
% 11.59/2.01  ------ Problem properties
% 11.59/2.01  
% 11.59/2.01  clauses:                                42
% 11.59/2.01  conjectures:                            1
% 11.59/2.01  epr:                                    1
% 11.59/2.01  horn:                                   39
% 11.59/2.01  ground:                                 1
% 11.59/2.01  unary:                                  28
% 11.59/2.01  binary:                                 8
% 11.59/2.01  lits:                                   63
% 11.59/2.01  lits_eq:                                38
% 11.59/2.01  fd_pure:                                0
% 11.59/2.01  fd_pseudo:                              0
% 11.59/2.01  fd_cond:                                1
% 11.59/2.01  fd_pseudo_cond:                         5
% 11.59/2.01  ac_symbols:                             0
% 11.59/2.01  
% 11.59/2.01  ------ Propositional Solver
% 11.59/2.01  
% 11.59/2.01  prop_solver_calls:                      30
% 11.59/2.01  prop_fast_solver_calls:                 883
% 11.59/2.01  smt_solver_calls:                       0
% 11.59/2.01  smt_fast_solver_calls:                  0
% 11.59/2.01  prop_num_of_clauses:                    17428
% 11.59/2.01  prop_preprocess_simplified:             22322
% 11.59/2.01  prop_fo_subsumed:                       0
% 11.59/2.01  prop_solver_time:                       0.
% 11.59/2.01  smt_solver_time:                        0.
% 11.59/2.01  smt_fast_solver_time:                   0.
% 11.59/2.01  prop_fast_solver_time:                  0.
% 11.59/2.01  prop_unsat_core_time:                   0.002
% 11.59/2.01  
% 11.59/2.01  ------ QBF
% 11.59/2.01  
% 11.59/2.01  qbf_q_res:                              0
% 11.59/2.01  qbf_num_tautologies:                    0
% 11.59/2.01  qbf_prep_cycles:                        0
% 11.59/2.01  
% 11.59/2.01  ------ BMC1
% 11.59/2.01  
% 11.59/2.01  bmc1_current_bound:                     -1
% 11.59/2.01  bmc1_last_solved_bound:                 -1
% 11.59/2.01  bmc1_unsat_core_size:                   -1
% 11.59/2.01  bmc1_unsat_core_parents_size:           -1
% 11.59/2.01  bmc1_merge_next_fun:                    0
% 11.59/2.01  bmc1_unsat_core_clauses_time:           0.
% 11.59/2.01  
% 11.59/2.01  ------ Instantiation
% 11.59/2.01  
% 11.59/2.01  inst_num_of_clauses:                    3786
% 11.59/2.01  inst_num_in_passive:                    1180
% 11.59/2.01  inst_num_in_active:                     722
% 11.59/2.01  inst_num_in_unprocessed:                1884
% 11.59/2.01  inst_num_of_loops:                      780
% 11.59/2.01  inst_num_of_learning_restarts:          0
% 11.59/2.01  inst_num_moves_active_passive:          55
% 11.59/2.01  inst_lit_activity:                      0
% 11.59/2.01  inst_lit_activity_moves:                0
% 11.59/2.01  inst_num_tautologies:                   0
% 11.59/2.01  inst_num_prop_implied:                  0
% 11.59/2.01  inst_num_existing_simplified:           0
% 11.59/2.01  inst_num_eq_res_simplified:             0
% 11.59/2.01  inst_num_child_elim:                    0
% 11.59/2.01  inst_num_of_dismatching_blockings:      1109
% 11.59/2.01  inst_num_of_non_proper_insts:           1662
% 11.59/2.01  inst_num_of_duplicates:                 0
% 11.59/2.01  inst_inst_num_from_inst_to_res:         0
% 11.59/2.01  inst_dismatching_checking_time:         0.
% 11.59/2.01  
% 11.59/2.01  ------ Resolution
% 11.59/2.01  
% 11.59/2.01  res_num_of_clauses:                     0
% 11.59/2.01  res_num_in_passive:                     0
% 11.59/2.01  res_num_in_active:                      0
% 11.59/2.01  res_num_of_loops:                       198
% 11.59/2.01  res_forward_subset_subsumed:            229
% 11.59/2.01  res_backward_subset_subsumed:           0
% 11.59/2.01  res_forward_subsumed:                   0
% 11.59/2.01  res_backward_subsumed:                  0
% 11.59/2.01  res_forward_subsumption_resolution:     0
% 11.59/2.01  res_backward_subsumption_resolution:    0
% 11.59/2.01  res_clause_to_clause_subsumption:       37807
% 11.59/2.01  res_orphan_elimination:                 0
% 11.59/2.01  res_tautology_del:                      129
% 11.59/2.01  res_num_eq_res_simplified:              0
% 11.59/2.01  res_num_sel_changes:                    0
% 11.59/2.01  res_moves_from_active_to_pass:          0
% 11.59/2.01  
% 11.59/2.01  ------ Superposition
% 11.59/2.01  
% 11.59/2.01  sup_time_total:                         0.
% 11.59/2.01  sup_time_generating:                    0.
% 11.59/2.01  sup_time_sim_full:                      0.
% 11.59/2.01  sup_time_sim_immed:                     0.
% 11.59/2.01  
% 11.59/2.01  sup_num_of_clauses:                     2508
% 11.59/2.01  sup_num_in_active:                      135
% 11.59/2.01  sup_num_in_passive:                     2373
% 11.59/2.01  sup_num_of_loops:                       154
% 11.59/2.01  sup_fw_superposition:                   5358
% 11.59/2.01  sup_bw_superposition:                   3056
% 11.59/2.01  sup_immediate_simplified:               4218
% 11.59/2.01  sup_given_eliminated:                   5
% 11.59/2.01  comparisons_done:                       0
% 11.59/2.01  comparisons_avoided:                    0
% 11.59/2.01  
% 11.59/2.01  ------ Simplifications
% 11.59/2.01  
% 11.59/2.01  
% 11.59/2.01  sim_fw_subset_subsumed:                 14
% 11.59/2.01  sim_bw_subset_subsumed:                 0
% 11.59/2.01  sim_fw_subsumed:                        628
% 11.59/2.01  sim_bw_subsumed:                        54
% 11.59/2.01  sim_fw_subsumption_res:                 0
% 11.59/2.01  sim_bw_subsumption_res:                 0
% 11.59/2.01  sim_tautology_del:                      58
% 11.59/2.01  sim_eq_tautology_del:                   727
% 11.59/2.01  sim_eq_res_simp:                        7
% 11.59/2.01  sim_fw_demodulated:                     2802
% 11.59/2.01  sim_bw_demodulated:                     226
% 11.59/2.01  sim_light_normalised:                   1869
% 11.59/2.01  sim_joinable_taut:                      0
% 11.59/2.01  sim_joinable_simp:                      0
% 11.59/2.01  sim_ac_normalised:                      0
% 11.59/2.01  sim_smt_subsumption:                    0
% 11.59/2.01  
%------------------------------------------------------------------------------
