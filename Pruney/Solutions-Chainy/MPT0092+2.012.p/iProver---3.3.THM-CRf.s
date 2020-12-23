%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:24:45 EST 2020

% Result     : Theorem 11.38s
% Output     : CNFRefutation 11.38s
% Verified   : 
% Statistics : Number of formulae       :   58 (  65 expanded)
%              Number of clauses        :   35 (  37 expanded)
%              Number of leaves         :   11 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 126 expanded)
%              Number of equality atoms :   69 (  73 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,k4_xboole_0(X2,X1))
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f23,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f24,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_4,plain,
    ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_26867,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK1),X0) = k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_45470,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK1),sK0) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_26867])).

cnf(c_154,plain,
    ( X0 != X1
    | X2 != X3
    | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
    theory(equality)).

cnf(c_6261,plain,
    ( X0 != X1
    | k2_xboole_0(X2,X3) != X4
    | k4_xboole_0(X0,k2_xboole_0(X2,X3)) = k4_xboole_0(X1,X4) ),
    inference(instantiation,[status(thm)],[c_154])).

cnf(c_20295,plain,
    ( k2_xboole_0(sK1,sK0) != sK1
    | k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK2,sK1)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_6261])).

cnf(c_152,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_437,plain,
    ( X0 != X1
    | X0 = k4_xboole_0(X2,X3)
    | k4_xboole_0(X2,X3) != X1 ),
    inference(instantiation,[status(thm)],[c_152])).

cnf(c_498,plain,
    ( X0 != k4_xboole_0(X1,X2)
    | X0 = k4_xboole_0(X3,X4)
    | k4_xboole_0(X3,X4) != k4_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_437])).

cnf(c_788,plain,
    ( X0 != k4_xboole_0(X1,X2)
    | X0 = k4_xboole_0(X3,k2_xboole_0(X4,X5))
    | k4_xboole_0(X3,k2_xboole_0(X4,X5)) != k4_xboole_0(X1,X2) ),
    inference(instantiation,[status(thm)],[c_498])).

cnf(c_2685,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) != k4_xboole_0(X0,X1)
    | k4_xboole_0(sK2,sK1) != k4_xboole_0(X0,X1)
    | k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_788])).

cnf(c_9433,plain,
    ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) != k4_xboole_0(sK2,sK1)
    | k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK0))
    | k4_xboole_0(sK2,sK1) != k4_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_2685])).

cnf(c_151,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2921,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_151])).

cnf(c_353,plain,
    ( k4_xboole_0(X0,X1) = k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_151])).

cnf(c_1332,plain,
    ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_334,plain,
    ( X0 != X1
    | k4_xboole_0(X0,X2) != X1
    | k4_xboole_0(X0,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_152])).

cnf(c_350,plain,
    ( k4_xboole_0(X0,X1) != k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,X1)
    | k4_xboole_0(k4_xboole_0(X0,X1),X2) != k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_1003,plain,
    ( k4_xboole_0(k4_xboole_0(sK2,sK1),sK0) != k4_xboole_0(sK2,k2_xboole_0(sK1,sK0))
    | k4_xboole_0(k4_xboole_0(sK2,sK1),sK0) = k4_xboole_0(sK2,sK1)
    | k4_xboole_0(sK2,sK1) != k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_350])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_325,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X2)
    | k4_xboole_0(k4_xboole_0(X0,X1),X2) != k4_xboole_0(X0,X1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_626,plain,
    ( r1_xboole_0(k4_xboole_0(sK2,sK1),sK0)
    | k4_xboole_0(k4_xboole_0(sK2,sK1),sK0) != k4_xboole_0(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_325])).

cnf(c_0,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_337,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | ~ r1_xboole_0(k4_xboole_0(X1,X2),X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_385,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,sK1),sK0)
    | r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_337])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_95,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | sK1 != X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_8])).

cnf(c_96,plain,
    ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_95])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_368,plain,
    ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_96,c_3])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_369,plain,
    ( k2_xboole_0(sK1,sK0) = sK1 ),
    inference(demodulation,[status(thm)],[c_368,c_2])).

cnf(c_7,negated_conjecture,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f24])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_45470,c_20295,c_9433,c_2921,c_1332,c_1003,c_626,c_385,c_369,c_7])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.31  % Computer   : n024.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 14:25:06 EST 2020
% 0.16/0.31  % CPUTime    : 
% 0.16/0.31  % Running in FOF mode
% 11.38/1.92  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.38/1.92  
% 11.38/1.92  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.38/1.92  
% 11.38/1.92  ------  iProver source info
% 11.38/1.92  
% 11.38/1.92  git: date: 2020-06-30 10:37:57 +0100
% 11.38/1.92  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.38/1.92  git: non_committed_changes: false
% 11.38/1.92  git: last_make_outside_of_git: false
% 11.38/1.92  
% 11.38/1.92  ------ 
% 11.38/1.92  
% 11.38/1.92  ------ Input Options
% 11.38/1.92  
% 11.38/1.92  --out_options                           all
% 11.38/1.92  --tptp_safe_out                         true
% 11.38/1.92  --problem_path                          ""
% 11.38/1.92  --include_path                          ""
% 11.38/1.92  --clausifier                            res/vclausify_rel
% 11.38/1.92  --clausifier_options                    --mode clausify
% 11.38/1.92  --stdin                                 false
% 11.38/1.92  --stats_out                             all
% 11.38/1.92  
% 11.38/1.92  ------ General Options
% 11.38/1.92  
% 11.38/1.92  --fof                                   false
% 11.38/1.92  --time_out_real                         305.
% 11.38/1.92  --time_out_virtual                      -1.
% 11.38/1.92  --symbol_type_check                     false
% 11.38/1.92  --clausify_out                          false
% 11.38/1.92  --sig_cnt_out                           false
% 11.38/1.92  --trig_cnt_out                          false
% 11.38/1.92  --trig_cnt_out_tolerance                1.
% 11.38/1.92  --trig_cnt_out_sk_spl                   false
% 11.38/1.92  --abstr_cl_out                          false
% 11.38/1.92  
% 11.38/1.92  ------ Global Options
% 11.38/1.92  
% 11.38/1.92  --schedule                              default
% 11.38/1.92  --add_important_lit                     false
% 11.38/1.92  --prop_solver_per_cl                    1000
% 11.38/1.92  --min_unsat_core                        false
% 11.38/1.92  --soft_assumptions                      false
% 11.38/1.92  --soft_lemma_size                       3
% 11.38/1.92  --prop_impl_unit_size                   0
% 11.38/1.92  --prop_impl_unit                        []
% 11.38/1.92  --share_sel_clauses                     true
% 11.38/1.92  --reset_solvers                         false
% 11.38/1.92  --bc_imp_inh                            [conj_cone]
% 11.38/1.92  --conj_cone_tolerance                   3.
% 11.38/1.92  --extra_neg_conj                        none
% 11.38/1.92  --large_theory_mode                     true
% 11.38/1.92  --prolific_symb_bound                   200
% 11.38/1.92  --lt_threshold                          2000
% 11.38/1.92  --clause_weak_htbl                      true
% 11.38/1.92  --gc_record_bc_elim                     false
% 11.38/1.92  
% 11.38/1.92  ------ Preprocessing Options
% 11.38/1.92  
% 11.38/1.92  --preprocessing_flag                    true
% 11.38/1.92  --time_out_prep_mult                    0.1
% 11.38/1.92  --splitting_mode                        input
% 11.38/1.92  --splitting_grd                         true
% 11.38/1.92  --splitting_cvd                         false
% 11.38/1.92  --splitting_cvd_svl                     false
% 11.38/1.92  --splitting_nvd                         32
% 11.38/1.92  --sub_typing                            true
% 11.38/1.92  --prep_gs_sim                           true
% 11.38/1.92  --prep_unflatten                        true
% 11.38/1.92  --prep_res_sim                          true
% 11.38/1.92  --prep_upred                            true
% 11.38/1.92  --prep_sem_filter                       exhaustive
% 11.38/1.92  --prep_sem_filter_out                   false
% 11.38/1.92  --pred_elim                             true
% 11.38/1.92  --res_sim_input                         true
% 11.38/1.92  --eq_ax_congr_red                       true
% 11.38/1.92  --pure_diseq_elim                       true
% 11.38/1.92  --brand_transform                       false
% 11.38/1.92  --non_eq_to_eq                          false
% 11.38/1.92  --prep_def_merge                        true
% 11.38/1.92  --prep_def_merge_prop_impl              false
% 11.38/1.92  --prep_def_merge_mbd                    true
% 11.38/1.92  --prep_def_merge_tr_red                 false
% 11.38/1.92  --prep_def_merge_tr_cl                  false
% 11.38/1.92  --smt_preprocessing                     true
% 11.38/1.92  --smt_ac_axioms                         fast
% 11.38/1.92  --preprocessed_out                      false
% 11.38/1.92  --preprocessed_stats                    false
% 11.38/1.92  
% 11.38/1.92  ------ Abstraction refinement Options
% 11.38/1.92  
% 11.38/1.92  --abstr_ref                             []
% 11.38/1.92  --abstr_ref_prep                        false
% 11.38/1.92  --abstr_ref_until_sat                   false
% 11.38/1.92  --abstr_ref_sig_restrict                funpre
% 11.38/1.92  --abstr_ref_af_restrict_to_split_sk     false
% 11.38/1.92  --abstr_ref_under                       []
% 11.38/1.92  
% 11.38/1.92  ------ SAT Options
% 11.38/1.92  
% 11.38/1.92  --sat_mode                              false
% 11.38/1.92  --sat_fm_restart_options                ""
% 11.38/1.92  --sat_gr_def                            false
% 11.38/1.92  --sat_epr_types                         true
% 11.38/1.92  --sat_non_cyclic_types                  false
% 11.38/1.92  --sat_finite_models                     false
% 11.38/1.92  --sat_fm_lemmas                         false
% 11.38/1.92  --sat_fm_prep                           false
% 11.38/1.92  --sat_fm_uc_incr                        true
% 11.38/1.92  --sat_out_model                         small
% 11.38/1.92  --sat_out_clauses                       false
% 11.38/1.92  
% 11.38/1.92  ------ QBF Options
% 11.38/1.92  
% 11.38/1.92  --qbf_mode                              false
% 11.38/1.92  --qbf_elim_univ                         false
% 11.38/1.92  --qbf_dom_inst                          none
% 11.38/1.92  --qbf_dom_pre_inst                      false
% 11.38/1.92  --qbf_sk_in                             false
% 11.38/1.92  --qbf_pred_elim                         true
% 11.38/1.92  --qbf_split                             512
% 11.38/1.92  
% 11.38/1.92  ------ BMC1 Options
% 11.38/1.92  
% 11.38/1.92  --bmc1_incremental                      false
% 11.38/1.92  --bmc1_axioms                           reachable_all
% 11.38/1.92  --bmc1_min_bound                        0
% 11.38/1.92  --bmc1_max_bound                        -1
% 11.38/1.92  --bmc1_max_bound_default                -1
% 11.38/1.92  --bmc1_symbol_reachability              true
% 11.38/1.92  --bmc1_property_lemmas                  false
% 11.38/1.92  --bmc1_k_induction                      false
% 11.38/1.92  --bmc1_non_equiv_states                 false
% 11.38/1.92  --bmc1_deadlock                         false
% 11.38/1.92  --bmc1_ucm                              false
% 11.38/1.92  --bmc1_add_unsat_core                   none
% 11.38/1.92  --bmc1_unsat_core_children              false
% 11.38/1.92  --bmc1_unsat_core_extrapolate_axioms    false
% 11.38/1.92  --bmc1_out_stat                         full
% 11.38/1.92  --bmc1_ground_init                      false
% 11.38/1.92  --bmc1_pre_inst_next_state              false
% 11.38/1.92  --bmc1_pre_inst_state                   false
% 11.38/1.92  --bmc1_pre_inst_reach_state             false
% 11.38/1.92  --bmc1_out_unsat_core                   false
% 11.38/1.92  --bmc1_aig_witness_out                  false
% 11.38/1.92  --bmc1_verbose                          false
% 11.38/1.92  --bmc1_dump_clauses_tptp                false
% 11.38/1.92  --bmc1_dump_unsat_core_tptp             false
% 11.38/1.92  --bmc1_dump_file                        -
% 11.38/1.92  --bmc1_ucm_expand_uc_limit              128
% 11.38/1.92  --bmc1_ucm_n_expand_iterations          6
% 11.38/1.92  --bmc1_ucm_extend_mode                  1
% 11.38/1.92  --bmc1_ucm_init_mode                    2
% 11.38/1.92  --bmc1_ucm_cone_mode                    none
% 11.38/1.92  --bmc1_ucm_reduced_relation_type        0
% 11.38/1.92  --bmc1_ucm_relax_model                  4
% 11.38/1.92  --bmc1_ucm_full_tr_after_sat            true
% 11.38/1.92  --bmc1_ucm_expand_neg_assumptions       false
% 11.38/1.92  --bmc1_ucm_layered_model                none
% 11.38/1.92  --bmc1_ucm_max_lemma_size               10
% 11.38/1.92  
% 11.38/1.92  ------ AIG Options
% 11.38/1.92  
% 11.38/1.92  --aig_mode                              false
% 11.38/1.92  
% 11.38/1.92  ------ Instantiation Options
% 11.38/1.92  
% 11.38/1.92  --instantiation_flag                    true
% 11.38/1.92  --inst_sos_flag                         false
% 11.38/1.92  --inst_sos_phase                        true
% 11.38/1.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.38/1.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.38/1.92  --inst_lit_sel_side                     num_symb
% 11.38/1.92  --inst_solver_per_active                1400
% 11.38/1.92  --inst_solver_calls_frac                1.
% 11.38/1.92  --inst_passive_queue_type               priority_queues
% 11.38/1.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.38/1.92  --inst_passive_queues_freq              [25;2]
% 11.38/1.92  --inst_dismatching                      true
% 11.38/1.92  --inst_eager_unprocessed_to_passive     true
% 11.38/1.92  --inst_prop_sim_given                   true
% 11.38/1.92  --inst_prop_sim_new                     false
% 11.38/1.92  --inst_subs_new                         false
% 11.38/1.92  --inst_eq_res_simp                      false
% 11.38/1.92  --inst_subs_given                       false
% 11.38/1.92  --inst_orphan_elimination               true
% 11.38/1.92  --inst_learning_loop_flag               true
% 11.38/1.92  --inst_learning_start                   3000
% 11.38/1.92  --inst_learning_factor                  2
% 11.38/1.92  --inst_start_prop_sim_after_learn       3
% 11.38/1.92  --inst_sel_renew                        solver
% 11.38/1.92  --inst_lit_activity_flag                true
% 11.38/1.92  --inst_restr_to_given                   false
% 11.38/1.92  --inst_activity_threshold               500
% 11.38/1.92  --inst_out_proof                        true
% 11.38/1.92  
% 11.38/1.92  ------ Resolution Options
% 11.38/1.92  
% 11.38/1.92  --resolution_flag                       true
% 11.38/1.92  --res_lit_sel                           adaptive
% 11.38/1.92  --res_lit_sel_side                      none
% 11.38/1.92  --res_ordering                          kbo
% 11.38/1.92  --res_to_prop_solver                    active
% 11.38/1.92  --res_prop_simpl_new                    false
% 11.38/1.92  --res_prop_simpl_given                  true
% 11.38/1.92  --res_passive_queue_type                priority_queues
% 11.38/1.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.38/1.92  --res_passive_queues_freq               [15;5]
% 11.38/1.92  --res_forward_subs                      full
% 11.38/1.92  --res_backward_subs                     full
% 11.38/1.92  --res_forward_subs_resolution           true
% 11.38/1.92  --res_backward_subs_resolution          true
% 11.38/1.92  --res_orphan_elimination                true
% 11.38/1.92  --res_time_limit                        2.
% 11.38/1.92  --res_out_proof                         true
% 11.38/1.92  
% 11.38/1.92  ------ Superposition Options
% 11.38/1.92  
% 11.38/1.92  --superposition_flag                    true
% 11.38/1.92  --sup_passive_queue_type                priority_queues
% 11.38/1.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.38/1.92  --sup_passive_queues_freq               [8;1;4]
% 11.38/1.92  --demod_completeness_check              fast
% 11.38/1.92  --demod_use_ground                      true
% 11.38/1.92  --sup_to_prop_solver                    passive
% 11.38/1.92  --sup_prop_simpl_new                    true
% 11.38/1.92  --sup_prop_simpl_given                  true
% 11.38/1.92  --sup_fun_splitting                     false
% 11.38/1.92  --sup_smt_interval                      50000
% 11.38/1.92  
% 11.38/1.92  ------ Superposition Simplification Setup
% 11.38/1.92  
% 11.38/1.92  --sup_indices_passive                   []
% 11.38/1.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.38/1.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.38/1.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.38/1.92  --sup_full_triv                         [TrivRules;PropSubs]
% 11.38/1.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.38/1.92  --sup_full_bw                           [BwDemod]
% 11.38/1.92  --sup_immed_triv                        [TrivRules]
% 11.38/1.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.38/1.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.38/1.92  --sup_immed_bw_main                     []
% 11.38/1.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.38/1.92  --sup_input_triv                        [Unflattening;TrivRules]
% 11.38/1.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.38/1.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.38/1.92  
% 11.38/1.92  ------ Combination Options
% 11.38/1.92  
% 11.38/1.92  --comb_res_mult                         3
% 11.38/1.92  --comb_sup_mult                         2
% 11.38/1.92  --comb_inst_mult                        10
% 11.38/1.92  
% 11.38/1.92  ------ Debug Options
% 11.38/1.92  
% 11.38/1.92  --dbg_backtrace                         false
% 11.38/1.92  --dbg_dump_prop_clauses                 false
% 11.38/1.92  --dbg_dump_prop_clauses_file            -
% 11.38/1.92  --dbg_out_stat                          false
% 11.38/1.92  ------ Parsing...
% 11.38/1.92  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.38/1.92  
% 11.38/1.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.38/1.92  
% 11.38/1.92  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.38/1.92  
% 11.38/1.92  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.38/1.92  ------ Proving...
% 11.38/1.92  ------ Problem Properties 
% 11.38/1.92  
% 11.38/1.92  
% 11.38/1.92  clauses                                 8
% 11.38/1.92  conjectures                             1
% 11.38/1.92  EPR                                     1
% 11.38/1.92  Horn                                    8
% 11.38/1.92  unary                                   5
% 11.38/1.92  binary                                  3
% 11.38/1.92  lits                                    11
% 11.38/1.92  lits eq                                 6
% 11.38/1.92  fd_pure                                 0
% 11.38/1.92  fd_pseudo                               0
% 11.38/1.92  fd_cond                                 0
% 11.38/1.92  fd_pseudo_cond                          0
% 11.38/1.92  AC symbols                              0
% 11.38/1.92  
% 11.38/1.92  ------ Schedule dynamic 5 is on 
% 11.38/1.92  
% 11.38/1.92  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.38/1.92  
% 11.38/1.92  
% 11.38/1.92  ------ 
% 11.38/1.92  Current options:
% 11.38/1.92  ------ 
% 11.38/1.92  
% 11.38/1.92  ------ Input Options
% 11.38/1.92  
% 11.38/1.92  --out_options                           all
% 11.38/1.92  --tptp_safe_out                         true
% 11.38/1.92  --problem_path                          ""
% 11.38/1.92  --include_path                          ""
% 11.38/1.92  --clausifier                            res/vclausify_rel
% 11.38/1.92  --clausifier_options                    --mode clausify
% 11.38/1.92  --stdin                                 false
% 11.38/1.92  --stats_out                             all
% 11.38/1.92  
% 11.38/1.92  ------ General Options
% 11.38/1.92  
% 11.38/1.92  --fof                                   false
% 11.38/1.92  --time_out_real                         305.
% 11.38/1.92  --time_out_virtual                      -1.
% 11.38/1.92  --symbol_type_check                     false
% 11.38/1.92  --clausify_out                          false
% 11.38/1.92  --sig_cnt_out                           false
% 11.38/1.92  --trig_cnt_out                          false
% 11.38/1.92  --trig_cnt_out_tolerance                1.
% 11.38/1.92  --trig_cnt_out_sk_spl                   false
% 11.38/1.92  --abstr_cl_out                          false
% 11.38/1.92  
% 11.38/1.92  ------ Global Options
% 11.38/1.92  
% 11.38/1.92  --schedule                              default
% 11.38/1.92  --add_important_lit                     false
% 11.38/1.92  --prop_solver_per_cl                    1000
% 11.38/1.92  --min_unsat_core                        false
% 11.38/1.92  --soft_assumptions                      false
% 11.38/1.92  --soft_lemma_size                       3
% 11.38/1.92  --prop_impl_unit_size                   0
% 11.38/1.92  --prop_impl_unit                        []
% 11.38/1.92  --share_sel_clauses                     true
% 11.38/1.92  --reset_solvers                         false
% 11.38/1.92  --bc_imp_inh                            [conj_cone]
% 11.38/1.92  --conj_cone_tolerance                   3.
% 11.38/1.92  --extra_neg_conj                        none
% 11.38/1.92  --large_theory_mode                     true
% 11.38/1.92  --prolific_symb_bound                   200
% 11.38/1.92  --lt_threshold                          2000
% 11.38/1.92  --clause_weak_htbl                      true
% 11.38/1.92  --gc_record_bc_elim                     false
% 11.38/1.92  
% 11.38/1.92  ------ Preprocessing Options
% 11.38/1.92  
% 11.38/1.92  --preprocessing_flag                    true
% 11.38/1.92  --time_out_prep_mult                    0.1
% 11.38/1.92  --splitting_mode                        input
% 11.38/1.92  --splitting_grd                         true
% 11.38/1.92  --splitting_cvd                         false
% 11.38/1.92  --splitting_cvd_svl                     false
% 11.38/1.92  --splitting_nvd                         32
% 11.38/1.92  --sub_typing                            true
% 11.38/1.92  --prep_gs_sim                           true
% 11.38/1.92  --prep_unflatten                        true
% 11.38/1.92  --prep_res_sim                          true
% 11.38/1.92  --prep_upred                            true
% 11.38/1.92  --prep_sem_filter                       exhaustive
% 11.38/1.92  --prep_sem_filter_out                   false
% 11.38/1.92  --pred_elim                             true
% 11.38/1.92  --res_sim_input                         true
% 11.38/1.92  --eq_ax_congr_red                       true
% 11.38/1.92  --pure_diseq_elim                       true
% 11.38/1.92  --brand_transform                       false
% 11.38/1.92  --non_eq_to_eq                          false
% 11.38/1.92  --prep_def_merge                        true
% 11.38/1.92  --prep_def_merge_prop_impl              false
% 11.38/1.92  --prep_def_merge_mbd                    true
% 11.38/1.92  --prep_def_merge_tr_red                 false
% 11.38/1.92  --prep_def_merge_tr_cl                  false
% 11.38/1.92  --smt_preprocessing                     true
% 11.38/1.92  --smt_ac_axioms                         fast
% 11.38/1.92  --preprocessed_out                      false
% 11.38/1.92  --preprocessed_stats                    false
% 11.38/1.92  
% 11.38/1.92  ------ Abstraction refinement Options
% 11.38/1.92  
% 11.38/1.92  --abstr_ref                             []
% 11.38/1.92  --abstr_ref_prep                        false
% 11.38/1.92  --abstr_ref_until_sat                   false
% 11.38/1.92  --abstr_ref_sig_restrict                funpre
% 11.38/1.92  --abstr_ref_af_restrict_to_split_sk     false
% 11.38/1.92  --abstr_ref_under                       []
% 11.38/1.92  
% 11.38/1.92  ------ SAT Options
% 11.38/1.92  
% 11.38/1.92  --sat_mode                              false
% 11.38/1.92  --sat_fm_restart_options                ""
% 11.38/1.92  --sat_gr_def                            false
% 11.38/1.92  --sat_epr_types                         true
% 11.38/1.92  --sat_non_cyclic_types                  false
% 11.38/1.92  --sat_finite_models                     false
% 11.38/1.92  --sat_fm_lemmas                         false
% 11.38/1.92  --sat_fm_prep                           false
% 11.38/1.92  --sat_fm_uc_incr                        true
% 11.38/1.92  --sat_out_model                         small
% 11.38/1.92  --sat_out_clauses                       false
% 11.38/1.92  
% 11.38/1.92  ------ QBF Options
% 11.38/1.92  
% 11.38/1.92  --qbf_mode                              false
% 11.38/1.92  --qbf_elim_univ                         false
% 11.38/1.92  --qbf_dom_inst                          none
% 11.38/1.92  --qbf_dom_pre_inst                      false
% 11.38/1.92  --qbf_sk_in                             false
% 11.38/1.92  --qbf_pred_elim                         true
% 11.38/1.92  --qbf_split                             512
% 11.38/1.92  
% 11.38/1.92  ------ BMC1 Options
% 11.38/1.92  
% 11.38/1.92  --bmc1_incremental                      false
% 11.38/1.92  --bmc1_axioms                           reachable_all
% 11.38/1.92  --bmc1_min_bound                        0
% 11.38/1.92  --bmc1_max_bound                        -1
% 11.38/1.92  --bmc1_max_bound_default                -1
% 11.38/1.92  --bmc1_symbol_reachability              true
% 11.38/1.92  --bmc1_property_lemmas                  false
% 11.38/1.92  --bmc1_k_induction                      false
% 11.38/1.92  --bmc1_non_equiv_states                 false
% 11.38/1.92  --bmc1_deadlock                         false
% 11.38/1.92  --bmc1_ucm                              false
% 11.38/1.92  --bmc1_add_unsat_core                   none
% 11.38/1.92  --bmc1_unsat_core_children              false
% 11.38/1.92  --bmc1_unsat_core_extrapolate_axioms    false
% 11.38/1.92  --bmc1_out_stat                         full
% 11.38/1.92  --bmc1_ground_init                      false
% 11.38/1.92  --bmc1_pre_inst_next_state              false
% 11.38/1.92  --bmc1_pre_inst_state                   false
% 11.38/1.92  --bmc1_pre_inst_reach_state             false
% 11.38/1.92  --bmc1_out_unsat_core                   false
% 11.38/1.92  --bmc1_aig_witness_out                  false
% 11.38/1.92  --bmc1_verbose                          false
% 11.38/1.92  --bmc1_dump_clauses_tptp                false
% 11.38/1.92  --bmc1_dump_unsat_core_tptp             false
% 11.38/1.92  --bmc1_dump_file                        -
% 11.38/1.92  --bmc1_ucm_expand_uc_limit              128
% 11.38/1.92  --bmc1_ucm_n_expand_iterations          6
% 11.38/1.92  --bmc1_ucm_extend_mode                  1
% 11.38/1.92  --bmc1_ucm_init_mode                    2
% 11.38/1.92  --bmc1_ucm_cone_mode                    none
% 11.38/1.92  --bmc1_ucm_reduced_relation_type        0
% 11.38/1.92  --bmc1_ucm_relax_model                  4
% 11.38/1.92  --bmc1_ucm_full_tr_after_sat            true
% 11.38/1.92  --bmc1_ucm_expand_neg_assumptions       false
% 11.38/1.92  --bmc1_ucm_layered_model                none
% 11.38/1.92  --bmc1_ucm_max_lemma_size               10
% 11.38/1.92  
% 11.38/1.92  ------ AIG Options
% 11.38/1.92  
% 11.38/1.92  --aig_mode                              false
% 11.38/1.92  
% 11.38/1.92  ------ Instantiation Options
% 11.38/1.92  
% 11.38/1.92  --instantiation_flag                    true
% 11.38/1.92  --inst_sos_flag                         false
% 11.38/1.92  --inst_sos_phase                        true
% 11.38/1.92  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.38/1.92  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.38/1.92  --inst_lit_sel_side                     none
% 11.38/1.92  --inst_solver_per_active                1400
% 11.38/1.92  --inst_solver_calls_frac                1.
% 11.38/1.92  --inst_passive_queue_type               priority_queues
% 11.38/1.92  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.38/1.92  --inst_passive_queues_freq              [25;2]
% 11.38/1.92  --inst_dismatching                      true
% 11.38/1.92  --inst_eager_unprocessed_to_passive     true
% 11.38/1.92  --inst_prop_sim_given                   true
% 11.38/1.92  --inst_prop_sim_new                     false
% 11.38/1.92  --inst_subs_new                         false
% 11.38/1.92  --inst_eq_res_simp                      false
% 11.38/1.92  --inst_subs_given                       false
% 11.38/1.92  --inst_orphan_elimination               true
% 11.38/1.92  --inst_learning_loop_flag               true
% 11.38/1.92  --inst_learning_start                   3000
% 11.38/1.92  --inst_learning_factor                  2
% 11.38/1.92  --inst_start_prop_sim_after_learn       3
% 11.38/1.92  --inst_sel_renew                        solver
% 11.38/1.92  --inst_lit_activity_flag                true
% 11.38/1.92  --inst_restr_to_given                   false
% 11.38/1.92  --inst_activity_threshold               500
% 11.38/1.92  --inst_out_proof                        true
% 11.38/1.92  
% 11.38/1.92  ------ Resolution Options
% 11.38/1.92  
% 11.38/1.92  --resolution_flag                       false
% 11.38/1.92  --res_lit_sel                           adaptive
% 11.38/1.92  --res_lit_sel_side                      none
% 11.38/1.92  --res_ordering                          kbo
% 11.38/1.92  --res_to_prop_solver                    active
% 11.38/1.92  --res_prop_simpl_new                    false
% 11.38/1.92  --res_prop_simpl_given                  true
% 11.38/1.92  --res_passive_queue_type                priority_queues
% 11.38/1.92  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.38/1.92  --res_passive_queues_freq               [15;5]
% 11.38/1.92  --res_forward_subs                      full
% 11.38/1.92  --res_backward_subs                     full
% 11.38/1.92  --res_forward_subs_resolution           true
% 11.38/1.92  --res_backward_subs_resolution          true
% 11.38/1.92  --res_orphan_elimination                true
% 11.38/1.92  --res_time_limit                        2.
% 11.38/1.92  --res_out_proof                         true
% 11.38/1.92  
% 11.38/1.92  ------ Superposition Options
% 11.38/1.92  
% 11.38/1.92  --superposition_flag                    true
% 11.38/1.92  --sup_passive_queue_type                priority_queues
% 11.38/1.92  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.38/1.92  --sup_passive_queues_freq               [8;1;4]
% 11.38/1.92  --demod_completeness_check              fast
% 11.38/1.92  --demod_use_ground                      true
% 11.38/1.92  --sup_to_prop_solver                    passive
% 11.38/1.92  --sup_prop_simpl_new                    true
% 11.38/1.92  --sup_prop_simpl_given                  true
% 11.38/1.92  --sup_fun_splitting                     false
% 11.38/1.92  --sup_smt_interval                      50000
% 11.38/1.92  
% 11.38/1.92  ------ Superposition Simplification Setup
% 11.38/1.92  
% 11.38/1.92  --sup_indices_passive                   []
% 11.38/1.92  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.38/1.92  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.38/1.92  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.38/1.92  --sup_full_triv                         [TrivRules;PropSubs]
% 11.38/1.92  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.38/1.92  --sup_full_bw                           [BwDemod]
% 11.38/1.92  --sup_immed_triv                        [TrivRules]
% 11.38/1.92  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.38/1.92  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.38/1.92  --sup_immed_bw_main                     []
% 11.38/1.92  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.38/1.92  --sup_input_triv                        [Unflattening;TrivRules]
% 11.38/1.92  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.38/1.92  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.38/1.92  
% 11.38/1.92  ------ Combination Options
% 11.38/1.92  
% 11.38/1.92  --comb_res_mult                         3
% 11.38/1.92  --comb_sup_mult                         2
% 11.38/1.92  --comb_inst_mult                        10
% 11.38/1.92  
% 11.38/1.92  ------ Debug Options
% 11.38/1.92  
% 11.38/1.92  --dbg_backtrace                         false
% 11.38/1.92  --dbg_dump_prop_clauses                 false
% 11.38/1.92  --dbg_dump_prop_clauses_file            -
% 11.38/1.92  --dbg_out_stat                          false
% 11.38/1.92  
% 11.38/1.92  
% 11.38/1.92  
% 11.38/1.92  
% 11.38/1.92  ------ Proving...
% 11.38/1.92  
% 11.38/1.92  
% 11.38/1.92  % SZS status Theorem for theBenchmark.p
% 11.38/1.92  
% 11.38/1.92  % SZS output start CNFRefutation for theBenchmark.p
% 11.38/1.92  
% 11.38/1.92  fof(f5,axiom,(
% 11.38/1.92    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)),
% 11.38/1.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.92  
% 11.38/1.92  fof(f20,plain,(
% 11.38/1.92    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 11.38/1.92    inference(cnf_transformation,[],[f5])).
% 11.38/1.92  
% 11.38/1.92  fof(f6,axiom,(
% 11.38/1.92    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 11.38/1.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.92  
% 11.38/1.92  fof(f13,plain,(
% 11.38/1.92    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 11.38/1.92    inference(nnf_transformation,[],[f6])).
% 11.38/1.92  
% 11.38/1.92  fof(f22,plain,(
% 11.38/1.92    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 11.38/1.92    inference(cnf_transformation,[],[f13])).
% 11.38/1.92  
% 11.38/1.92  fof(f1,axiom,(
% 11.38/1.92    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 11.38/1.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.92  
% 11.38/1.92  fof(f10,plain,(
% 11.38/1.92    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 11.38/1.92    inference(ennf_transformation,[],[f1])).
% 11.38/1.92  
% 11.38/1.92  fof(f16,plain,(
% 11.38/1.92    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 11.38/1.92    inference(cnf_transformation,[],[f10])).
% 11.38/1.92  
% 11.38/1.92  fof(f2,axiom,(
% 11.38/1.92    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.38/1.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.92  
% 11.38/1.92  fof(f9,plain,(
% 11.38/1.92    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 11.38/1.92    inference(unused_predicate_definition_removal,[],[f2])).
% 11.38/1.92  
% 11.38/1.92  fof(f11,plain,(
% 11.38/1.92    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 11.38/1.92    inference(ennf_transformation,[],[f9])).
% 11.38/1.92  
% 11.38/1.92  fof(f17,plain,(
% 11.38/1.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.38/1.92    inference(cnf_transformation,[],[f11])).
% 11.38/1.92  
% 11.38/1.92  fof(f7,conjecture,(
% 11.38/1.92    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 11.38/1.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.92  
% 11.38/1.92  fof(f8,negated_conjecture,(
% 11.38/1.92    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 11.38/1.92    inference(negated_conjecture,[],[f7])).
% 11.38/1.92  
% 11.38/1.92  fof(f12,plain,(
% 11.38/1.92    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1))),
% 11.38/1.92    inference(ennf_transformation,[],[f8])).
% 11.38/1.92  
% 11.38/1.92  fof(f14,plain,(
% 11.38/1.92    ? [X0,X1,X2] : (~r1_xboole_0(X0,k4_xboole_0(X2,X1)) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1))),
% 11.38/1.92    introduced(choice_axiom,[])).
% 11.38/1.92  
% 11.38/1.92  fof(f15,plain,(
% 11.38/1.92    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) & r1_tarski(sK0,sK1)),
% 11.38/1.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 11.38/1.92  
% 11.38/1.92  fof(f23,plain,(
% 11.38/1.92    r1_tarski(sK0,sK1)),
% 11.38/1.92    inference(cnf_transformation,[],[f15])).
% 11.38/1.92  
% 11.38/1.92  fof(f4,axiom,(
% 11.38/1.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.38/1.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.92  
% 11.38/1.92  fof(f19,plain,(
% 11.38/1.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.38/1.92    inference(cnf_transformation,[],[f4])).
% 11.38/1.92  
% 11.38/1.92  fof(f3,axiom,(
% 11.38/1.92    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.38/1.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.38/1.92  
% 11.38/1.92  fof(f18,plain,(
% 11.38/1.92    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.38/1.92    inference(cnf_transformation,[],[f3])).
% 11.38/1.92  
% 11.38/1.92  fof(f24,plain,(
% 11.38/1.92    ~r1_xboole_0(sK0,k4_xboole_0(sK2,sK1))),
% 11.38/1.92    inference(cnf_transformation,[],[f15])).
% 11.38/1.92  
% 11.38/1.92  cnf(c_4,plain,
% 11.38/1.92      ( k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.38/1.92      inference(cnf_transformation,[],[f20]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_26867,plain,
% 11.38/1.92      ( k4_xboole_0(k4_xboole_0(sK2,sK1),X0) = k4_xboole_0(sK2,k2_xboole_0(sK1,X0)) ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_4]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_45470,plain,
% 11.38/1.92      ( k4_xboole_0(k4_xboole_0(sK2,sK1),sK0) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_26867]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_154,plain,
% 11.38/1.92      ( X0 != X1 | X2 != X3 | k4_xboole_0(X0,X2) = k4_xboole_0(X1,X3) ),
% 11.38/1.92      theory(equality) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_6261,plain,
% 11.38/1.92      ( X0 != X1
% 11.38/1.92      | k2_xboole_0(X2,X3) != X4
% 11.38/1.92      | k4_xboole_0(X0,k2_xboole_0(X2,X3)) = k4_xboole_0(X1,X4) ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_154]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_20295,plain,
% 11.38/1.92      ( k2_xboole_0(sK1,sK0) != sK1
% 11.38/1.92      | k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) = k4_xboole_0(sK2,sK1)
% 11.38/1.92      | sK2 != sK2 ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_6261]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_152,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_437,plain,
% 11.38/1.92      ( X0 != X1 | X0 = k4_xboole_0(X2,X3) | k4_xboole_0(X2,X3) != X1 ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_152]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_498,plain,
% 11.38/1.92      ( X0 != k4_xboole_0(X1,X2)
% 11.38/1.92      | X0 = k4_xboole_0(X3,X4)
% 11.38/1.92      | k4_xboole_0(X3,X4) != k4_xboole_0(X1,X2) ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_437]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_788,plain,
% 11.38/1.92      ( X0 != k4_xboole_0(X1,X2)
% 11.38/1.92      | X0 = k4_xboole_0(X3,k2_xboole_0(X4,X5))
% 11.38/1.92      | k4_xboole_0(X3,k2_xboole_0(X4,X5)) != k4_xboole_0(X1,X2) ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_498]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_2685,plain,
% 11.38/1.92      ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) != k4_xboole_0(X0,X1)
% 11.38/1.92      | k4_xboole_0(sK2,sK1) != k4_xboole_0(X0,X1)
% 11.38/1.92      | k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_788]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_9433,plain,
% 11.38/1.92      ( k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) != k4_xboole_0(sK2,sK1)
% 11.38/1.92      | k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,k2_xboole_0(sK1,sK0))
% 11.38/1.92      | k4_xboole_0(sK2,sK1) != k4_xboole_0(sK2,sK1) ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_2685]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_151,plain,( X0 = X0 ),theory(equality) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_2921,plain,
% 11.38/1.92      ( sK2 = sK2 ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_151]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_353,plain,
% 11.38/1.92      ( k4_xboole_0(X0,X1) = k4_xboole_0(X0,X1) ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_151]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_1332,plain,
% 11.38/1.92      ( k4_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK1) ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_353]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_334,plain,
% 11.38/1.92      ( X0 != X1 | k4_xboole_0(X0,X2) != X1 | k4_xboole_0(X0,X2) = X0 ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_152]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_350,plain,
% 11.38/1.92      ( k4_xboole_0(X0,X1) != k4_xboole_0(X0,k2_xboole_0(X1,X2))
% 11.38/1.92      | k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,X1)
% 11.38/1.92      | k4_xboole_0(k4_xboole_0(X0,X1),X2) != k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_334]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_1003,plain,
% 11.38/1.92      ( k4_xboole_0(k4_xboole_0(sK2,sK1),sK0) != k4_xboole_0(sK2,k2_xboole_0(sK1,sK0))
% 11.38/1.92      | k4_xboole_0(k4_xboole_0(sK2,sK1),sK0) = k4_xboole_0(sK2,sK1)
% 11.38/1.92      | k4_xboole_0(sK2,sK1) != k4_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_350]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_5,plain,
% 11.38/1.92      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 11.38/1.92      inference(cnf_transformation,[],[f22]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_325,plain,
% 11.38/1.92      ( r1_xboole_0(k4_xboole_0(X0,X1),X2)
% 11.38/1.92      | k4_xboole_0(k4_xboole_0(X0,X1),X2) != k4_xboole_0(X0,X1) ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_5]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_626,plain,
% 11.38/1.92      ( r1_xboole_0(k4_xboole_0(sK2,sK1),sK0)
% 11.38/1.92      | k4_xboole_0(k4_xboole_0(sK2,sK1),sK0) != k4_xboole_0(sK2,sK1) ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_325]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_0,plain,
% 11.38/1.92      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0) ),
% 11.38/1.92      inference(cnf_transformation,[],[f16]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_337,plain,
% 11.38/1.92      ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
% 11.38/1.92      | ~ r1_xboole_0(k4_xboole_0(X1,X2),X0) ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_0]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_385,plain,
% 11.38/1.92      ( ~ r1_xboole_0(k4_xboole_0(sK2,sK1),sK0)
% 11.38/1.92      | r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
% 11.38/1.92      inference(instantiation,[status(thm)],[c_337]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_1,plain,
% 11.38/1.92      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 11.38/1.92      inference(cnf_transformation,[],[f17]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_8,negated_conjecture,
% 11.38/1.92      ( r1_tarski(sK0,sK1) ),
% 11.38/1.92      inference(cnf_transformation,[],[f23]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_95,plain,
% 11.38/1.92      ( k4_xboole_0(X0,X1) = k1_xboole_0 | sK1 != X1 | sK0 != X0 ),
% 11.38/1.92      inference(resolution_lifted,[status(thm)],[c_1,c_8]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_96,plain,
% 11.38/1.92      ( k4_xboole_0(sK0,sK1) = k1_xboole_0 ),
% 11.38/1.92      inference(unflattening,[status(thm)],[c_95]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_3,plain,
% 11.38/1.92      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 11.38/1.92      inference(cnf_transformation,[],[f19]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_368,plain,
% 11.38/1.92      ( k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k1_xboole_0) ),
% 11.38/1.92      inference(superposition,[status(thm)],[c_96,c_3]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_2,plain,
% 11.38/1.92      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.38/1.92      inference(cnf_transformation,[],[f18]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_369,plain,
% 11.38/1.92      ( k2_xboole_0(sK1,sK0) = sK1 ),
% 11.38/1.92      inference(demodulation,[status(thm)],[c_368,c_2]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(c_7,negated_conjecture,
% 11.38/1.92      ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,sK1)) ),
% 11.38/1.92      inference(cnf_transformation,[],[f24]) ).
% 11.38/1.92  
% 11.38/1.92  cnf(contradiction,plain,
% 11.38/1.92      ( $false ),
% 11.38/1.92      inference(minisat,
% 11.38/1.92                [status(thm)],
% 11.38/1.92                [c_45470,c_20295,c_9433,c_2921,c_1332,c_1003,c_626,c_385,
% 11.38/1.92                 c_369,c_7]) ).
% 11.38/1.92  
% 11.38/1.92  
% 11.38/1.92  % SZS output end CNFRefutation for theBenchmark.p
% 11.38/1.92  
% 11.38/1.92  ------                               Statistics
% 11.38/1.92  
% 11.38/1.92  ------ General
% 11.38/1.92  
% 11.38/1.92  abstr_ref_over_cycles:                  0
% 11.38/1.92  abstr_ref_under_cycles:                 0
% 11.38/1.92  gc_basic_clause_elim:                   0
% 11.38/1.92  forced_gc_time:                         0
% 11.38/1.92  parsing_time:                           0.011
% 11.38/1.92  unif_index_cands_time:                  0.
% 11.38/1.92  unif_index_add_time:                    0.
% 11.38/1.92  orderings_time:                         0.
% 11.38/1.92  out_proof_time:                         0.008
% 11.38/1.92  total_time:                             1.134
% 11.38/1.92  num_of_symbols:                         39
% 11.38/1.92  num_of_terms:                           52001
% 11.38/1.92  
% 11.38/1.92  ------ Preprocessing
% 11.38/1.92  
% 11.38/1.92  num_of_splits:                          0
% 11.38/1.92  num_of_split_atoms:                     0
% 11.38/1.92  num_of_reused_defs:                     0
% 11.38/1.92  num_eq_ax_congr_red:                    3
% 11.38/1.92  num_of_sem_filtered_clauses:            1
% 11.38/1.92  num_of_subtypes:                        0
% 11.38/1.92  monotx_restored_types:                  0
% 11.38/1.92  sat_num_of_epr_types:                   0
% 11.38/1.92  sat_num_of_non_cyclic_types:            0
% 11.38/1.92  sat_guarded_non_collapsed_types:        0
% 11.38/1.92  num_pure_diseq_elim:                    0
% 11.38/1.92  simp_replaced_by:                       0
% 11.38/1.92  res_preprocessed:                       44
% 11.38/1.92  prep_upred:                             0
% 11.38/1.92  prep_unflattend:                        2
% 11.38/1.92  smt_new_axioms:                         0
% 11.38/1.92  pred_elim_cands:                        1
% 11.38/1.92  pred_elim:                              1
% 11.38/1.92  pred_elim_cl:                           1
% 11.38/1.92  pred_elim_cycles:                       3
% 11.38/1.92  merged_defs:                            8
% 11.38/1.92  merged_defs_ncl:                        0
% 11.38/1.92  bin_hyper_res:                          8
% 11.38/1.92  prep_cycles:                            4
% 11.38/1.92  pred_elim_time:                         0.
% 11.38/1.92  splitting_time:                         0.
% 11.38/1.92  sem_filter_time:                        0.
% 11.38/1.92  monotx_time:                            0.
% 11.38/1.92  subtype_inf_time:                       0.
% 11.38/1.92  
% 11.38/1.92  ------ Problem properties
% 11.38/1.92  
% 11.38/1.92  clauses:                                8
% 11.38/1.92  conjectures:                            1
% 11.38/1.92  epr:                                    1
% 11.38/1.92  horn:                                   8
% 11.38/1.92  ground:                                 2
% 11.38/1.92  unary:                                  5
% 11.38/1.92  binary:                                 3
% 11.38/1.92  lits:                                   11
% 11.38/1.92  lits_eq:                                6
% 11.38/1.92  fd_pure:                                0
% 11.38/1.92  fd_pseudo:                              0
% 11.38/1.92  fd_cond:                                0
% 11.38/1.92  fd_pseudo_cond:                         0
% 11.38/1.92  ac_symbols:                             0
% 11.38/1.92  
% 11.38/1.92  ------ Propositional Solver
% 11.38/1.92  
% 11.38/1.92  prop_solver_calls:                      31
% 11.38/1.92  prop_fast_solver_calls:                 371
% 11.38/1.92  smt_solver_calls:                       0
% 11.38/1.92  smt_fast_solver_calls:                  0
% 11.38/1.92  prop_num_of_clauses:                    12646
% 11.38/1.92  prop_preprocess_simplified:             12085
% 11.38/1.92  prop_fo_subsumed:                       0
% 11.38/1.92  prop_solver_time:                       0.
% 11.38/1.92  smt_solver_time:                        0.
% 11.38/1.92  smt_fast_solver_time:                   0.
% 11.38/1.92  prop_fast_solver_time:                  0.
% 11.38/1.92  prop_unsat_core_time:                   0.001
% 11.38/1.92  
% 11.38/1.92  ------ QBF
% 11.38/1.92  
% 11.38/1.92  qbf_q_res:                              0
% 11.38/1.92  qbf_num_tautologies:                    0
% 11.38/1.92  qbf_prep_cycles:                        0
% 11.38/1.92  
% 11.38/1.92  ------ BMC1
% 11.38/1.92  
% 11.38/1.92  bmc1_current_bound:                     -1
% 11.38/1.92  bmc1_last_solved_bound:                 -1
% 11.38/1.92  bmc1_unsat_core_size:                   -1
% 11.38/1.92  bmc1_unsat_core_parents_size:           -1
% 11.38/1.92  bmc1_merge_next_fun:                    0
% 11.38/1.92  bmc1_unsat_core_clauses_time:           0.
% 11.38/1.92  
% 11.38/1.92  ------ Instantiation
% 11.38/1.92  
% 11.38/1.92  inst_num_of_clauses:                    2352
% 11.38/1.92  inst_num_in_passive:                    1356
% 11.38/1.92  inst_num_in_active:                     907
% 11.38/1.92  inst_num_in_unprocessed:                88
% 11.38/1.92  inst_num_of_loops:                      1030
% 11.38/1.92  inst_num_of_learning_restarts:          0
% 11.38/1.92  inst_num_moves_active_passive:          118
% 11.38/1.92  inst_lit_activity:                      0
% 11.38/1.92  inst_lit_activity_moves:                0
% 11.38/1.92  inst_num_tautologies:                   0
% 11.38/1.92  inst_num_prop_implied:                  0
% 11.38/1.92  inst_num_existing_simplified:           0
% 11.38/1.92  inst_num_eq_res_simplified:             0
% 11.38/1.92  inst_num_child_elim:                    0
% 11.38/1.92  inst_num_of_dismatching_blockings:      4935
% 11.38/1.92  inst_num_of_non_proper_insts:           4223
% 11.38/1.92  inst_num_of_duplicates:                 0
% 11.38/1.92  inst_inst_num_from_inst_to_res:         0
% 11.38/1.92  inst_dismatching_checking_time:         0.
% 11.38/1.92  
% 11.38/1.92  ------ Resolution
% 11.38/1.92  
% 11.38/1.92  res_num_of_clauses:                     0
% 11.38/1.92  res_num_in_passive:                     0
% 11.38/1.92  res_num_in_active:                      0
% 11.38/1.92  res_num_of_loops:                       48
% 11.38/1.92  res_forward_subset_subsumed:            278
% 11.38/1.92  res_backward_subset_subsumed:           2
% 11.38/1.92  res_forward_subsumed:                   0
% 11.38/1.92  res_backward_subsumed:                  0
% 11.38/1.92  res_forward_subsumption_resolution:     0
% 11.38/1.92  res_backward_subsumption_resolution:    0
% 11.38/1.92  res_clause_to_clause_subsumption:       18237
% 11.38/1.92  res_orphan_elimination:                 0
% 11.38/1.92  res_tautology_del:                      331
% 11.38/1.92  res_num_eq_res_simplified:              0
% 11.38/1.92  res_num_sel_changes:                    0
% 11.38/1.92  res_moves_from_active_to_pass:          0
% 11.38/1.92  
% 11.38/1.92  ------ Superposition
% 11.38/1.92  
% 11.38/1.92  sup_time_total:                         0.
% 11.38/1.92  sup_time_generating:                    0.
% 11.38/1.92  sup_time_sim_full:                      0.
% 11.38/1.92  sup_time_sim_immed:                     0.
% 11.38/1.92  
% 11.38/1.92  sup_num_of_clauses:                     2863
% 11.38/1.92  sup_num_in_active:                      201
% 11.38/1.92  sup_num_in_passive:                     2662
% 11.38/1.92  sup_num_of_loops:                       204
% 11.38/1.92  sup_fw_superposition:                   3306
% 11.38/1.92  sup_bw_superposition:                   2938
% 11.38/1.92  sup_immediate_simplified:               3339
% 11.38/1.92  sup_given_eliminated:                   0
% 11.38/1.92  comparisons_done:                       0
% 11.38/1.92  comparisons_avoided:                    0
% 11.38/1.92  
% 11.38/1.92  ------ Simplifications
% 11.38/1.92  
% 11.38/1.92  
% 11.38/1.92  sim_fw_subset_subsumed:                 0
% 11.38/1.92  sim_bw_subset_subsumed:                 0
% 11.38/1.92  sim_fw_subsumed:                        957
% 11.38/1.92  sim_bw_subsumed:                        14
% 11.38/1.92  sim_fw_subsumption_res:                 0
% 11.38/1.92  sim_bw_subsumption_res:                 0
% 11.38/1.92  sim_tautology_del:                      0
% 11.38/1.92  sim_eq_tautology_del:                   485
% 11.38/1.92  sim_eq_res_simp:                        15
% 11.38/1.92  sim_fw_demodulated:                     2167
% 11.38/1.92  sim_bw_demodulated:                     26
% 11.38/1.92  sim_light_normalised:                   1415
% 11.38/1.92  sim_joinable_taut:                      0
% 11.38/1.92  sim_joinable_simp:                      0
% 11.38/1.92  sim_ac_normalised:                      0
% 11.38/1.92  sim_smt_subsumption:                    0
% 11.38/1.92  
%------------------------------------------------------------------------------
