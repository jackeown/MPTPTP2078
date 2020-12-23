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
% DateTime   : Thu Dec  3 11:38:28 EST 2020

% Result     : Theorem 11.64s
% Output     : CNFRefutation 11.64s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 154 expanded)
%              Number of clauses        :   36 (  60 expanded)
%              Number of leaves         :    9 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :   95 ( 297 expanded)
%              Number of equality atoms :   68 ( 200 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :    8 (   1 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r2_hidden(X3,X0)
          & k3_xboole_0(X1,X2) = k1_tarski(X3)
          & r1_tarski(X0,X1) )
       => k3_xboole_0(X0,X2) = k1_tarski(X3) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( k3_xboole_0(X0,X2) != k1_tarski(X3)
      & r2_hidden(X3,X0)
      & k3_xboole_0(X1,X2) = k1_tarski(X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( k3_xboole_0(X0,X2) != k1_tarski(X3)
        & r2_hidden(X3,X0)
        & k3_xboole_0(X1,X2) = k1_tarski(X3)
        & r1_tarski(X0,X1) )
   => ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
      & r2_hidden(sK3,sK0)
      & k3_xboole_0(sK1,sK2) = k1_tarski(sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3)
    & r2_hidden(sK3,sK0)
    & k3_xboole_0(sK1,sK2) = k1_tarski(sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f22])).

fof(f39,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f38,plain,(
    k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f37,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_122,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) = X1
    | sK3 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_14])).

cnf(c_123,plain,
    ( k2_xboole_0(k1_tarski(sK3),sK0) = sK0 ),
    inference(unflattening,[status(thm)],[c_122])).

cnf(c_7,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_596,plain,
    ( k3_xboole_0(k1_tarski(sK3),sK0) = k1_tarski(sK3) ),
    inference(superposition,[status(thm)],[c_123,c_7])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1232,plain,
    ( k3_xboole_0(sK0,k1_tarski(sK3)) = k1_tarski(sK3) ),
    inference(superposition,[status(thm)],[c_596,c_0])).

cnf(c_9,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2478,plain,
    ( k2_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,k2_xboole_0(k1_tarski(sK3),X0)) ),
    inference(superposition,[status(thm)],[c_1232,c_9])).

cnf(c_15,negated_conjecture,
    ( k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_507,plain,
    ( k3_xboole_0(sK2,sK1) = k1_tarski(sK3) ),
    inference(superposition,[status(thm)],[c_15,c_0])).

cnf(c_768,plain,
    ( k2_xboole_0(k1_tarski(sK3),k3_xboole_0(sK2,X0)) = k3_xboole_0(sK2,k2_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_507,c_9])).

cnf(c_1923,plain,
    ( k2_xboole_0(k1_tarski(sK3),k3_xboole_0(X0,sK2)) = k3_xboole_0(sK2,k2_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_0,c_768])).

cnf(c_29790,plain,
    ( k3_xboole_0(sK0,k2_xboole_0(k1_tarski(sK3),sK2)) = k3_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[status(thm)],[c_2478,c_1923])).

cnf(c_8,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_684,plain,
    ( k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_8,c_7])).

cnf(c_1927,plain,
    ( k3_xboole_0(sK2,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k1_tarski(sK3),sK2) ),
    inference(superposition,[status(thm)],[c_684,c_768])).

cnf(c_680,plain,
    ( k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[status(thm)],[c_7,c_8])).

cnf(c_10,plain,
    ( k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_764,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k2_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_0,c_9])).

cnf(c_787,plain,
    ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) = k2_xboole_0(k3_xboole_0(X1,k2_xboole_0(X0,X2)),k3_xboole_0(X2,X0)) ),
    inference(light_normalisation,[status(thm)],[c_10,c_10,c_764])).

cnf(c_889,plain,
    ( k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X0,X1)),k3_xboole_0(X1,X0)) = k3_xboole_0(k3_xboole_0(X0,k2_xboole_0(X0,X1)),k2_xboole_0(X1,X0)) ),
    inference(superposition,[status(thm)],[c_680,c_787])).

cnf(c_678,plain,
    ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_8])).

cnf(c_899,plain,
    ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_889,c_7,c_678])).

cnf(c_1934,plain,
    ( k2_xboole_0(k1_tarski(sK3),sK2) = sK2 ),
    inference(demodulation,[status(thm)],[c_1927,c_899])).

cnf(c_16,negated_conjecture,
    ( r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_296,plain,
    ( r1_tarski(sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_300,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2239,plain,
    ( k2_xboole_0(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_296,c_300])).

cnf(c_2585,plain,
    ( k3_xboole_0(sK0,sK1) = sK0 ),
    inference(superposition,[status(thm)],[c_2239,c_7])).

cnf(c_3481,plain,
    ( k2_xboole_0(sK1,sK0) = sK1 ),
    inference(superposition,[status(thm)],[c_2585,c_678])).

cnf(c_29791,plain,
    ( k3_xboole_0(sK0,sK2) = k1_tarski(sK3) ),
    inference(light_normalisation,[status(thm)],[c_29790,c_507,c_1934,c_3481])).

cnf(c_13,negated_conjecture,
    ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29791,c_13])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:31:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 11.64/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.64/1.98  
% 11.64/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.64/1.98  
% 11.64/1.98  ------  iProver source info
% 11.64/1.98  
% 11.64/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.64/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.64/1.98  git: non_committed_changes: false
% 11.64/1.98  git: last_make_outside_of_git: false
% 11.64/1.98  
% 11.64/1.98  ------ 
% 11.64/1.98  
% 11.64/1.98  ------ Input Options
% 11.64/1.98  
% 11.64/1.98  --out_options                           all
% 11.64/1.98  --tptp_safe_out                         true
% 11.64/1.98  --problem_path                          ""
% 11.64/1.98  --include_path                          ""
% 11.64/1.98  --clausifier                            res/vclausify_rel
% 11.64/1.98  --clausifier_options                    ""
% 11.64/1.98  --stdin                                 false
% 11.64/1.98  --stats_out                             all
% 11.64/1.98  
% 11.64/1.98  ------ General Options
% 11.64/1.98  
% 11.64/1.98  --fof                                   false
% 11.64/1.98  --time_out_real                         305.
% 11.64/1.98  --time_out_virtual                      -1.
% 11.64/1.98  --symbol_type_check                     false
% 11.64/1.98  --clausify_out                          false
% 11.64/1.98  --sig_cnt_out                           false
% 11.64/1.98  --trig_cnt_out                          false
% 11.64/1.98  --trig_cnt_out_tolerance                1.
% 11.64/1.98  --trig_cnt_out_sk_spl                   false
% 11.64/1.98  --abstr_cl_out                          false
% 11.64/1.98  
% 11.64/1.98  ------ Global Options
% 11.64/1.98  
% 11.64/1.98  --schedule                              default
% 11.64/1.98  --add_important_lit                     false
% 11.64/1.98  --prop_solver_per_cl                    1000
% 11.64/1.98  --min_unsat_core                        false
% 11.64/1.98  --soft_assumptions                      false
% 11.64/1.98  --soft_lemma_size                       3
% 11.64/1.98  --prop_impl_unit_size                   0
% 11.64/1.98  --prop_impl_unit                        []
% 11.64/1.98  --share_sel_clauses                     true
% 11.64/1.98  --reset_solvers                         false
% 11.64/1.98  --bc_imp_inh                            [conj_cone]
% 11.64/1.98  --conj_cone_tolerance                   3.
% 11.64/1.98  --extra_neg_conj                        none
% 11.64/1.98  --large_theory_mode                     true
% 11.64/1.98  --prolific_symb_bound                   200
% 11.64/1.98  --lt_threshold                          2000
% 11.64/1.98  --clause_weak_htbl                      true
% 11.64/1.98  --gc_record_bc_elim                     false
% 11.64/1.98  
% 11.64/1.98  ------ Preprocessing Options
% 11.64/1.98  
% 11.64/1.98  --preprocessing_flag                    true
% 11.64/1.98  --time_out_prep_mult                    0.1
% 11.64/1.98  --splitting_mode                        input
% 11.64/1.98  --splitting_grd                         true
% 11.64/1.98  --splitting_cvd                         false
% 11.64/1.98  --splitting_cvd_svl                     false
% 11.64/1.98  --splitting_nvd                         32
% 11.64/1.98  --sub_typing                            true
% 11.64/1.98  --prep_gs_sim                           true
% 11.64/1.98  --prep_unflatten                        true
% 11.64/1.98  --prep_res_sim                          true
% 11.64/1.98  --prep_upred                            true
% 11.64/1.98  --prep_sem_filter                       exhaustive
% 11.64/1.98  --prep_sem_filter_out                   false
% 11.64/1.98  --pred_elim                             true
% 11.64/1.98  --res_sim_input                         true
% 11.64/1.98  --eq_ax_congr_red                       true
% 11.64/1.98  --pure_diseq_elim                       true
% 11.64/1.98  --brand_transform                       false
% 11.64/1.98  --non_eq_to_eq                          false
% 11.64/1.98  --prep_def_merge                        true
% 11.64/1.98  --prep_def_merge_prop_impl              false
% 11.64/1.98  --prep_def_merge_mbd                    true
% 11.64/1.98  --prep_def_merge_tr_red                 false
% 11.64/1.98  --prep_def_merge_tr_cl                  false
% 11.64/1.98  --smt_preprocessing                     true
% 11.64/1.98  --smt_ac_axioms                         fast
% 11.64/1.98  --preprocessed_out                      false
% 11.64/1.98  --preprocessed_stats                    false
% 11.64/1.98  
% 11.64/1.98  ------ Abstraction refinement Options
% 11.64/1.98  
% 11.64/1.98  --abstr_ref                             []
% 11.64/1.98  --abstr_ref_prep                        false
% 11.64/1.98  --abstr_ref_until_sat                   false
% 11.64/1.98  --abstr_ref_sig_restrict                funpre
% 11.64/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.64/1.98  --abstr_ref_under                       []
% 11.64/1.98  
% 11.64/1.98  ------ SAT Options
% 11.64/1.98  
% 11.64/1.98  --sat_mode                              false
% 11.64/1.98  --sat_fm_restart_options                ""
% 11.64/1.98  --sat_gr_def                            false
% 11.64/1.98  --sat_epr_types                         true
% 11.64/1.98  --sat_non_cyclic_types                  false
% 11.64/1.98  --sat_finite_models                     false
% 11.64/1.98  --sat_fm_lemmas                         false
% 11.64/1.98  --sat_fm_prep                           false
% 11.64/1.98  --sat_fm_uc_incr                        true
% 11.64/1.98  --sat_out_model                         small
% 11.64/1.98  --sat_out_clauses                       false
% 11.64/1.98  
% 11.64/1.98  ------ QBF Options
% 11.64/1.98  
% 11.64/1.98  --qbf_mode                              false
% 11.64/1.98  --qbf_elim_univ                         false
% 11.64/1.98  --qbf_dom_inst                          none
% 11.64/1.98  --qbf_dom_pre_inst                      false
% 11.64/1.98  --qbf_sk_in                             false
% 11.64/1.98  --qbf_pred_elim                         true
% 11.64/1.98  --qbf_split                             512
% 11.64/1.98  
% 11.64/1.98  ------ BMC1 Options
% 11.64/1.98  
% 11.64/1.98  --bmc1_incremental                      false
% 11.64/1.98  --bmc1_axioms                           reachable_all
% 11.64/1.98  --bmc1_min_bound                        0
% 11.64/1.98  --bmc1_max_bound                        -1
% 11.64/1.98  --bmc1_max_bound_default                -1
% 11.64/1.98  --bmc1_symbol_reachability              true
% 11.64/1.98  --bmc1_property_lemmas                  false
% 11.64/1.98  --bmc1_k_induction                      false
% 11.64/1.98  --bmc1_non_equiv_states                 false
% 11.64/1.98  --bmc1_deadlock                         false
% 11.64/1.98  --bmc1_ucm                              false
% 11.64/1.98  --bmc1_add_unsat_core                   none
% 11.64/1.98  --bmc1_unsat_core_children              false
% 11.64/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.64/1.98  --bmc1_out_stat                         full
% 11.64/1.98  --bmc1_ground_init                      false
% 11.64/1.98  --bmc1_pre_inst_next_state              false
% 11.64/1.98  --bmc1_pre_inst_state                   false
% 11.64/1.98  --bmc1_pre_inst_reach_state             false
% 11.64/1.98  --bmc1_out_unsat_core                   false
% 11.64/1.98  --bmc1_aig_witness_out                  false
% 11.64/1.98  --bmc1_verbose                          false
% 11.64/1.98  --bmc1_dump_clauses_tptp                false
% 11.64/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.64/1.98  --bmc1_dump_file                        -
% 11.64/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.64/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.64/1.98  --bmc1_ucm_extend_mode                  1
% 11.64/1.98  --bmc1_ucm_init_mode                    2
% 11.64/1.98  --bmc1_ucm_cone_mode                    none
% 11.64/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.64/1.98  --bmc1_ucm_relax_model                  4
% 11.64/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.64/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.64/1.98  --bmc1_ucm_layered_model                none
% 11.64/1.98  --bmc1_ucm_max_lemma_size               10
% 11.64/1.98  
% 11.64/1.98  ------ AIG Options
% 11.64/1.98  
% 11.64/1.98  --aig_mode                              false
% 11.64/1.98  
% 11.64/1.98  ------ Instantiation Options
% 11.64/1.98  
% 11.64/1.98  --instantiation_flag                    true
% 11.64/1.98  --inst_sos_flag                         true
% 11.64/1.98  --inst_sos_phase                        true
% 11.64/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.64/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.64/1.98  --inst_lit_sel_side                     num_symb
% 11.64/1.98  --inst_solver_per_active                1400
% 11.64/1.98  --inst_solver_calls_frac                1.
% 11.64/1.98  --inst_passive_queue_type               priority_queues
% 11.64/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.64/1.98  --inst_passive_queues_freq              [25;2]
% 11.64/1.98  --inst_dismatching                      true
% 11.64/1.98  --inst_eager_unprocessed_to_passive     true
% 11.64/1.98  --inst_prop_sim_given                   true
% 11.64/1.98  --inst_prop_sim_new                     false
% 11.64/1.98  --inst_subs_new                         false
% 11.64/1.98  --inst_eq_res_simp                      false
% 11.64/1.98  --inst_subs_given                       false
% 11.64/1.98  --inst_orphan_elimination               true
% 11.64/1.98  --inst_learning_loop_flag               true
% 11.64/1.98  --inst_learning_start                   3000
% 11.64/1.98  --inst_learning_factor                  2
% 11.64/1.98  --inst_start_prop_sim_after_learn       3
% 11.64/1.98  --inst_sel_renew                        solver
% 11.64/1.98  --inst_lit_activity_flag                true
% 11.64/1.98  --inst_restr_to_given                   false
% 11.64/1.98  --inst_activity_threshold               500
% 11.64/1.98  --inst_out_proof                        true
% 11.64/1.98  
% 11.64/1.98  ------ Resolution Options
% 11.64/1.98  
% 11.64/1.98  --resolution_flag                       true
% 11.64/1.98  --res_lit_sel                           adaptive
% 11.64/1.98  --res_lit_sel_side                      none
% 11.64/1.98  --res_ordering                          kbo
% 11.64/1.98  --res_to_prop_solver                    active
% 11.64/1.98  --res_prop_simpl_new                    false
% 11.64/1.98  --res_prop_simpl_given                  true
% 11.64/1.98  --res_passive_queue_type                priority_queues
% 11.64/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.64/1.98  --res_passive_queues_freq               [15;5]
% 11.64/1.98  --res_forward_subs                      full
% 11.64/1.98  --res_backward_subs                     full
% 11.64/1.98  --res_forward_subs_resolution           true
% 11.64/1.98  --res_backward_subs_resolution          true
% 11.64/1.98  --res_orphan_elimination                true
% 11.64/1.98  --res_time_limit                        2.
% 11.64/1.98  --res_out_proof                         true
% 11.64/1.98  
% 11.64/1.98  ------ Superposition Options
% 11.64/1.98  
% 11.64/1.98  --superposition_flag                    true
% 11.64/1.98  --sup_passive_queue_type                priority_queues
% 11.64/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.64/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.64/1.98  --demod_completeness_check              fast
% 11.64/1.98  --demod_use_ground                      true
% 11.64/1.98  --sup_to_prop_solver                    passive
% 11.64/1.98  --sup_prop_simpl_new                    true
% 11.64/1.98  --sup_prop_simpl_given                  true
% 11.64/1.98  --sup_fun_splitting                     true
% 11.64/1.98  --sup_smt_interval                      50000
% 11.64/1.98  
% 11.64/1.98  ------ Superposition Simplification Setup
% 11.64/1.98  
% 11.64/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.64/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.64/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.64/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.64/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.64/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.64/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.64/1.98  --sup_immed_triv                        [TrivRules]
% 11.64/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.64/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.64/1.98  --sup_immed_bw_main                     []
% 11.64/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.64/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.64/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.64/1.98  --sup_input_bw                          []
% 11.64/1.98  
% 11.64/1.98  ------ Combination Options
% 11.64/1.98  
% 11.64/1.98  --comb_res_mult                         3
% 11.64/1.98  --comb_sup_mult                         2
% 11.64/1.98  --comb_inst_mult                        10
% 11.64/1.98  
% 11.64/1.98  ------ Debug Options
% 11.64/1.98  
% 11.64/1.98  --dbg_backtrace                         false
% 11.64/1.98  --dbg_dump_prop_clauses                 false
% 11.64/1.98  --dbg_dump_prop_clauses_file            -
% 11.64/1.98  --dbg_out_stat                          false
% 11.64/1.98  ------ Parsing...
% 11.64/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.64/1.98  
% 11.64/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.64/1.98  
% 11.64/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.64/1.98  
% 11.64/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.64/1.98  ------ Proving...
% 11.64/1.98  ------ Problem Properties 
% 11.64/1.98  
% 11.64/1.98  
% 11.64/1.98  clauses                                 15
% 11.64/1.98  conjectures                             3
% 11.64/1.98  EPR                                     3
% 11.64/1.98  Horn                                    15
% 11.64/1.98  unary                                   12
% 11.64/1.98  binary                                  1
% 11.64/1.98  lits                                    20
% 11.64/1.98  lits eq                                 10
% 11.64/1.98  fd_pure                                 0
% 11.64/1.98  fd_pseudo                               0
% 11.64/1.98  fd_cond                                 0
% 11.64/1.98  fd_pseudo_cond                          1
% 11.64/1.98  AC symbols                              0
% 11.64/1.98  
% 11.64/1.98  ------ Schedule dynamic 5 is on 
% 11.64/1.98  
% 11.64/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.64/1.98  
% 11.64/1.98  
% 11.64/1.98  ------ 
% 11.64/1.98  Current options:
% 11.64/1.98  ------ 
% 11.64/1.98  
% 11.64/1.98  ------ Input Options
% 11.64/1.98  
% 11.64/1.98  --out_options                           all
% 11.64/1.98  --tptp_safe_out                         true
% 11.64/1.98  --problem_path                          ""
% 11.64/1.98  --include_path                          ""
% 11.64/1.98  --clausifier                            res/vclausify_rel
% 11.64/1.98  --clausifier_options                    ""
% 11.64/1.98  --stdin                                 false
% 11.64/1.98  --stats_out                             all
% 11.64/1.98  
% 11.64/1.98  ------ General Options
% 11.64/1.98  
% 11.64/1.98  --fof                                   false
% 11.64/1.98  --time_out_real                         305.
% 11.64/1.98  --time_out_virtual                      -1.
% 11.64/1.98  --symbol_type_check                     false
% 11.64/1.98  --clausify_out                          false
% 11.64/1.98  --sig_cnt_out                           false
% 11.64/1.98  --trig_cnt_out                          false
% 11.64/1.98  --trig_cnt_out_tolerance                1.
% 11.64/1.98  --trig_cnt_out_sk_spl                   false
% 11.64/1.98  --abstr_cl_out                          false
% 11.64/1.98  
% 11.64/1.98  ------ Global Options
% 11.64/1.98  
% 11.64/1.98  --schedule                              default
% 11.64/1.98  --add_important_lit                     false
% 11.64/1.98  --prop_solver_per_cl                    1000
% 11.64/1.98  --min_unsat_core                        false
% 11.64/1.98  --soft_assumptions                      false
% 11.64/1.98  --soft_lemma_size                       3
% 11.64/1.98  --prop_impl_unit_size                   0
% 11.64/1.98  --prop_impl_unit                        []
% 11.64/1.98  --share_sel_clauses                     true
% 11.64/1.98  --reset_solvers                         false
% 11.64/1.98  --bc_imp_inh                            [conj_cone]
% 11.64/1.98  --conj_cone_tolerance                   3.
% 11.64/1.98  --extra_neg_conj                        none
% 11.64/1.98  --large_theory_mode                     true
% 11.64/1.98  --prolific_symb_bound                   200
% 11.64/1.98  --lt_threshold                          2000
% 11.64/1.98  --clause_weak_htbl                      true
% 11.64/1.98  --gc_record_bc_elim                     false
% 11.64/1.98  
% 11.64/1.98  ------ Preprocessing Options
% 11.64/1.98  
% 11.64/1.98  --preprocessing_flag                    true
% 11.64/1.98  --time_out_prep_mult                    0.1
% 11.64/1.98  --splitting_mode                        input
% 11.64/1.98  --splitting_grd                         true
% 11.64/1.98  --splitting_cvd                         false
% 11.64/1.98  --splitting_cvd_svl                     false
% 11.64/1.98  --splitting_nvd                         32
% 11.64/1.98  --sub_typing                            true
% 11.64/1.98  --prep_gs_sim                           true
% 11.64/1.98  --prep_unflatten                        true
% 11.64/1.98  --prep_res_sim                          true
% 11.64/1.98  --prep_upred                            true
% 11.64/1.98  --prep_sem_filter                       exhaustive
% 11.64/1.98  --prep_sem_filter_out                   false
% 11.64/1.98  --pred_elim                             true
% 11.64/1.98  --res_sim_input                         true
% 11.64/1.98  --eq_ax_congr_red                       true
% 11.64/1.98  --pure_diseq_elim                       true
% 11.64/1.98  --brand_transform                       false
% 11.64/1.98  --non_eq_to_eq                          false
% 11.64/1.98  --prep_def_merge                        true
% 11.64/1.98  --prep_def_merge_prop_impl              false
% 11.64/1.98  --prep_def_merge_mbd                    true
% 11.64/1.98  --prep_def_merge_tr_red                 false
% 11.64/1.98  --prep_def_merge_tr_cl                  false
% 11.64/1.98  --smt_preprocessing                     true
% 11.64/1.98  --smt_ac_axioms                         fast
% 11.64/1.98  --preprocessed_out                      false
% 11.64/1.98  --preprocessed_stats                    false
% 11.64/1.98  
% 11.64/1.98  ------ Abstraction refinement Options
% 11.64/1.98  
% 11.64/1.98  --abstr_ref                             []
% 11.64/1.98  --abstr_ref_prep                        false
% 11.64/1.98  --abstr_ref_until_sat                   false
% 11.64/1.98  --abstr_ref_sig_restrict                funpre
% 11.64/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.64/1.98  --abstr_ref_under                       []
% 11.64/1.98  
% 11.64/1.98  ------ SAT Options
% 11.64/1.98  
% 11.64/1.98  --sat_mode                              false
% 11.64/1.98  --sat_fm_restart_options                ""
% 11.64/1.98  --sat_gr_def                            false
% 11.64/1.98  --sat_epr_types                         true
% 11.64/1.98  --sat_non_cyclic_types                  false
% 11.64/1.98  --sat_finite_models                     false
% 11.64/1.98  --sat_fm_lemmas                         false
% 11.64/1.98  --sat_fm_prep                           false
% 11.64/1.98  --sat_fm_uc_incr                        true
% 11.64/1.98  --sat_out_model                         small
% 11.64/1.98  --sat_out_clauses                       false
% 11.64/1.98  
% 11.64/1.98  ------ QBF Options
% 11.64/1.98  
% 11.64/1.98  --qbf_mode                              false
% 11.64/1.98  --qbf_elim_univ                         false
% 11.64/1.98  --qbf_dom_inst                          none
% 11.64/1.98  --qbf_dom_pre_inst                      false
% 11.64/1.98  --qbf_sk_in                             false
% 11.64/1.98  --qbf_pred_elim                         true
% 11.64/1.98  --qbf_split                             512
% 11.64/1.98  
% 11.64/1.98  ------ BMC1 Options
% 11.64/1.98  
% 11.64/1.98  --bmc1_incremental                      false
% 11.64/1.98  --bmc1_axioms                           reachable_all
% 11.64/1.98  --bmc1_min_bound                        0
% 11.64/1.98  --bmc1_max_bound                        -1
% 11.64/1.98  --bmc1_max_bound_default                -1
% 11.64/1.98  --bmc1_symbol_reachability              true
% 11.64/1.98  --bmc1_property_lemmas                  false
% 11.64/1.98  --bmc1_k_induction                      false
% 11.64/1.98  --bmc1_non_equiv_states                 false
% 11.64/1.98  --bmc1_deadlock                         false
% 11.64/1.98  --bmc1_ucm                              false
% 11.64/1.98  --bmc1_add_unsat_core                   none
% 11.64/1.98  --bmc1_unsat_core_children              false
% 11.64/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.64/1.98  --bmc1_out_stat                         full
% 11.64/1.98  --bmc1_ground_init                      false
% 11.64/1.98  --bmc1_pre_inst_next_state              false
% 11.64/1.98  --bmc1_pre_inst_state                   false
% 11.64/1.98  --bmc1_pre_inst_reach_state             false
% 11.64/1.98  --bmc1_out_unsat_core                   false
% 11.64/1.98  --bmc1_aig_witness_out                  false
% 11.64/1.98  --bmc1_verbose                          false
% 11.64/1.98  --bmc1_dump_clauses_tptp                false
% 11.64/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.64/1.98  --bmc1_dump_file                        -
% 11.64/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.64/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.64/1.98  --bmc1_ucm_extend_mode                  1
% 11.64/1.98  --bmc1_ucm_init_mode                    2
% 11.64/1.98  --bmc1_ucm_cone_mode                    none
% 11.64/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.64/1.98  --bmc1_ucm_relax_model                  4
% 11.64/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.64/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.64/1.98  --bmc1_ucm_layered_model                none
% 11.64/1.98  --bmc1_ucm_max_lemma_size               10
% 11.64/1.98  
% 11.64/1.98  ------ AIG Options
% 11.64/1.98  
% 11.64/1.98  --aig_mode                              false
% 11.64/1.98  
% 11.64/1.98  ------ Instantiation Options
% 11.64/1.98  
% 11.64/1.98  --instantiation_flag                    true
% 11.64/1.98  --inst_sos_flag                         true
% 11.64/1.98  --inst_sos_phase                        true
% 11.64/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.64/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.64/1.98  --inst_lit_sel_side                     none
% 11.64/1.98  --inst_solver_per_active                1400
% 11.64/1.98  --inst_solver_calls_frac                1.
% 11.64/1.98  --inst_passive_queue_type               priority_queues
% 11.64/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.64/1.98  --inst_passive_queues_freq              [25;2]
% 11.64/1.98  --inst_dismatching                      true
% 11.64/1.98  --inst_eager_unprocessed_to_passive     true
% 11.64/1.98  --inst_prop_sim_given                   true
% 11.64/1.98  --inst_prop_sim_new                     false
% 11.64/1.98  --inst_subs_new                         false
% 11.64/1.98  --inst_eq_res_simp                      false
% 11.64/1.98  --inst_subs_given                       false
% 11.64/1.98  --inst_orphan_elimination               true
% 11.64/1.98  --inst_learning_loop_flag               true
% 11.64/1.98  --inst_learning_start                   3000
% 11.64/1.98  --inst_learning_factor                  2
% 11.64/1.98  --inst_start_prop_sim_after_learn       3
% 11.64/1.98  --inst_sel_renew                        solver
% 11.64/1.98  --inst_lit_activity_flag                true
% 11.64/1.98  --inst_restr_to_given                   false
% 11.64/1.98  --inst_activity_threshold               500
% 11.64/1.98  --inst_out_proof                        true
% 11.64/1.98  
% 11.64/1.98  ------ Resolution Options
% 11.64/1.98  
% 11.64/1.98  --resolution_flag                       false
% 11.64/1.98  --res_lit_sel                           adaptive
% 11.64/1.98  --res_lit_sel_side                      none
% 11.64/1.98  --res_ordering                          kbo
% 11.64/1.98  --res_to_prop_solver                    active
% 11.64/1.98  --res_prop_simpl_new                    false
% 11.64/1.98  --res_prop_simpl_given                  true
% 11.64/1.98  --res_passive_queue_type                priority_queues
% 11.64/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.64/1.98  --res_passive_queues_freq               [15;5]
% 11.64/1.98  --res_forward_subs                      full
% 11.64/1.98  --res_backward_subs                     full
% 11.64/1.98  --res_forward_subs_resolution           true
% 11.64/1.98  --res_backward_subs_resolution          true
% 11.64/1.98  --res_orphan_elimination                true
% 11.64/1.98  --res_time_limit                        2.
% 11.64/1.98  --res_out_proof                         true
% 11.64/1.98  
% 11.64/1.98  ------ Superposition Options
% 11.64/1.98  
% 11.64/1.98  --superposition_flag                    true
% 11.64/1.98  --sup_passive_queue_type                priority_queues
% 11.64/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.64/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.64/1.98  --demod_completeness_check              fast
% 11.64/1.98  --demod_use_ground                      true
% 11.64/1.98  --sup_to_prop_solver                    passive
% 11.64/1.98  --sup_prop_simpl_new                    true
% 11.64/1.98  --sup_prop_simpl_given                  true
% 11.64/1.98  --sup_fun_splitting                     true
% 11.64/1.98  --sup_smt_interval                      50000
% 11.64/1.98  
% 11.64/1.98  ------ Superposition Simplification Setup
% 11.64/1.98  
% 11.64/1.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.64/1.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.64/1.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.64/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.64/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.64/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.64/1.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.64/1.98  --sup_immed_triv                        [TrivRules]
% 11.64/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.64/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.64/1.98  --sup_immed_bw_main                     []
% 11.64/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.64/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.64/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.64/1.98  --sup_input_bw                          []
% 11.64/1.98  
% 11.64/1.98  ------ Combination Options
% 11.64/1.98  
% 11.64/1.98  --comb_res_mult                         3
% 11.64/1.98  --comb_sup_mult                         2
% 11.64/1.98  --comb_inst_mult                        10
% 11.64/1.98  
% 11.64/1.98  ------ Debug Options
% 11.64/1.98  
% 11.64/1.98  --dbg_backtrace                         false
% 11.64/1.98  --dbg_dump_prop_clauses                 false
% 11.64/1.98  --dbg_dump_prop_clauses_file            -
% 11.64/1.98  --dbg_out_stat                          false
% 11.64/1.98  
% 11.64/1.98  
% 11.64/1.98  
% 11.64/1.98  
% 11.64/1.98  ------ Proving...
% 11.64/1.98  
% 11.64/1.98  
% 11.64/1.98  % SZS status Theorem for theBenchmark.p
% 11.64/1.98  
% 11.64/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.64/1.98  
% 11.64/1.98  fof(f11,axiom,(
% 11.64/1.98    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 11.64/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.64/1.98  
% 11.64/1.98  fof(f17,plain,(
% 11.64/1.98    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 11.64/1.98    inference(ennf_transformation,[],[f11])).
% 11.64/1.98  
% 11.64/1.98  fof(f36,plain,(
% 11.64/1.98    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 11.64/1.98    inference(cnf_transformation,[],[f17])).
% 11.64/1.98  
% 11.64/1.98  fof(f12,conjecture,(
% 11.64/1.98    ! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 11.64/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.64/1.98  
% 11.64/1.98  fof(f13,negated_conjecture,(
% 11.64/1.98    ~! [X0,X1,X2,X3] : ((r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => k3_xboole_0(X0,X2) = k1_tarski(X3))),
% 11.64/1.98    inference(negated_conjecture,[],[f12])).
% 11.64/1.98  
% 11.64/1.98  fof(f18,plain,(
% 11.64/1.98    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & (r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)))),
% 11.64/1.98    inference(ennf_transformation,[],[f13])).
% 11.64/1.98  
% 11.64/1.98  fof(f19,plain,(
% 11.64/1.98    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1))),
% 11.64/1.98    inference(flattening,[],[f18])).
% 11.64/1.98  
% 11.64/1.98  fof(f22,plain,(
% 11.64/1.98    ? [X0,X1,X2,X3] : (k3_xboole_0(X0,X2) != k1_tarski(X3) & r2_hidden(X3,X0) & k3_xboole_0(X1,X2) = k1_tarski(X3) & r1_tarski(X0,X1)) => (k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k3_xboole_0(sK1,sK2) = k1_tarski(sK3) & r1_tarski(sK0,sK1))),
% 11.64/1.98    introduced(choice_axiom,[])).
% 11.64/1.98  
% 11.64/1.98  fof(f23,plain,(
% 11.64/1.98    k3_xboole_0(sK0,sK2) != k1_tarski(sK3) & r2_hidden(sK3,sK0) & k3_xboole_0(sK1,sK2) = k1_tarski(sK3) & r1_tarski(sK0,sK1)),
% 11.64/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f22])).
% 11.64/1.98  
% 11.64/1.98  fof(f39,plain,(
% 11.64/1.98    r2_hidden(sK3,sK0)),
% 11.64/1.98    inference(cnf_transformation,[],[f23])).
% 11.64/1.98  
% 11.64/1.98  fof(f6,axiom,(
% 11.64/1.98    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 11.64/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.64/1.98  
% 11.64/1.98  fof(f31,plain,(
% 11.64/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 11.64/1.98    inference(cnf_transformation,[],[f6])).
% 11.64/1.98  
% 11.64/1.98  fof(f1,axiom,(
% 11.64/1.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.64/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.64/1.98  
% 11.64/1.98  fof(f24,plain,(
% 11.64/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.64/1.98    inference(cnf_transformation,[],[f1])).
% 11.64/1.98  
% 11.64/1.98  fof(f8,axiom,(
% 11.64/1.98    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 11.64/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.64/1.98  
% 11.64/1.98  fof(f33,plain,(
% 11.64/1.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 11.64/1.98    inference(cnf_transformation,[],[f8])).
% 11.64/1.98  
% 11.64/1.98  fof(f38,plain,(
% 11.64/1.98    k3_xboole_0(sK1,sK2) = k1_tarski(sK3)),
% 11.64/1.98    inference(cnf_transformation,[],[f23])).
% 11.64/1.98  
% 11.64/1.98  fof(f7,axiom,(
% 11.64/1.98    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 11.64/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.64/1.98  
% 11.64/1.98  fof(f32,plain,(
% 11.64/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 11.64/1.98    inference(cnf_transformation,[],[f7])).
% 11.64/1.98  
% 11.64/1.98  fof(f9,axiom,(
% 11.64/1.98    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0))),
% 11.64/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.64/1.98  
% 11.64/1.98  fof(f34,plain,(
% 11.64/1.98    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) = k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0))) )),
% 11.64/1.98    inference(cnf_transformation,[],[f9])).
% 11.64/1.98  
% 11.64/1.98  fof(f37,plain,(
% 11.64/1.98    r1_tarski(sK0,sK1)),
% 11.64/1.98    inference(cnf_transformation,[],[f23])).
% 11.64/1.98  
% 11.64/1.98  fof(f3,axiom,(
% 11.64/1.98    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 11.64/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.64/1.98  
% 11.64/1.98  fof(f14,plain,(
% 11.64/1.98    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 11.64/1.98    inference(ennf_transformation,[],[f3])).
% 11.64/1.98  
% 11.64/1.98  fof(f28,plain,(
% 11.64/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 11.64/1.98    inference(cnf_transformation,[],[f14])).
% 11.64/1.98  
% 11.64/1.98  fof(f40,plain,(
% 11.64/1.98    k3_xboole_0(sK0,sK2) != k1_tarski(sK3)),
% 11.64/1.98    inference(cnf_transformation,[],[f23])).
% 11.64/1.98  
% 11.64/1.98  cnf(c_12,plain,
% 11.64/1.98      ( ~ r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
% 11.64/1.98      inference(cnf_transformation,[],[f36]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_14,negated_conjecture,
% 11.64/1.98      ( r2_hidden(sK3,sK0) ),
% 11.64/1.98      inference(cnf_transformation,[],[f39]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_122,plain,
% 11.64/1.98      ( k2_xboole_0(k1_tarski(X0),X1) = X1 | sK3 != X0 | sK0 != X1 ),
% 11.64/1.98      inference(resolution_lifted,[status(thm)],[c_12,c_14]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_123,plain,
% 11.64/1.98      ( k2_xboole_0(k1_tarski(sK3),sK0) = sK0 ),
% 11.64/1.98      inference(unflattening,[status(thm)],[c_122]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_7,plain,
% 11.64/1.98      ( k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
% 11.64/1.98      inference(cnf_transformation,[],[f31]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_596,plain,
% 11.64/1.98      ( k3_xboole_0(k1_tarski(sK3),sK0) = k1_tarski(sK3) ),
% 11.64/1.98      inference(superposition,[status(thm)],[c_123,c_7]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_0,plain,
% 11.64/1.98      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 11.64/1.98      inference(cnf_transformation,[],[f24]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_1232,plain,
% 11.64/1.98      ( k3_xboole_0(sK0,k1_tarski(sK3)) = k1_tarski(sK3) ),
% 11.64/1.98      inference(superposition,[status(thm)],[c_596,c_0]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_9,plain,
% 11.64/1.98      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k2_xboole_0(X1,X2)) ),
% 11.64/1.98      inference(cnf_transformation,[],[f33]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_2478,plain,
% 11.64/1.98      ( k2_xboole_0(k1_tarski(sK3),k3_xboole_0(sK0,X0)) = k3_xboole_0(sK0,k2_xboole_0(k1_tarski(sK3),X0)) ),
% 11.64/1.98      inference(superposition,[status(thm)],[c_1232,c_9]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_15,negated_conjecture,
% 11.64/1.98      ( k3_xboole_0(sK1,sK2) = k1_tarski(sK3) ),
% 11.64/1.98      inference(cnf_transformation,[],[f38]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_507,plain,
% 11.64/1.98      ( k3_xboole_0(sK2,sK1) = k1_tarski(sK3) ),
% 11.64/1.98      inference(superposition,[status(thm)],[c_15,c_0]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_768,plain,
% 11.64/1.98      ( k2_xboole_0(k1_tarski(sK3),k3_xboole_0(sK2,X0)) = k3_xboole_0(sK2,k2_xboole_0(sK1,X0)) ),
% 11.64/1.98      inference(superposition,[status(thm)],[c_507,c_9]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_1923,plain,
% 11.64/1.98      ( k2_xboole_0(k1_tarski(sK3),k3_xboole_0(X0,sK2)) = k3_xboole_0(sK2,k2_xboole_0(sK1,X0)) ),
% 11.64/1.98      inference(superposition,[status(thm)],[c_0,c_768]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_29790,plain,
% 11.64/1.98      ( k3_xboole_0(sK0,k2_xboole_0(k1_tarski(sK3),sK2)) = k3_xboole_0(sK2,k2_xboole_0(sK1,sK0)) ),
% 11.64/1.98      inference(superposition,[status(thm)],[c_2478,c_1923]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_8,plain,
% 11.64/1.98      ( k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 11.64/1.98      inference(cnf_transformation,[],[f32]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_684,plain,
% 11.64/1.98      ( k3_xboole_0(X0,X0) = X0 ),
% 11.64/1.98      inference(superposition,[status(thm)],[c_8,c_7]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_1927,plain,
% 11.64/1.98      ( k3_xboole_0(sK2,k2_xboole_0(sK1,sK2)) = k2_xboole_0(k1_tarski(sK3),sK2) ),
% 11.64/1.98      inference(superposition,[status(thm)],[c_684,c_768]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_680,plain,
% 11.64/1.98      ( k2_xboole_0(X0,X0) = X0 ),
% 11.64/1.98      inference(superposition,[status(thm)],[c_7,c_8]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_10,plain,
% 11.64/1.98      ( k2_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)),k3_xboole_0(X2,X0)) = k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) ),
% 11.64/1.98      inference(cnf_transformation,[],[f34]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_764,plain,
% 11.64/1.98      ( k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X1,X2)) = k3_xboole_0(X1,k2_xboole_0(X0,X2)) ),
% 11.64/1.98      inference(superposition,[status(thm)],[c_0,c_9]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_787,plain,
% 11.64/1.98      ( k3_xboole_0(k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X1,X2)),k2_xboole_0(X2,X0)) = k2_xboole_0(k3_xboole_0(X1,k2_xboole_0(X0,X2)),k3_xboole_0(X2,X0)) ),
% 11.64/1.98      inference(light_normalisation,[status(thm)],[c_10,c_10,c_764]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_889,plain,
% 11.64/1.98      ( k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X0,X1)),k3_xboole_0(X1,X0)) = k3_xboole_0(k3_xboole_0(X0,k2_xboole_0(X0,X1)),k2_xboole_0(X1,X0)) ),
% 11.64/1.98      inference(superposition,[status(thm)],[c_680,c_787]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_678,plain,
% 11.64/1.98      ( k2_xboole_0(X0,k3_xboole_0(X1,X0)) = X0 ),
% 11.64/1.98      inference(superposition,[status(thm)],[c_0,c_8]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_899,plain,
% 11.64/1.98      ( k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
% 11.64/1.98      inference(light_normalisation,[status(thm)],[c_889,c_7,c_678]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_1934,plain,
% 11.64/1.98      ( k2_xboole_0(k1_tarski(sK3),sK2) = sK2 ),
% 11.64/1.98      inference(demodulation,[status(thm)],[c_1927,c_899]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_16,negated_conjecture,
% 11.64/1.98      ( r1_tarski(sK0,sK1) ),
% 11.64/1.98      inference(cnf_transformation,[],[f37]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_296,plain,
% 11.64/1.98      ( r1_tarski(sK0,sK1) = iProver_top ),
% 11.64/1.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_4,plain,
% 11.64/1.98      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 11.64/1.98      inference(cnf_transformation,[],[f28]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_300,plain,
% 11.64/1.98      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 11.64/1.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_2239,plain,
% 11.64/1.98      ( k2_xboole_0(sK0,sK1) = sK1 ),
% 11.64/1.98      inference(superposition,[status(thm)],[c_296,c_300]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_2585,plain,
% 11.64/1.98      ( k3_xboole_0(sK0,sK1) = sK0 ),
% 11.64/1.98      inference(superposition,[status(thm)],[c_2239,c_7]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_3481,plain,
% 11.64/1.98      ( k2_xboole_0(sK1,sK0) = sK1 ),
% 11.64/1.98      inference(superposition,[status(thm)],[c_2585,c_678]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_29791,plain,
% 11.64/1.98      ( k3_xboole_0(sK0,sK2) = k1_tarski(sK3) ),
% 11.64/1.98      inference(light_normalisation,
% 11.64/1.98                [status(thm)],
% 11.64/1.98                [c_29790,c_507,c_1934,c_3481]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(c_13,negated_conjecture,
% 11.64/1.98      ( k3_xboole_0(sK0,sK2) != k1_tarski(sK3) ),
% 11.64/1.98      inference(cnf_transformation,[],[f40]) ).
% 11.64/1.98  
% 11.64/1.98  cnf(contradiction,plain,
% 11.64/1.98      ( $false ),
% 11.64/1.98      inference(minisat,[status(thm)],[c_29791,c_13]) ).
% 11.64/1.98  
% 11.64/1.98  
% 11.64/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.64/1.98  
% 11.64/1.98  ------                               Statistics
% 11.64/1.98  
% 11.64/1.98  ------ General
% 11.64/1.98  
% 11.64/1.98  abstr_ref_over_cycles:                  0
% 11.64/1.98  abstr_ref_under_cycles:                 0
% 11.64/1.98  gc_basic_clause_elim:                   0
% 11.64/1.98  forced_gc_time:                         0
% 11.64/1.98  parsing_time:                           0.009
% 11.64/1.98  unif_index_cands_time:                  0.
% 11.64/1.98  unif_index_add_time:                    0.
% 11.64/1.98  orderings_time:                         0.
% 11.64/1.98  out_proof_time:                         0.007
% 11.64/1.98  total_time:                             1.032
% 11.64/1.98  num_of_symbols:                         40
% 11.64/1.98  num_of_terms:                           48002
% 11.64/1.98  
% 11.64/1.98  ------ Preprocessing
% 11.64/1.98  
% 11.64/1.98  num_of_splits:                          0
% 11.64/1.98  num_of_split_atoms:                     0
% 11.64/1.98  num_of_reused_defs:                     0
% 11.64/1.98  num_eq_ax_congr_red:                    0
% 11.64/1.98  num_of_sem_filtered_clauses:            1
% 11.64/1.98  num_of_subtypes:                        0
% 11.64/1.98  monotx_restored_types:                  0
% 11.64/1.98  sat_num_of_epr_types:                   0
% 11.64/1.98  sat_num_of_non_cyclic_types:            0
% 11.64/1.98  sat_guarded_non_collapsed_types:        0
% 11.64/1.98  num_pure_diseq_elim:                    0
% 11.64/1.98  simp_replaced_by:                       0
% 11.64/1.98  res_preprocessed:                       74
% 11.64/1.98  prep_upred:                             0
% 11.64/1.98  prep_unflattend:                        2
% 11.64/1.98  smt_new_axioms:                         0
% 11.64/1.98  pred_elim_cands:                        1
% 11.64/1.98  pred_elim:                              1
% 11.64/1.98  pred_elim_cl:                           1
% 11.64/1.98  pred_elim_cycles:                       3
% 11.64/1.98  merged_defs:                            0
% 11.64/1.98  merged_defs_ncl:                        0
% 11.64/1.98  bin_hyper_res:                          0
% 11.64/1.98  prep_cycles:                            4
% 11.64/1.98  pred_elim_time:                         0.
% 11.64/1.98  splitting_time:                         0.
% 11.64/1.98  sem_filter_time:                        0.
% 11.64/1.98  monotx_time:                            0.
% 11.64/1.98  subtype_inf_time:                       0.
% 11.64/1.98  
% 11.64/1.98  ------ Problem properties
% 11.64/1.98  
% 11.64/1.98  clauses:                                15
% 11.64/1.98  conjectures:                            3
% 11.64/1.98  epr:                                    3
% 11.64/1.98  horn:                                   15
% 11.64/1.98  ground:                                 4
% 11.64/1.98  unary:                                  12
% 11.64/1.98  binary:                                 1
% 11.64/1.98  lits:                                   20
% 11.64/1.98  lits_eq:                                10
% 11.64/1.98  fd_pure:                                0
% 11.64/1.98  fd_pseudo:                              0
% 11.64/1.98  fd_cond:                                0
% 11.64/1.98  fd_pseudo_cond:                         1
% 11.64/1.98  ac_symbols:                             0
% 11.64/1.98  
% 11.64/1.98  ------ Propositional Solver
% 11.64/1.98  
% 11.64/1.98  prop_solver_calls:                      33
% 11.64/1.98  prop_fast_solver_calls:                 443
% 11.64/1.98  smt_solver_calls:                       0
% 11.64/1.98  smt_fast_solver_calls:                  0
% 11.64/1.98  prop_num_of_clauses:                    13677
% 11.64/1.98  prop_preprocess_simplified:             15076
% 11.64/1.98  prop_fo_subsumed:                       1
% 11.64/1.98  prop_solver_time:                       0.
% 11.64/1.98  smt_solver_time:                        0.
% 11.64/1.98  smt_fast_solver_time:                   0.
% 11.64/1.98  prop_fast_solver_time:                  0.
% 11.64/1.98  prop_unsat_core_time:                   0.001
% 11.64/1.98  
% 11.64/1.98  ------ QBF
% 11.64/1.98  
% 11.64/1.98  qbf_q_res:                              0
% 11.64/1.98  qbf_num_tautologies:                    0
% 11.64/1.98  qbf_prep_cycles:                        0
% 11.64/1.98  
% 11.64/1.98  ------ BMC1
% 11.64/1.98  
% 11.64/1.98  bmc1_current_bound:                     -1
% 11.64/1.98  bmc1_last_solved_bound:                 -1
% 11.64/1.98  bmc1_unsat_core_size:                   -1
% 11.64/1.98  bmc1_unsat_core_parents_size:           -1
% 11.64/1.98  bmc1_merge_next_fun:                    0
% 11.64/1.98  bmc1_unsat_core_clauses_time:           0.
% 11.64/1.98  
% 11.64/1.98  ------ Instantiation
% 11.64/1.98  
% 11.64/1.98  inst_num_of_clauses:                    2673
% 11.64/1.98  inst_num_in_passive:                    728
% 11.64/1.98  inst_num_in_active:                     873
% 11.64/1.98  inst_num_in_unprocessed:                1072
% 11.64/1.98  inst_num_of_loops:                      930
% 11.64/1.98  inst_num_of_learning_restarts:          0
% 11.64/1.98  inst_num_moves_active_passive:          53
% 11.64/1.98  inst_lit_activity:                      0
% 11.64/1.98  inst_lit_activity_moves:                0
% 11.64/1.98  inst_num_tautologies:                   0
% 11.64/1.98  inst_num_prop_implied:                  0
% 11.64/1.98  inst_num_existing_simplified:           0
% 11.64/1.98  inst_num_eq_res_simplified:             0
% 11.64/1.98  inst_num_child_elim:                    0
% 11.64/1.98  inst_num_of_dismatching_blockings:      993
% 11.64/1.98  inst_num_of_non_proper_insts:           2773
% 11.64/1.98  inst_num_of_duplicates:                 0
% 11.64/1.98  inst_inst_num_from_inst_to_res:         0
% 11.64/1.98  inst_dismatching_checking_time:         0.
% 11.64/1.98  
% 11.64/1.98  ------ Resolution
% 11.64/1.98  
% 11.64/1.98  res_num_of_clauses:                     0
% 11.64/1.98  res_num_in_passive:                     0
% 11.64/1.98  res_num_in_active:                      0
% 11.64/1.98  res_num_of_loops:                       78
% 11.64/1.98  res_forward_subset_subsumed:            722
% 11.64/1.98  res_backward_subset_subsumed:           2
% 11.64/1.98  res_forward_subsumed:                   0
% 11.64/1.98  res_backward_subsumed:                  0
% 11.64/1.98  res_forward_subsumption_resolution:     0
% 11.64/1.98  res_backward_subsumption_resolution:    0
% 11.64/1.98  res_clause_to_clause_subsumption:       37523
% 11.64/1.98  res_orphan_elimination:                 0
% 11.64/1.98  res_tautology_del:                      113
% 11.64/1.98  res_num_eq_res_simplified:              0
% 11.64/1.98  res_num_sel_changes:                    0
% 11.64/1.98  res_moves_from_active_to_pass:          0
% 11.64/1.98  
% 11.64/1.98  ------ Superposition
% 11.64/1.98  
% 11.64/1.98  sup_time_total:                         0.
% 11.64/1.98  sup_time_generating:                    0.
% 11.64/1.98  sup_time_sim_full:                      0.
% 11.64/1.98  sup_time_sim_immed:                     0.
% 11.64/1.98  
% 11.64/1.98  sup_num_of_clauses:                     2444
% 11.64/1.98  sup_num_in_active:                      146
% 11.64/1.98  sup_num_in_passive:                     2298
% 11.64/1.98  sup_num_of_loops:                       185
% 11.64/1.98  sup_fw_superposition:                   4181
% 11.64/1.98  sup_bw_superposition:                   2882
% 11.64/1.98  sup_immediate_simplified:               3546
% 11.64/1.98  sup_given_eliminated:                   3
% 11.64/1.98  comparisons_done:                       0
% 11.64/1.98  comparisons_avoided:                    0
% 11.64/1.98  
% 11.64/1.98  ------ Simplifications
% 11.64/1.98  
% 11.64/1.98  
% 11.64/1.98  sim_fw_subset_subsumed:                 0
% 11.64/1.98  sim_bw_subset_subsumed:                 1
% 11.64/1.98  sim_fw_subsumed:                        456
% 11.64/1.98  sim_bw_subsumed:                        91
% 11.64/1.98  sim_fw_subsumption_res:                 0
% 11.64/1.98  sim_bw_subsumption_res:                 0
% 11.64/1.98  sim_tautology_del:                      49
% 11.64/1.98  sim_eq_tautology_del:                   757
% 11.64/1.98  sim_eq_res_simp:                        0
% 11.64/1.98  sim_fw_demodulated:                     2040
% 11.64/1.98  sim_bw_demodulated:                     78
% 11.64/1.98  sim_light_normalised:                   1623
% 11.64/1.98  sim_joinable_taut:                      0
% 11.64/1.98  sim_joinable_simp:                      0
% 11.64/1.98  sim_ac_normalised:                      0
% 11.64/1.98  sim_smt_subsumption:                    0
% 11.64/1.98  
%------------------------------------------------------------------------------
