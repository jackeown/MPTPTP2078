%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:57:24 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 223 expanded)
%              Number of clauses        :   34 (  85 expanded)
%              Number of leaves         :    9 (  50 expanded)
%              Depth                    :   15
%              Number of atoms          :  127 ( 507 expanded)
%              Number of equality atoms :   57 ( 158 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
       => ( r2_hidden(k2_mcart_1(X0),X2)
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f59,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
          | ~ r2_hidden(k1_mcart_1(X0),X1) )
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ( ~ r2_hidden(k2_mcart_1(sK9),sK11)
        | ~ r2_hidden(k1_mcart_1(sK9),sK10) )
      & r2_hidden(sK9,k2_zfmisc_1(sK10,sK11)) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,
    ( ( ~ r2_hidden(k2_mcart_1(sK9),sK11)
      | ~ r2_hidden(k1_mcart_1(sK9),sK10) )
    & r2_hidden(sK9,k2_zfmisc_1(sK10,sK11)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f31,f59])).

fof(f99,plain,(
    r2_hidden(sK9,k2_zfmisc_1(sK10,sK11)) ),
    inference(cnf_transformation,[],[f60])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
     => k4_tarski(sK4(X0),sK5(X0)) = X0 ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k4_tarski(sK4(X0),sK5(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f49])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(sK4(X0),sK5(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f97,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f15])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X1] :
      ( ? [X2,X3] : k4_tarski(X2,X3) = X1
     => k4_tarski(sK7(X1),sK8(X1)) = X1 ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_tarski(sK7(X1),sK8(X1)) = X1
          | ~ r2_hidden(X1,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f29,f57])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k4_tarski(sK7(X1),sK8(X1)) = X1
      | ~ r2_hidden(X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f16,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f95,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f100,plain,
    ( ~ r2_hidden(k2_mcart_1(sK9),sK11)
    | ~ r2_hidden(k1_mcart_1(sK9),sK10) ),
    inference(cnf_transformation,[],[f60])).

fof(f98,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f51])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_39,negated_conjecture,
    ( r2_hidden(sK9,k2_zfmisc_1(sK10,sK11)) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1474,plain,
    ( r2_hidden(sK9,k2_zfmisc_1(sK10,sK11)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK4(X0),sK5(X0)) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1488,plain,
    ( k4_tarski(sK4(X0),sK5(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7256,plain,
    ( k4_tarski(sK4(sK9),sK5(sK9)) = sK9 ),
    inference(superposition,[status(thm)],[c_1474,c_1488])).

cnf(c_37,plain,
    ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_7269,plain,
    ( k1_mcart_1(sK9) = sK4(sK9) ),
    inference(superposition,[status(thm)],[c_7256,c_37])).

cnf(c_33,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(sK7(X0),sK8(X0)) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_34,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_462,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_zfmisc_1(X2,X3) != X1
    | k4_tarski(sK7(X0),sK8(X0)) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_34])).

cnf(c_463,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(sK7(X0),sK8(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_462])).

cnf(c_1473,plain,
    ( k4_tarski(sK7(X0),sK8(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_3498,plain,
    ( k4_tarski(sK7(sK9),sK8(sK9)) = sK9 ),
    inference(superposition,[status(thm)],[c_1474,c_1473])).

cnf(c_3704,plain,
    ( k1_mcart_1(sK9) = sK7(sK9) ),
    inference(superposition,[status(thm)],[c_3498,c_37])).

cnf(c_7580,plain,
    ( sK7(sK9) = sK4(sK9) ),
    inference(demodulation,[status(thm)],[c_7269,c_3704])).

cnf(c_38,negated_conjecture,
    ( ~ r2_hidden(k1_mcart_1(sK9),sK10)
    | ~ r2_hidden(k2_mcart_1(sK9),sK11) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1475,plain,
    ( r2_hidden(k1_mcart_1(sK9),sK10) != iProver_top
    | r2_hidden(k2_mcart_1(sK9),sK11) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3978,plain,
    ( r2_hidden(k2_mcart_1(sK9),sK11) != iProver_top
    | r2_hidden(sK7(sK9),sK10) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3704,c_1475])).

cnf(c_36,plain,
    ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_3705,plain,
    ( k2_mcart_1(sK9) = sK8(sK9) ),
    inference(superposition,[status(thm)],[c_3498,c_36])).

cnf(c_3979,plain,
    ( r2_hidden(sK8(sK9),sK11) != iProver_top
    | r2_hidden(sK7(sK9),sK10) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3978,c_3705])).

cnf(c_14849,plain,
    ( r2_hidden(sK8(sK9),sK11) != iProver_top
    | r2_hidden(sK4(sK9),sK10) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7580,c_3979])).

cnf(c_7270,plain,
    ( k2_mcart_1(sK9) = sK5(sK9) ),
    inference(superposition,[status(thm)],[c_7256,c_36])).

cnf(c_7581,plain,
    ( sK8(sK9) = sK5(sK9) ),
    inference(demodulation,[status(thm)],[c_7270,c_3705])).

cnf(c_14852,plain,
    ( r2_hidden(sK5(sK9),sK11) != iProver_top
    | r2_hidden(sK4(sK9),sK10) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14849,c_7581])).

cnf(c_24,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1482,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7268,plain,
    ( r2_hidden(sK4(sK9),X0) = iProver_top
    | r2_hidden(sK9,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7256,c_1482])).

cnf(c_13168,plain,
    ( r2_hidden(sK4(sK9),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_1474,c_7268])).

cnf(c_23,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1483,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_7267,plain,
    ( r2_hidden(sK5(sK9),X0) = iProver_top
    | r2_hidden(sK9,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7256,c_1483])).

cnf(c_7659,plain,
    ( r2_hidden(sK5(sK9),sK11) = iProver_top ),
    inference(superposition,[status(thm)],[c_1474,c_7267])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_14852,c_13168,c_7659])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:29:00 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.65/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.65/0.99  
% 3.65/0.99  ------  iProver source info
% 3.65/0.99  
% 3.65/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.65/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.65/0.99  git: non_committed_changes: false
% 3.65/0.99  git: last_make_outside_of_git: false
% 3.65/0.99  
% 3.65/0.99  ------ 
% 3.65/0.99  
% 3.65/0.99  ------ Input Options
% 3.65/0.99  
% 3.65/0.99  --out_options                           all
% 3.65/0.99  --tptp_safe_out                         true
% 3.65/0.99  --problem_path                          ""
% 3.65/0.99  --include_path                          ""
% 3.65/0.99  --clausifier                            res/vclausify_rel
% 3.65/0.99  --clausifier_options                    ""
% 3.65/0.99  --stdin                                 false
% 3.65/0.99  --stats_out                             all
% 3.65/0.99  
% 3.65/0.99  ------ General Options
% 3.65/0.99  
% 3.65/0.99  --fof                                   false
% 3.65/0.99  --time_out_real                         305.
% 3.65/0.99  --time_out_virtual                      -1.
% 3.65/0.99  --symbol_type_check                     false
% 3.65/0.99  --clausify_out                          false
% 3.65/0.99  --sig_cnt_out                           false
% 3.65/0.99  --trig_cnt_out                          false
% 3.65/0.99  --trig_cnt_out_tolerance                1.
% 3.65/0.99  --trig_cnt_out_sk_spl                   false
% 3.65/0.99  --abstr_cl_out                          false
% 3.65/0.99  
% 3.65/0.99  ------ Global Options
% 3.65/0.99  
% 3.65/0.99  --schedule                              default
% 3.65/0.99  --add_important_lit                     false
% 3.65/0.99  --prop_solver_per_cl                    1000
% 3.65/0.99  --min_unsat_core                        false
% 3.65/0.99  --soft_assumptions                      false
% 3.65/0.99  --soft_lemma_size                       3
% 3.65/0.99  --prop_impl_unit_size                   0
% 3.65/0.99  --prop_impl_unit                        []
% 3.65/0.99  --share_sel_clauses                     true
% 3.65/0.99  --reset_solvers                         false
% 3.65/0.99  --bc_imp_inh                            [conj_cone]
% 3.65/0.99  --conj_cone_tolerance                   3.
% 3.65/0.99  --extra_neg_conj                        none
% 3.65/0.99  --large_theory_mode                     true
% 3.65/0.99  --prolific_symb_bound                   200
% 3.65/0.99  --lt_threshold                          2000
% 3.65/0.99  --clause_weak_htbl                      true
% 3.65/0.99  --gc_record_bc_elim                     false
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing Options
% 3.65/0.99  
% 3.65/0.99  --preprocessing_flag                    true
% 3.65/0.99  --time_out_prep_mult                    0.1
% 3.65/0.99  --splitting_mode                        input
% 3.65/0.99  --splitting_grd                         true
% 3.65/0.99  --splitting_cvd                         false
% 3.65/0.99  --splitting_cvd_svl                     false
% 3.65/0.99  --splitting_nvd                         32
% 3.65/0.99  --sub_typing                            true
% 3.65/0.99  --prep_gs_sim                           true
% 3.65/0.99  --prep_unflatten                        true
% 3.65/0.99  --prep_res_sim                          true
% 3.65/0.99  --prep_upred                            true
% 3.65/0.99  --prep_sem_filter                       exhaustive
% 3.65/0.99  --prep_sem_filter_out                   false
% 3.65/0.99  --pred_elim                             true
% 3.65/0.99  --res_sim_input                         true
% 3.65/0.99  --eq_ax_congr_red                       true
% 3.65/0.99  --pure_diseq_elim                       true
% 3.65/0.99  --brand_transform                       false
% 3.65/0.99  --non_eq_to_eq                          false
% 3.65/0.99  --prep_def_merge                        true
% 3.65/0.99  --prep_def_merge_prop_impl              false
% 3.65/0.99  --prep_def_merge_mbd                    true
% 3.65/0.99  --prep_def_merge_tr_red                 false
% 3.65/0.99  --prep_def_merge_tr_cl                  false
% 3.65/0.99  --smt_preprocessing                     true
% 3.65/0.99  --smt_ac_axioms                         fast
% 3.65/0.99  --preprocessed_out                      false
% 3.65/0.99  --preprocessed_stats                    false
% 3.65/0.99  
% 3.65/0.99  ------ Abstraction refinement Options
% 3.65/0.99  
% 3.65/0.99  --abstr_ref                             []
% 3.65/0.99  --abstr_ref_prep                        false
% 3.65/0.99  --abstr_ref_until_sat                   false
% 3.65/0.99  --abstr_ref_sig_restrict                funpre
% 3.65/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/0.99  --abstr_ref_under                       []
% 3.65/0.99  
% 3.65/0.99  ------ SAT Options
% 3.65/0.99  
% 3.65/0.99  --sat_mode                              false
% 3.65/0.99  --sat_fm_restart_options                ""
% 3.65/0.99  --sat_gr_def                            false
% 3.65/0.99  --sat_epr_types                         true
% 3.65/0.99  --sat_non_cyclic_types                  false
% 3.65/0.99  --sat_finite_models                     false
% 3.65/0.99  --sat_fm_lemmas                         false
% 3.65/0.99  --sat_fm_prep                           false
% 3.65/0.99  --sat_fm_uc_incr                        true
% 3.65/0.99  --sat_out_model                         small
% 3.65/0.99  --sat_out_clauses                       false
% 3.65/0.99  
% 3.65/0.99  ------ QBF Options
% 3.65/0.99  
% 3.65/0.99  --qbf_mode                              false
% 3.65/0.99  --qbf_elim_univ                         false
% 3.65/0.99  --qbf_dom_inst                          none
% 3.65/0.99  --qbf_dom_pre_inst                      false
% 3.65/0.99  --qbf_sk_in                             false
% 3.65/0.99  --qbf_pred_elim                         true
% 3.65/0.99  --qbf_split                             512
% 3.65/0.99  
% 3.65/0.99  ------ BMC1 Options
% 3.65/0.99  
% 3.65/0.99  --bmc1_incremental                      false
% 3.65/0.99  --bmc1_axioms                           reachable_all
% 3.65/0.99  --bmc1_min_bound                        0
% 3.65/0.99  --bmc1_max_bound                        -1
% 3.65/0.99  --bmc1_max_bound_default                -1
% 3.65/0.99  --bmc1_symbol_reachability              true
% 3.65/0.99  --bmc1_property_lemmas                  false
% 3.65/0.99  --bmc1_k_induction                      false
% 3.65/0.99  --bmc1_non_equiv_states                 false
% 3.65/0.99  --bmc1_deadlock                         false
% 3.65/0.99  --bmc1_ucm                              false
% 3.65/0.99  --bmc1_add_unsat_core                   none
% 3.65/0.99  --bmc1_unsat_core_children              false
% 3.65/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/0.99  --bmc1_out_stat                         full
% 3.65/0.99  --bmc1_ground_init                      false
% 3.65/0.99  --bmc1_pre_inst_next_state              false
% 3.65/0.99  --bmc1_pre_inst_state                   false
% 3.65/0.99  --bmc1_pre_inst_reach_state             false
% 3.65/0.99  --bmc1_out_unsat_core                   false
% 3.65/0.99  --bmc1_aig_witness_out                  false
% 3.65/0.99  --bmc1_verbose                          false
% 3.65/0.99  --bmc1_dump_clauses_tptp                false
% 3.65/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.65/0.99  --bmc1_dump_file                        -
% 3.65/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.65/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.65/0.99  --bmc1_ucm_extend_mode                  1
% 3.65/0.99  --bmc1_ucm_init_mode                    2
% 3.65/0.99  --bmc1_ucm_cone_mode                    none
% 3.65/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.65/0.99  --bmc1_ucm_relax_model                  4
% 3.65/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.65/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/0.99  --bmc1_ucm_layered_model                none
% 3.65/0.99  --bmc1_ucm_max_lemma_size               10
% 3.65/0.99  
% 3.65/0.99  ------ AIG Options
% 3.65/0.99  
% 3.65/0.99  --aig_mode                              false
% 3.65/0.99  
% 3.65/0.99  ------ Instantiation Options
% 3.65/0.99  
% 3.65/0.99  --instantiation_flag                    true
% 3.65/0.99  --inst_sos_flag                         true
% 3.65/0.99  --inst_sos_phase                        true
% 3.65/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/0.99  --inst_lit_sel_side                     num_symb
% 3.65/0.99  --inst_solver_per_active                1400
% 3.65/0.99  --inst_solver_calls_frac                1.
% 3.65/0.99  --inst_passive_queue_type               priority_queues
% 3.65/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/0.99  --inst_passive_queues_freq              [25;2]
% 3.65/0.99  --inst_dismatching                      true
% 3.65/0.99  --inst_eager_unprocessed_to_passive     true
% 3.65/0.99  --inst_prop_sim_given                   true
% 3.65/0.99  --inst_prop_sim_new                     false
% 3.65/0.99  --inst_subs_new                         false
% 3.65/0.99  --inst_eq_res_simp                      false
% 3.65/0.99  --inst_subs_given                       false
% 3.65/0.99  --inst_orphan_elimination               true
% 3.65/0.99  --inst_learning_loop_flag               true
% 3.65/0.99  --inst_learning_start                   3000
% 3.65/0.99  --inst_learning_factor                  2
% 3.65/0.99  --inst_start_prop_sim_after_learn       3
% 3.65/0.99  --inst_sel_renew                        solver
% 3.65/0.99  --inst_lit_activity_flag                true
% 3.65/0.99  --inst_restr_to_given                   false
% 3.65/0.99  --inst_activity_threshold               500
% 3.65/0.99  --inst_out_proof                        true
% 3.65/0.99  
% 3.65/0.99  ------ Resolution Options
% 3.65/0.99  
% 3.65/0.99  --resolution_flag                       true
% 3.65/0.99  --res_lit_sel                           adaptive
% 3.65/0.99  --res_lit_sel_side                      none
% 3.65/0.99  --res_ordering                          kbo
% 3.65/0.99  --res_to_prop_solver                    active
% 3.65/0.99  --res_prop_simpl_new                    false
% 3.65/0.99  --res_prop_simpl_given                  true
% 3.65/0.99  --res_passive_queue_type                priority_queues
% 3.65/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/0.99  --res_passive_queues_freq               [15;5]
% 3.65/0.99  --res_forward_subs                      full
% 3.65/0.99  --res_backward_subs                     full
% 3.65/0.99  --res_forward_subs_resolution           true
% 3.65/0.99  --res_backward_subs_resolution          true
% 3.65/0.99  --res_orphan_elimination                true
% 3.65/0.99  --res_time_limit                        2.
% 3.65/0.99  --res_out_proof                         true
% 3.65/0.99  
% 3.65/0.99  ------ Superposition Options
% 3.65/0.99  
% 3.65/0.99  --superposition_flag                    true
% 3.65/0.99  --sup_passive_queue_type                priority_queues
% 3.65/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.65/0.99  --demod_completeness_check              fast
% 3.65/0.99  --demod_use_ground                      true
% 3.65/0.99  --sup_to_prop_solver                    passive
% 3.65/0.99  --sup_prop_simpl_new                    true
% 3.65/0.99  --sup_prop_simpl_given                  true
% 3.65/0.99  --sup_fun_splitting                     true
% 3.65/0.99  --sup_smt_interval                      50000
% 3.65/0.99  
% 3.65/0.99  ------ Superposition Simplification Setup
% 3.65/0.99  
% 3.65/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.65/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.65/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.65/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.65/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.65/0.99  --sup_immed_triv                        [TrivRules]
% 3.65/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.99  --sup_immed_bw_main                     []
% 3.65/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.65/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.99  --sup_input_bw                          []
% 3.65/0.99  
% 3.65/0.99  ------ Combination Options
% 3.65/0.99  
% 3.65/0.99  --comb_res_mult                         3
% 3.65/0.99  --comb_sup_mult                         2
% 3.65/0.99  --comb_inst_mult                        10
% 3.65/0.99  
% 3.65/0.99  ------ Debug Options
% 3.65/0.99  
% 3.65/0.99  --dbg_backtrace                         false
% 3.65/0.99  --dbg_dump_prop_clauses                 false
% 3.65/0.99  --dbg_dump_prop_clauses_file            -
% 3.65/0.99  --dbg_out_stat                          false
% 3.65/0.99  ------ Parsing...
% 3.65/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.65/0.99  ------ Proving...
% 3.65/0.99  ------ Problem Properties 
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  clauses                                 39
% 3.65/0.99  conjectures                             2
% 3.65/0.99  EPR                                     3
% 3.65/0.99  Horn                                    33
% 3.65/0.99  unary                                   8
% 3.65/0.99  binary                                  18
% 3.65/0.99  lits                                    84
% 3.65/0.99  lits eq                                 21
% 3.65/0.99  fd_pure                                 0
% 3.65/0.99  fd_pseudo                               0
% 3.65/0.99  fd_cond                                 1
% 3.65/0.99  fd_pseudo_cond                          7
% 3.65/0.99  AC symbols                              0
% 3.65/0.99  
% 3.65/0.99  ------ Schedule dynamic 5 is on 
% 3.65/0.99  
% 3.65/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  ------ 
% 3.65/0.99  Current options:
% 3.65/0.99  ------ 
% 3.65/0.99  
% 3.65/0.99  ------ Input Options
% 3.65/0.99  
% 3.65/0.99  --out_options                           all
% 3.65/0.99  --tptp_safe_out                         true
% 3.65/0.99  --problem_path                          ""
% 3.65/0.99  --include_path                          ""
% 3.65/0.99  --clausifier                            res/vclausify_rel
% 3.65/0.99  --clausifier_options                    ""
% 3.65/0.99  --stdin                                 false
% 3.65/0.99  --stats_out                             all
% 3.65/0.99  
% 3.65/0.99  ------ General Options
% 3.65/0.99  
% 3.65/0.99  --fof                                   false
% 3.65/0.99  --time_out_real                         305.
% 3.65/0.99  --time_out_virtual                      -1.
% 3.65/0.99  --symbol_type_check                     false
% 3.65/0.99  --clausify_out                          false
% 3.65/0.99  --sig_cnt_out                           false
% 3.65/0.99  --trig_cnt_out                          false
% 3.65/0.99  --trig_cnt_out_tolerance                1.
% 3.65/0.99  --trig_cnt_out_sk_spl                   false
% 3.65/0.99  --abstr_cl_out                          false
% 3.65/0.99  
% 3.65/0.99  ------ Global Options
% 3.65/0.99  
% 3.65/0.99  --schedule                              default
% 3.65/0.99  --add_important_lit                     false
% 3.65/0.99  --prop_solver_per_cl                    1000
% 3.65/0.99  --min_unsat_core                        false
% 3.65/0.99  --soft_assumptions                      false
% 3.65/0.99  --soft_lemma_size                       3
% 3.65/0.99  --prop_impl_unit_size                   0
% 3.65/0.99  --prop_impl_unit                        []
% 3.65/0.99  --share_sel_clauses                     true
% 3.65/0.99  --reset_solvers                         false
% 3.65/0.99  --bc_imp_inh                            [conj_cone]
% 3.65/0.99  --conj_cone_tolerance                   3.
% 3.65/0.99  --extra_neg_conj                        none
% 3.65/0.99  --large_theory_mode                     true
% 3.65/0.99  --prolific_symb_bound                   200
% 3.65/0.99  --lt_threshold                          2000
% 3.65/0.99  --clause_weak_htbl                      true
% 3.65/0.99  --gc_record_bc_elim                     false
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing Options
% 3.65/0.99  
% 3.65/0.99  --preprocessing_flag                    true
% 3.65/0.99  --time_out_prep_mult                    0.1
% 3.65/0.99  --splitting_mode                        input
% 3.65/0.99  --splitting_grd                         true
% 3.65/0.99  --splitting_cvd                         false
% 3.65/0.99  --splitting_cvd_svl                     false
% 3.65/0.99  --splitting_nvd                         32
% 3.65/0.99  --sub_typing                            true
% 3.65/0.99  --prep_gs_sim                           true
% 3.65/0.99  --prep_unflatten                        true
% 3.65/0.99  --prep_res_sim                          true
% 3.65/0.99  --prep_upred                            true
% 3.65/0.99  --prep_sem_filter                       exhaustive
% 3.65/0.99  --prep_sem_filter_out                   false
% 3.65/0.99  --pred_elim                             true
% 3.65/0.99  --res_sim_input                         true
% 3.65/0.99  --eq_ax_congr_red                       true
% 3.65/0.99  --pure_diseq_elim                       true
% 3.65/0.99  --brand_transform                       false
% 3.65/0.99  --non_eq_to_eq                          false
% 3.65/0.99  --prep_def_merge                        true
% 3.65/0.99  --prep_def_merge_prop_impl              false
% 3.65/0.99  --prep_def_merge_mbd                    true
% 3.65/0.99  --prep_def_merge_tr_red                 false
% 3.65/0.99  --prep_def_merge_tr_cl                  false
% 3.65/0.99  --smt_preprocessing                     true
% 3.65/0.99  --smt_ac_axioms                         fast
% 3.65/0.99  --preprocessed_out                      false
% 3.65/0.99  --preprocessed_stats                    false
% 3.65/0.99  
% 3.65/0.99  ------ Abstraction refinement Options
% 3.65/0.99  
% 3.65/0.99  --abstr_ref                             []
% 3.65/0.99  --abstr_ref_prep                        false
% 3.65/0.99  --abstr_ref_until_sat                   false
% 3.65/0.99  --abstr_ref_sig_restrict                funpre
% 3.65/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.65/0.99  --abstr_ref_under                       []
% 3.65/0.99  
% 3.65/0.99  ------ SAT Options
% 3.65/0.99  
% 3.65/0.99  --sat_mode                              false
% 3.65/0.99  --sat_fm_restart_options                ""
% 3.65/0.99  --sat_gr_def                            false
% 3.65/0.99  --sat_epr_types                         true
% 3.65/0.99  --sat_non_cyclic_types                  false
% 3.65/0.99  --sat_finite_models                     false
% 3.65/0.99  --sat_fm_lemmas                         false
% 3.65/0.99  --sat_fm_prep                           false
% 3.65/0.99  --sat_fm_uc_incr                        true
% 3.65/0.99  --sat_out_model                         small
% 3.65/0.99  --sat_out_clauses                       false
% 3.65/0.99  
% 3.65/0.99  ------ QBF Options
% 3.65/0.99  
% 3.65/0.99  --qbf_mode                              false
% 3.65/0.99  --qbf_elim_univ                         false
% 3.65/0.99  --qbf_dom_inst                          none
% 3.65/0.99  --qbf_dom_pre_inst                      false
% 3.65/0.99  --qbf_sk_in                             false
% 3.65/0.99  --qbf_pred_elim                         true
% 3.65/0.99  --qbf_split                             512
% 3.65/0.99  
% 3.65/0.99  ------ BMC1 Options
% 3.65/0.99  
% 3.65/0.99  --bmc1_incremental                      false
% 3.65/0.99  --bmc1_axioms                           reachable_all
% 3.65/0.99  --bmc1_min_bound                        0
% 3.65/0.99  --bmc1_max_bound                        -1
% 3.65/0.99  --bmc1_max_bound_default                -1
% 3.65/0.99  --bmc1_symbol_reachability              true
% 3.65/0.99  --bmc1_property_lemmas                  false
% 3.65/0.99  --bmc1_k_induction                      false
% 3.65/0.99  --bmc1_non_equiv_states                 false
% 3.65/0.99  --bmc1_deadlock                         false
% 3.65/0.99  --bmc1_ucm                              false
% 3.65/0.99  --bmc1_add_unsat_core                   none
% 3.65/0.99  --bmc1_unsat_core_children              false
% 3.65/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.65/0.99  --bmc1_out_stat                         full
% 3.65/0.99  --bmc1_ground_init                      false
% 3.65/0.99  --bmc1_pre_inst_next_state              false
% 3.65/0.99  --bmc1_pre_inst_state                   false
% 3.65/0.99  --bmc1_pre_inst_reach_state             false
% 3.65/0.99  --bmc1_out_unsat_core                   false
% 3.65/0.99  --bmc1_aig_witness_out                  false
% 3.65/0.99  --bmc1_verbose                          false
% 3.65/0.99  --bmc1_dump_clauses_tptp                false
% 3.65/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.65/0.99  --bmc1_dump_file                        -
% 3.65/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.65/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.65/0.99  --bmc1_ucm_extend_mode                  1
% 3.65/0.99  --bmc1_ucm_init_mode                    2
% 3.65/0.99  --bmc1_ucm_cone_mode                    none
% 3.65/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.65/0.99  --bmc1_ucm_relax_model                  4
% 3.65/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.65/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.65/0.99  --bmc1_ucm_layered_model                none
% 3.65/0.99  --bmc1_ucm_max_lemma_size               10
% 3.65/0.99  
% 3.65/0.99  ------ AIG Options
% 3.65/0.99  
% 3.65/0.99  --aig_mode                              false
% 3.65/0.99  
% 3.65/0.99  ------ Instantiation Options
% 3.65/0.99  
% 3.65/0.99  --instantiation_flag                    true
% 3.65/0.99  --inst_sos_flag                         true
% 3.65/0.99  --inst_sos_phase                        true
% 3.65/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.65/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.65/0.99  --inst_lit_sel_side                     none
% 3.65/0.99  --inst_solver_per_active                1400
% 3.65/0.99  --inst_solver_calls_frac                1.
% 3.65/0.99  --inst_passive_queue_type               priority_queues
% 3.65/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.65/0.99  --inst_passive_queues_freq              [25;2]
% 3.65/0.99  --inst_dismatching                      true
% 3.65/0.99  --inst_eager_unprocessed_to_passive     true
% 3.65/0.99  --inst_prop_sim_given                   true
% 3.65/0.99  --inst_prop_sim_new                     false
% 3.65/0.99  --inst_subs_new                         false
% 3.65/0.99  --inst_eq_res_simp                      false
% 3.65/0.99  --inst_subs_given                       false
% 3.65/0.99  --inst_orphan_elimination               true
% 3.65/0.99  --inst_learning_loop_flag               true
% 3.65/0.99  --inst_learning_start                   3000
% 3.65/0.99  --inst_learning_factor                  2
% 3.65/0.99  --inst_start_prop_sim_after_learn       3
% 3.65/0.99  --inst_sel_renew                        solver
% 3.65/0.99  --inst_lit_activity_flag                true
% 3.65/0.99  --inst_restr_to_given                   false
% 3.65/0.99  --inst_activity_threshold               500
% 3.65/0.99  --inst_out_proof                        true
% 3.65/0.99  
% 3.65/0.99  ------ Resolution Options
% 3.65/0.99  
% 3.65/0.99  --resolution_flag                       false
% 3.65/0.99  --res_lit_sel                           adaptive
% 3.65/0.99  --res_lit_sel_side                      none
% 3.65/0.99  --res_ordering                          kbo
% 3.65/0.99  --res_to_prop_solver                    active
% 3.65/0.99  --res_prop_simpl_new                    false
% 3.65/0.99  --res_prop_simpl_given                  true
% 3.65/0.99  --res_passive_queue_type                priority_queues
% 3.65/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.65/0.99  --res_passive_queues_freq               [15;5]
% 3.65/0.99  --res_forward_subs                      full
% 3.65/0.99  --res_backward_subs                     full
% 3.65/0.99  --res_forward_subs_resolution           true
% 3.65/0.99  --res_backward_subs_resolution          true
% 3.65/0.99  --res_orphan_elimination                true
% 3.65/0.99  --res_time_limit                        2.
% 3.65/0.99  --res_out_proof                         true
% 3.65/0.99  
% 3.65/0.99  ------ Superposition Options
% 3.65/0.99  
% 3.65/0.99  --superposition_flag                    true
% 3.65/0.99  --sup_passive_queue_type                priority_queues
% 3.65/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.65/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.65/0.99  --demod_completeness_check              fast
% 3.65/0.99  --demod_use_ground                      true
% 3.65/0.99  --sup_to_prop_solver                    passive
% 3.65/0.99  --sup_prop_simpl_new                    true
% 3.65/0.99  --sup_prop_simpl_given                  true
% 3.65/0.99  --sup_fun_splitting                     true
% 3.65/0.99  --sup_smt_interval                      50000
% 3.65/0.99  
% 3.65/0.99  ------ Superposition Simplification Setup
% 3.65/0.99  
% 3.65/0.99  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.65/0.99  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.65/0.99  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.65/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.65/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.65/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.65/0.99  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.65/0.99  --sup_immed_triv                        [TrivRules]
% 3.65/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.99  --sup_immed_bw_main                     []
% 3.65/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.65/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.65/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.65/0.99  --sup_input_bw                          []
% 3.65/0.99  
% 3.65/0.99  ------ Combination Options
% 3.65/0.99  
% 3.65/0.99  --comb_res_mult                         3
% 3.65/0.99  --comb_sup_mult                         2
% 3.65/0.99  --comb_inst_mult                        10
% 3.65/0.99  
% 3.65/0.99  ------ Debug Options
% 3.65/0.99  
% 3.65/0.99  --dbg_backtrace                         false
% 3.65/0.99  --dbg_dump_prop_clauses                 false
% 3.65/0.99  --dbg_dump_prop_clauses_file            -
% 3.65/0.99  --dbg_out_stat                          false
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  ------ Proving...
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  % SZS status Theorem for theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  fof(f19,conjecture,(
% 3.65/0.99    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f20,negated_conjecture,(
% 3.65/0.99    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 3.65/0.99    inference(negated_conjecture,[],[f19])).
% 3.65/0.99  
% 3.65/0.99  fof(f31,plain,(
% 3.65/0.99    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.65/0.99    inference(ennf_transformation,[],[f20])).
% 3.65/0.99  
% 3.65/0.99  fof(f59,plain,(
% 3.65/0.99    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => ((~r2_hidden(k2_mcart_1(sK9),sK11) | ~r2_hidden(k1_mcart_1(sK9),sK10)) & r2_hidden(sK9,k2_zfmisc_1(sK10,sK11)))),
% 3.65/0.99    introduced(choice_axiom,[])).
% 3.65/0.99  
% 3.65/0.99  fof(f60,plain,(
% 3.65/0.99    (~r2_hidden(k2_mcart_1(sK9),sK11) | ~r2_hidden(k1_mcart_1(sK9),sK10)) & r2_hidden(sK9,k2_zfmisc_1(sK10,sK11))),
% 3.65/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f31,f59])).
% 3.65/0.99  
% 3.65/0.99  fof(f99,plain,(
% 3.65/0.99    r2_hidden(sK9,k2_zfmisc_1(sK10,sK11))),
% 3.65/0.99    inference(cnf_transformation,[],[f60])).
% 3.65/0.99  
% 3.65/0.99  fof(f6,axiom,(
% 3.65/0.99    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f24,plain,(
% 3.65/0.99    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.65/0.99    inference(ennf_transformation,[],[f6])).
% 3.65/0.99  
% 3.65/0.99  fof(f49,plain,(
% 3.65/0.99    ! [X0] : (? [X3,X4] : k4_tarski(X3,X4) = X0 => k4_tarski(sK4(X0),sK5(X0)) = X0)),
% 3.65/0.99    introduced(choice_axiom,[])).
% 3.65/0.99  
% 3.65/0.99  fof(f50,plain,(
% 3.65/0.99    ! [X0,X1,X2] : (k4_tarski(sK4(X0),sK5(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 3.65/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f24,f49])).
% 3.65/0.99  
% 3.65/0.99  fof(f79,plain,(
% 3.65/0.99    ( ! [X2,X0,X1] : (k4_tarski(sK4(X0),sK5(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 3.65/0.99    inference(cnf_transformation,[],[f50])).
% 3.65/0.99  
% 3.65/0.99  fof(f18,axiom,(
% 3.65/0.99    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f97,plain,(
% 3.65/0.99    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 3.65/0.99    inference(cnf_transformation,[],[f18])).
% 3.65/0.99  
% 3.65/0.99  fof(f15,axiom,(
% 3.65/0.99    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f21,plain,(
% 3.65/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 3.65/0.99    inference(unused_predicate_definition_removal,[],[f15])).
% 3.65/0.99  
% 3.65/0.99  fof(f29,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0))),
% 3.65/0.99    inference(ennf_transformation,[],[f21])).
% 3.65/0.99  
% 3.65/0.99  fof(f57,plain,(
% 3.65/0.99    ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 => k4_tarski(sK7(X1),sK8(X1)) = X1)),
% 3.65/0.99    introduced(choice_axiom,[])).
% 3.65/0.99  
% 3.65/0.99  fof(f58,plain,(
% 3.65/0.99    ! [X0] : (! [X1] : (k4_tarski(sK7(X1),sK8(X1)) = X1 | ~r2_hidden(X1,X0)) | ~v1_relat_1(X0))),
% 3.65/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f29,f57])).
% 3.65/0.99  
% 3.65/0.99  fof(f94,plain,(
% 3.65/0.99    ( ! [X0,X1] : (k4_tarski(sK7(X1),sK8(X1)) = X1 | ~r2_hidden(X1,X0) | ~v1_relat_1(X0)) )),
% 3.65/0.99    inference(cnf_transformation,[],[f58])).
% 3.65/0.99  
% 3.65/0.99  fof(f16,axiom,(
% 3.65/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f95,plain,(
% 3.65/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.65/0.99    inference(cnf_transformation,[],[f16])).
% 3.65/0.99  
% 3.65/0.99  fof(f100,plain,(
% 3.65/0.99    ~r2_hidden(k2_mcart_1(sK9),sK11) | ~r2_hidden(k1_mcart_1(sK9),sK10)),
% 3.65/0.99    inference(cnf_transformation,[],[f60])).
% 3.65/0.99  
% 3.65/0.99  fof(f98,plain,(
% 3.65/0.99    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 3.65/0.99    inference(cnf_transformation,[],[f18])).
% 3.65/0.99  
% 3.65/0.99  fof(f10,axiom,(
% 3.65/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 3.65/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.65/0.99  
% 3.65/0.99  fof(f51,plain,(
% 3.65/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.65/0.99    inference(nnf_transformation,[],[f10])).
% 3.65/0.99  
% 3.65/0.99  fof(f52,plain,(
% 3.65/0.99    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 3.65/0.99    inference(flattening,[],[f51])).
% 3.65/0.99  
% 3.65/0.99  fof(f83,plain,(
% 3.65/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.65/0.99    inference(cnf_transformation,[],[f52])).
% 3.65/0.99  
% 3.65/0.99  fof(f84,plain,(
% 3.65/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 3.65/0.99    inference(cnf_transformation,[],[f52])).
% 3.65/0.99  
% 3.65/0.99  cnf(c_39,negated_conjecture,
% 3.65/0.99      ( r2_hidden(sK9,k2_zfmisc_1(sK10,sK11)) ),
% 3.65/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1474,plain,
% 3.65/0.99      ( r2_hidden(sK9,k2_zfmisc_1(sK10,sK11)) = iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_18,plain,
% 3.65/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.65/0.99      | k4_tarski(sK4(X0),sK5(X0)) = X0 ),
% 3.65/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1488,plain,
% 3.65/0.99      ( k4_tarski(sK4(X0),sK5(X0)) = X0
% 3.65/0.99      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7256,plain,
% 3.65/0.99      ( k4_tarski(sK4(sK9),sK5(sK9)) = sK9 ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1474,c_1488]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_37,plain,
% 3.65/0.99      ( k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
% 3.65/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7269,plain,
% 3.65/0.99      ( k1_mcart_1(sK9) = sK4(sK9) ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_7256,c_37]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_33,plain,
% 3.65/0.99      ( ~ r2_hidden(X0,X1)
% 3.65/0.99      | ~ v1_relat_1(X1)
% 3.65/0.99      | k4_tarski(sK7(X0),sK8(X0)) = X0 ),
% 3.65/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_34,plain,
% 3.65/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.65/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_462,plain,
% 3.65/0.99      ( ~ r2_hidden(X0,X1)
% 3.65/0.99      | k2_zfmisc_1(X2,X3) != X1
% 3.65/0.99      | k4_tarski(sK7(X0),sK8(X0)) = X0 ),
% 3.65/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_34]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_463,plain,
% 3.65/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 3.65/0.99      | k4_tarski(sK7(X0),sK8(X0)) = X0 ),
% 3.65/0.99      inference(unflattening,[status(thm)],[c_462]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1473,plain,
% 3.65/0.99      ( k4_tarski(sK7(X0),sK8(X0)) = X0
% 3.65/0.99      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3498,plain,
% 3.65/0.99      ( k4_tarski(sK7(sK9),sK8(sK9)) = sK9 ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1474,c_1473]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3704,plain,
% 3.65/0.99      ( k1_mcart_1(sK9) = sK7(sK9) ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_3498,c_37]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7580,plain,
% 3.65/0.99      ( sK7(sK9) = sK4(sK9) ),
% 3.65/0.99      inference(demodulation,[status(thm)],[c_7269,c_3704]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_38,negated_conjecture,
% 3.65/0.99      ( ~ r2_hidden(k1_mcart_1(sK9),sK10)
% 3.65/0.99      | ~ r2_hidden(k2_mcart_1(sK9),sK11) ),
% 3.65/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1475,plain,
% 3.65/0.99      ( r2_hidden(k1_mcart_1(sK9),sK10) != iProver_top
% 3.65/0.99      | r2_hidden(k2_mcart_1(sK9),sK11) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3978,plain,
% 3.65/0.99      ( r2_hidden(k2_mcart_1(sK9),sK11) != iProver_top
% 3.65/0.99      | r2_hidden(sK7(sK9),sK10) != iProver_top ),
% 3.65/0.99      inference(demodulation,[status(thm)],[c_3704,c_1475]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_36,plain,
% 3.65/0.99      ( k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
% 3.65/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3705,plain,
% 3.65/0.99      ( k2_mcart_1(sK9) = sK8(sK9) ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_3498,c_36]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_3979,plain,
% 3.65/0.99      ( r2_hidden(sK8(sK9),sK11) != iProver_top
% 3.65/0.99      | r2_hidden(sK7(sK9),sK10) != iProver_top ),
% 3.65/0.99      inference(light_normalisation,[status(thm)],[c_3978,c_3705]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_14849,plain,
% 3.65/0.99      ( r2_hidden(sK8(sK9),sK11) != iProver_top
% 3.65/0.99      | r2_hidden(sK4(sK9),sK10) != iProver_top ),
% 3.65/0.99      inference(demodulation,[status(thm)],[c_7580,c_3979]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7270,plain,
% 3.65/0.99      ( k2_mcart_1(sK9) = sK5(sK9) ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_7256,c_36]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7581,plain,
% 3.65/0.99      ( sK8(sK9) = sK5(sK9) ),
% 3.65/0.99      inference(demodulation,[status(thm)],[c_7270,c_3705]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_14852,plain,
% 3.65/0.99      ( r2_hidden(sK5(sK9),sK11) != iProver_top
% 3.65/0.99      | r2_hidden(sK4(sK9),sK10) != iProver_top ),
% 3.65/0.99      inference(light_normalisation,[status(thm)],[c_14849,c_7581]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_24,plain,
% 3.65/0.99      ( r2_hidden(X0,X1)
% 3.65/0.99      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 3.65/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1482,plain,
% 3.65/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.65/0.99      | r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7268,plain,
% 3.65/0.99      ( r2_hidden(sK4(sK9),X0) = iProver_top
% 3.65/0.99      | r2_hidden(sK9,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_7256,c_1482]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_13168,plain,
% 3.65/0.99      ( r2_hidden(sK4(sK9),sK10) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1474,c_7268]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_23,plain,
% 3.65/0.99      ( r2_hidden(X0,X1)
% 3.65/0.99      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 3.65/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_1483,plain,
% 3.65/0.99      ( r2_hidden(X0,X1) = iProver_top
% 3.65/0.99      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 3.65/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7267,plain,
% 3.65/0.99      ( r2_hidden(sK5(sK9),X0) = iProver_top
% 3.65/0.99      | r2_hidden(sK9,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_7256,c_1483]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(c_7659,plain,
% 3.65/0.99      ( r2_hidden(sK5(sK9),sK11) = iProver_top ),
% 3.65/0.99      inference(superposition,[status(thm)],[c_1474,c_7267]) ).
% 3.65/0.99  
% 3.65/0.99  cnf(contradiction,plain,
% 3.65/0.99      ( $false ),
% 3.65/0.99      inference(minisat,[status(thm)],[c_14852,c_13168,c_7659]) ).
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.65/0.99  
% 3.65/0.99  ------                               Statistics
% 3.65/0.99  
% 3.65/0.99  ------ General
% 3.65/0.99  
% 3.65/0.99  abstr_ref_over_cycles:                  0
% 3.65/0.99  abstr_ref_under_cycles:                 0
% 3.65/0.99  gc_basic_clause_elim:                   0
% 3.65/0.99  forced_gc_time:                         0
% 3.65/0.99  parsing_time:                           0.008
% 3.65/0.99  unif_index_cands_time:                  0.
% 3.65/0.99  unif_index_add_time:                    0.
% 3.65/0.99  orderings_time:                         0.
% 3.65/0.99  out_proof_time:                         0.009
% 3.65/0.99  total_time:                             0.392
% 3.65/0.99  num_of_symbols:                         55
% 3.65/0.99  num_of_terms:                           18815
% 3.65/0.99  
% 3.65/0.99  ------ Preprocessing
% 3.65/0.99  
% 3.65/0.99  num_of_splits:                          0
% 3.65/0.99  num_of_split_atoms:                     0
% 3.65/0.99  num_of_reused_defs:                     0
% 3.65/0.99  num_eq_ax_congr_red:                    51
% 3.65/0.99  num_of_sem_filtered_clauses:            1
% 3.65/0.99  num_of_subtypes:                        0
% 3.65/0.99  monotx_restored_types:                  0
% 3.65/0.99  sat_num_of_epr_types:                   0
% 3.65/0.99  sat_num_of_non_cyclic_types:            0
% 3.65/0.99  sat_guarded_non_collapsed_types:        0
% 3.65/0.99  num_pure_diseq_elim:                    0
% 3.65/0.99  simp_replaced_by:                       0
% 3.65/0.99  res_preprocessed:                       180
% 3.65/0.99  prep_upred:                             0
% 3.65/0.99  prep_unflattend:                        1
% 3.65/0.99  smt_new_axioms:                         0
% 3.65/0.99  pred_elim_cands:                        2
% 3.65/0.99  pred_elim:                              1
% 3.65/0.99  pred_elim_cl:                           1
% 3.65/0.99  pred_elim_cycles:                       3
% 3.65/0.99  merged_defs:                            8
% 3.65/0.99  merged_defs_ncl:                        0
% 3.65/0.99  bin_hyper_res:                          8
% 3.65/0.99  prep_cycles:                            4
% 3.65/0.99  pred_elim_time:                         0.001
% 3.65/0.99  splitting_time:                         0.
% 3.65/0.99  sem_filter_time:                        0.
% 3.65/0.99  monotx_time:                            0.
% 3.65/0.99  subtype_inf_time:                       0.
% 3.65/0.99  
% 3.65/0.99  ------ Problem properties
% 3.65/0.99  
% 3.65/0.99  clauses:                                39
% 3.65/0.99  conjectures:                            2
% 3.65/0.99  epr:                                    3
% 3.65/0.99  horn:                                   33
% 3.65/0.99  ground:                                 2
% 3.65/0.99  unary:                                  8
% 3.65/0.99  binary:                                 18
% 3.65/0.99  lits:                                   84
% 3.65/0.99  lits_eq:                                21
% 3.65/0.99  fd_pure:                                0
% 3.65/0.99  fd_pseudo:                              0
% 3.65/0.99  fd_cond:                                1
% 3.65/0.99  fd_pseudo_cond:                         7
% 3.65/0.99  ac_symbols:                             0
% 3.65/0.99  
% 3.65/0.99  ------ Propositional Solver
% 3.65/0.99  
% 3.65/0.99  prop_solver_calls:                      31
% 3.65/0.99  prop_fast_solver_calls:                 989
% 3.65/0.99  smt_solver_calls:                       0
% 3.65/0.99  smt_fast_solver_calls:                  0
% 3.65/0.99  prop_num_of_clauses:                    7992
% 3.65/0.99  prop_preprocess_simplified:             18873
% 3.65/0.99  prop_fo_subsumed:                       3
% 3.65/0.99  prop_solver_time:                       0.
% 3.65/0.99  smt_solver_time:                        0.
% 3.65/0.99  smt_fast_solver_time:                   0.
% 3.65/0.99  prop_fast_solver_time:                  0.
% 3.65/0.99  prop_unsat_core_time:                   0.
% 3.65/0.99  
% 3.65/0.99  ------ QBF
% 3.65/0.99  
% 3.65/0.99  qbf_q_res:                              0
% 3.65/0.99  qbf_num_tautologies:                    0
% 3.65/0.99  qbf_prep_cycles:                        0
% 3.65/0.99  
% 3.65/0.99  ------ BMC1
% 3.65/0.99  
% 3.65/0.99  bmc1_current_bound:                     -1
% 3.65/0.99  bmc1_last_solved_bound:                 -1
% 3.65/0.99  bmc1_unsat_core_size:                   -1
% 3.65/0.99  bmc1_unsat_core_parents_size:           -1
% 3.65/0.99  bmc1_merge_next_fun:                    0
% 3.65/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.65/0.99  
% 3.65/0.99  ------ Instantiation
% 3.65/0.99  
% 3.65/0.99  inst_num_of_clauses:                    1951
% 3.65/0.99  inst_num_in_passive:                    1128
% 3.65/0.99  inst_num_in_active:                     488
% 3.65/0.99  inst_num_in_unprocessed:                336
% 3.65/0.99  inst_num_of_loops:                      560
% 3.65/0.99  inst_num_of_learning_restarts:          0
% 3.65/0.99  inst_num_moves_active_passive:          70
% 3.65/0.99  inst_lit_activity:                      0
% 3.65/0.99  inst_lit_activity_moves:                0
% 3.65/0.99  inst_num_tautologies:                   0
% 3.65/0.99  inst_num_prop_implied:                  0
% 3.65/0.99  inst_num_existing_simplified:           0
% 3.65/0.99  inst_num_eq_res_simplified:             0
% 3.65/0.99  inst_num_child_elim:                    0
% 3.65/0.99  inst_num_of_dismatching_blockings:      663
% 3.65/0.99  inst_num_of_non_proper_insts:           1199
% 3.65/0.99  inst_num_of_duplicates:                 0
% 3.65/0.99  inst_inst_num_from_inst_to_res:         0
% 3.65/0.99  inst_dismatching_checking_time:         0.
% 3.65/0.99  
% 3.65/0.99  ------ Resolution
% 3.65/0.99  
% 3.65/0.99  res_num_of_clauses:                     0
% 3.65/0.99  res_num_in_passive:                     0
% 3.65/0.99  res_num_in_active:                      0
% 3.65/0.99  res_num_of_loops:                       184
% 3.65/0.99  res_forward_subset_subsumed:            108
% 3.65/0.99  res_backward_subset_subsumed:           6
% 3.65/0.99  res_forward_subsumed:                   0
% 3.65/0.99  res_backward_subsumed:                  0
% 3.65/0.99  res_forward_subsumption_resolution:     0
% 3.65/0.99  res_backward_subsumption_resolution:    0
% 3.65/0.99  res_clause_to_clause_subsumption:       1061
% 3.65/0.99  res_orphan_elimination:                 0
% 3.65/0.99  res_tautology_del:                      55
% 3.65/0.99  res_num_eq_res_simplified:              0
% 3.65/0.99  res_num_sel_changes:                    0
% 3.65/0.99  res_moves_from_active_to_pass:          0
% 3.65/0.99  
% 3.65/0.99  ------ Superposition
% 3.65/0.99  
% 3.65/0.99  sup_time_total:                         0.
% 3.65/0.99  sup_time_generating:                    0.
% 3.65/0.99  sup_time_sim_full:                      0.
% 3.65/0.99  sup_time_sim_immed:                     0.
% 3.65/0.99  
% 3.65/0.99  sup_num_of_clauses:                     357
% 3.65/0.99  sup_num_in_active:                      98
% 3.65/0.99  sup_num_in_passive:                     259
% 3.65/0.99  sup_num_of_loops:                       110
% 3.65/0.99  sup_fw_superposition:                   152
% 3.65/0.99  sup_bw_superposition:                   250
% 3.65/0.99  sup_immediate_simplified:               40
% 3.65/0.99  sup_given_eliminated:                   1
% 3.65/0.99  comparisons_done:                       0
% 3.65/0.99  comparisons_avoided:                    1
% 3.65/0.99  
% 3.65/0.99  ------ Simplifications
% 3.65/0.99  
% 3.65/0.99  
% 3.65/0.99  sim_fw_subset_subsumed:                 12
% 3.65/0.99  sim_bw_subset_subsumed:                 4
% 3.65/0.99  sim_fw_subsumed:                        14
% 3.65/0.99  sim_bw_subsumed:                        8
% 3.65/0.99  sim_fw_subsumption_res:                 0
% 3.65/0.99  sim_bw_subsumption_res:                 0
% 3.65/0.99  sim_tautology_del:                      17
% 3.65/0.99  sim_eq_tautology_del:                   3
% 3.65/0.99  sim_eq_res_simp:                        2
% 3.65/0.99  sim_fw_demodulated:                     2
% 3.65/0.99  sim_bw_demodulated:                     6
% 3.65/0.99  sim_light_normalised:                   8
% 3.65/0.99  sim_joinable_taut:                      0
% 3.65/0.99  sim_joinable_simp:                      0
% 3.65/0.99  sim_ac_normalised:                      0
% 3.65/0.99  sim_smt_subsumption:                    0
% 3.65/0.99  
%------------------------------------------------------------------------------
