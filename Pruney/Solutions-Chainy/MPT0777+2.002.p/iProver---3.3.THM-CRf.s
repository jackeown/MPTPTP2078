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
% DateTime   : Thu Dec  3 11:54:19 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 138 expanded)
%              Number of clauses        :   24 (  37 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :   71 ( 194 expanded)
%              Number of equality atoms :   45 ( 132 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k2_wellord1(X2,k3_xboole_0(X0,X1)) != k2_wellord1(k2_wellord1(X2,X0),X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( k2_wellord1(X2,k3_xboole_0(X0,X1)) != k2_wellord1(k2_wellord1(X2,X0),X1)
        & v1_relat_1(X2) )
   => ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f17,f15])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k1_enumset1(X0,X0,k2_zfmisc_1(X1,X1))) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f18,f22])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X2,X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) = k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X1)),X2)) ),
    inference(definition_unfolding,[],[f14,f22,f22,f22,f22])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X2,X0,X3,X1] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X2,X2,X3))) = k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f16,f22,f22,f22])).

fof(f21,plain,(
    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f26,plain,(
    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    inference(definition_unfolding,[],[f21,f22])).

cnf(c_5,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_46,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_134,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_wellord1(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_48,plain,
    ( ~ v1_relat_1(X0_36)
    | v1_relat_1(k2_wellord1(X0_36,X1_36)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_133,plain,
    ( v1_relat_1(X0_36) != iProver_top
    | v1_relat_1(k2_wellord1(X0_36,X1_36)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k1_setfam_1(k1_enumset1(X0,X0,k2_zfmisc_1(X1,X1))) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_49,plain,
    ( ~ v1_relat_1(X0_36)
    | k1_setfam_1(k1_enumset1(X0_36,X0_36,k2_zfmisc_1(X1_36,X1_36))) = k2_wellord1(X0_36,X1_36) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_132,plain,
    ( k1_setfam_1(k1_enumset1(X0_36,X0_36,k2_zfmisc_1(X1_36,X1_36))) = k2_wellord1(X0_36,X1_36)
    | v1_relat_1(X0_36) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_213,plain,
    ( k1_setfam_1(k1_enumset1(k2_wellord1(X0_36,X1_36),k2_wellord1(X0_36,X1_36),k2_zfmisc_1(X2_36,X2_36))) = k2_wellord1(k2_wellord1(X0_36,X1_36),X2_36)
    | v1_relat_1(X0_36) != iProver_top ),
    inference(superposition,[status(thm)],[c_133,c_132])).

cnf(c_1385,plain,
    ( k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0_36),k2_wellord1(sK2,X0_36),k2_zfmisc_1(X1_36,X1_36))) = k2_wellord1(k2_wellord1(sK2,X0_36),X1_36) ),
    inference(superposition,[status(thm)],[c_134,c_213])).

cnf(c_212,plain,
    ( k1_setfam_1(k1_enumset1(sK2,sK2,k2_zfmisc_1(X0_36,X0_36))) = k2_wellord1(sK2,X0_36) ),
    inference(superposition,[status(thm)],[c_134,c_132])).

cnf(c_0,plain,
    ( k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X1)),X2)) = k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_51,plain,
    ( k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0_36,X0_36,X1_36)),k1_setfam_1(k1_enumset1(X0_36,X0_36,X1_36)),X2_36)) = k1_setfam_1(k1_enumset1(X0_36,X0_36,k1_setfam_1(k1_enumset1(X1_36,X1_36,X2_36)))) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_459,plain,
    ( k1_setfam_1(k1_enumset1(sK2,sK2,k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0_36,X0_36),k2_zfmisc_1(X0_36,X0_36),X1_36)))) = k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0_36),k2_wellord1(sK2,X0_36),X1_36)) ),
    inference(superposition,[status(thm)],[c_212,c_51])).

cnf(c_1,plain,
    ( k2_zfmisc_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X2,X2,X3))) = k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_50,plain,
    ( k2_zfmisc_1(k1_setfam_1(k1_enumset1(X0_36,X0_36,X1_36)),k1_setfam_1(k1_enumset1(X2_36,X2_36,X3_36))) = k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0_36,X2_36),k2_zfmisc_1(X0_36,X2_36),k2_zfmisc_1(X1_36,X3_36))) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_281,plain,
    ( k1_setfam_1(k1_enumset1(sK2,sK2,k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0_36,X0_36),k2_zfmisc_1(X0_36,X0_36),k2_zfmisc_1(X1_36,X1_36))))) = k2_wellord1(sK2,k1_setfam_1(k1_enumset1(X0_36,X0_36,X1_36))) ),
    inference(superposition,[status(thm)],[c_50,c_212])).

cnf(c_575,plain,
    ( k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0_36),k2_wellord1(sK2,X0_36),k2_zfmisc_1(X1_36,X1_36))) = k2_wellord1(sK2,k1_setfam_1(k1_enumset1(X0_36,X0_36,X1_36))) ),
    inference(superposition,[status(thm)],[c_459,c_281])).

cnf(c_2047,plain,
    ( k2_wellord1(sK2,k1_setfam_1(k1_enumset1(X0_36,X0_36,X1_36))) = k2_wellord1(k2_wellord1(sK2,X0_36),X1_36) ),
    inference(demodulation,[status(thm)],[c_1385,c_575])).

cnf(c_4,negated_conjecture,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_47,negated_conjecture,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_2084,plain,
    ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
    inference(demodulation,[status(thm)],[c_2047,c_47])).

cnf(c_2100,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2084])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:30:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.57/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/0.98  
% 2.57/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.57/0.98  
% 2.57/0.98  ------  iProver source info
% 2.57/0.98  
% 2.57/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.57/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.57/0.98  git: non_committed_changes: false
% 2.57/0.98  git: last_make_outside_of_git: false
% 2.57/0.98  
% 2.57/0.98  ------ 
% 2.57/0.98  
% 2.57/0.98  ------ Input Options
% 2.57/0.98  
% 2.57/0.98  --out_options                           all
% 2.57/0.98  --tptp_safe_out                         true
% 2.57/0.98  --problem_path                          ""
% 2.57/0.98  --include_path                          ""
% 2.57/0.98  --clausifier                            res/vclausify_rel
% 2.57/0.98  --clausifier_options                    --mode clausify
% 2.57/0.98  --stdin                                 false
% 2.57/0.98  --stats_out                             all
% 2.57/0.98  
% 2.57/0.98  ------ General Options
% 2.57/0.98  
% 2.57/0.98  --fof                                   false
% 2.57/0.98  --time_out_real                         305.
% 2.57/0.98  --time_out_virtual                      -1.
% 2.57/0.98  --symbol_type_check                     false
% 2.57/0.98  --clausify_out                          false
% 2.57/0.98  --sig_cnt_out                           false
% 2.57/0.98  --trig_cnt_out                          false
% 2.57/0.98  --trig_cnt_out_tolerance                1.
% 2.57/0.98  --trig_cnt_out_sk_spl                   false
% 2.57/0.98  --abstr_cl_out                          false
% 2.57/0.98  
% 2.57/0.98  ------ Global Options
% 2.57/0.98  
% 2.57/0.98  --schedule                              default
% 2.57/0.98  --add_important_lit                     false
% 2.57/0.98  --prop_solver_per_cl                    1000
% 2.57/0.98  --min_unsat_core                        false
% 2.57/0.98  --soft_assumptions                      false
% 2.57/0.98  --soft_lemma_size                       3
% 2.57/0.98  --prop_impl_unit_size                   0
% 2.57/0.98  --prop_impl_unit                        []
% 2.57/0.98  --share_sel_clauses                     true
% 2.57/0.98  --reset_solvers                         false
% 2.57/0.98  --bc_imp_inh                            [conj_cone]
% 2.57/0.98  --conj_cone_tolerance                   3.
% 2.57/0.98  --extra_neg_conj                        none
% 2.57/0.98  --large_theory_mode                     true
% 2.57/0.98  --prolific_symb_bound                   200
% 2.57/0.98  --lt_threshold                          2000
% 2.57/0.98  --clause_weak_htbl                      true
% 2.57/0.98  --gc_record_bc_elim                     false
% 2.57/0.98  
% 2.57/0.98  ------ Preprocessing Options
% 2.57/0.98  
% 2.57/0.98  --preprocessing_flag                    true
% 2.57/0.98  --time_out_prep_mult                    0.1
% 2.57/0.98  --splitting_mode                        input
% 2.57/0.98  --splitting_grd                         true
% 2.57/0.98  --splitting_cvd                         false
% 2.57/0.98  --splitting_cvd_svl                     false
% 2.57/0.98  --splitting_nvd                         32
% 2.57/0.98  --sub_typing                            true
% 2.57/0.98  --prep_gs_sim                           true
% 2.57/0.98  --prep_unflatten                        true
% 2.57/0.98  --prep_res_sim                          true
% 2.57/0.98  --prep_upred                            true
% 2.57/0.98  --prep_sem_filter                       exhaustive
% 2.57/0.98  --prep_sem_filter_out                   false
% 2.57/0.98  --pred_elim                             true
% 2.57/0.98  --res_sim_input                         true
% 2.57/0.98  --eq_ax_congr_red                       true
% 2.57/0.98  --pure_diseq_elim                       true
% 2.57/0.98  --brand_transform                       false
% 2.57/0.98  --non_eq_to_eq                          false
% 2.57/0.98  --prep_def_merge                        true
% 2.57/0.98  --prep_def_merge_prop_impl              false
% 2.57/0.98  --prep_def_merge_mbd                    true
% 2.57/0.98  --prep_def_merge_tr_red                 false
% 2.57/0.98  --prep_def_merge_tr_cl                  false
% 2.57/0.98  --smt_preprocessing                     true
% 2.57/0.98  --smt_ac_axioms                         fast
% 2.57/0.98  --preprocessed_out                      false
% 2.57/0.98  --preprocessed_stats                    false
% 2.57/0.98  
% 2.57/0.98  ------ Abstraction refinement Options
% 2.57/0.98  
% 2.57/0.98  --abstr_ref                             []
% 2.57/0.98  --abstr_ref_prep                        false
% 2.57/0.98  --abstr_ref_until_sat                   false
% 2.57/0.98  --abstr_ref_sig_restrict                funpre
% 2.57/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.57/0.98  --abstr_ref_under                       []
% 2.57/0.98  
% 2.57/0.98  ------ SAT Options
% 2.57/0.98  
% 2.57/0.98  --sat_mode                              false
% 2.57/0.98  --sat_fm_restart_options                ""
% 2.57/0.98  --sat_gr_def                            false
% 2.57/0.98  --sat_epr_types                         true
% 2.57/0.98  --sat_non_cyclic_types                  false
% 2.57/0.98  --sat_finite_models                     false
% 2.57/0.98  --sat_fm_lemmas                         false
% 2.57/0.98  --sat_fm_prep                           false
% 2.57/0.98  --sat_fm_uc_incr                        true
% 2.57/0.98  --sat_out_model                         small
% 2.57/0.98  --sat_out_clauses                       false
% 2.57/0.98  
% 2.57/0.98  ------ QBF Options
% 2.57/0.98  
% 2.57/0.98  --qbf_mode                              false
% 2.57/0.98  --qbf_elim_univ                         false
% 2.57/0.98  --qbf_dom_inst                          none
% 2.57/0.98  --qbf_dom_pre_inst                      false
% 2.57/0.98  --qbf_sk_in                             false
% 2.57/0.98  --qbf_pred_elim                         true
% 2.57/0.98  --qbf_split                             512
% 2.57/0.98  
% 2.57/0.98  ------ BMC1 Options
% 2.57/0.98  
% 2.57/0.98  --bmc1_incremental                      false
% 2.57/0.98  --bmc1_axioms                           reachable_all
% 2.57/0.98  --bmc1_min_bound                        0
% 2.57/0.98  --bmc1_max_bound                        -1
% 2.57/0.98  --bmc1_max_bound_default                -1
% 2.57/0.98  --bmc1_symbol_reachability              true
% 2.57/0.98  --bmc1_property_lemmas                  false
% 2.57/0.98  --bmc1_k_induction                      false
% 2.57/0.98  --bmc1_non_equiv_states                 false
% 2.57/0.98  --bmc1_deadlock                         false
% 2.57/0.98  --bmc1_ucm                              false
% 2.57/0.98  --bmc1_add_unsat_core                   none
% 2.57/0.98  --bmc1_unsat_core_children              false
% 2.57/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.57/0.98  --bmc1_out_stat                         full
% 2.57/0.98  --bmc1_ground_init                      false
% 2.57/0.98  --bmc1_pre_inst_next_state              false
% 2.57/0.98  --bmc1_pre_inst_state                   false
% 2.57/0.98  --bmc1_pre_inst_reach_state             false
% 2.57/0.98  --bmc1_out_unsat_core                   false
% 2.57/0.98  --bmc1_aig_witness_out                  false
% 2.57/0.98  --bmc1_verbose                          false
% 2.57/0.98  --bmc1_dump_clauses_tptp                false
% 2.57/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.57/0.98  --bmc1_dump_file                        -
% 2.57/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.57/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.57/0.98  --bmc1_ucm_extend_mode                  1
% 2.57/0.98  --bmc1_ucm_init_mode                    2
% 2.57/0.98  --bmc1_ucm_cone_mode                    none
% 2.57/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.57/0.98  --bmc1_ucm_relax_model                  4
% 2.57/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.57/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.57/0.98  --bmc1_ucm_layered_model                none
% 2.57/0.98  --bmc1_ucm_max_lemma_size               10
% 2.57/0.98  
% 2.57/0.98  ------ AIG Options
% 2.57/0.98  
% 2.57/0.98  --aig_mode                              false
% 2.57/0.98  
% 2.57/0.98  ------ Instantiation Options
% 2.57/0.98  
% 2.57/0.98  --instantiation_flag                    true
% 2.57/0.98  --inst_sos_flag                         false
% 2.57/0.98  --inst_sos_phase                        true
% 2.57/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.57/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.57/0.98  --inst_lit_sel_side                     num_symb
% 2.57/0.98  --inst_solver_per_active                1400
% 2.57/0.98  --inst_solver_calls_frac                1.
% 2.57/0.98  --inst_passive_queue_type               priority_queues
% 2.57/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.57/0.98  --inst_passive_queues_freq              [25;2]
% 2.57/0.98  --inst_dismatching                      true
% 2.57/0.98  --inst_eager_unprocessed_to_passive     true
% 2.57/0.98  --inst_prop_sim_given                   true
% 2.57/0.98  --inst_prop_sim_new                     false
% 2.57/0.98  --inst_subs_new                         false
% 2.57/0.98  --inst_eq_res_simp                      false
% 2.57/0.98  --inst_subs_given                       false
% 2.57/0.98  --inst_orphan_elimination               true
% 2.57/0.98  --inst_learning_loop_flag               true
% 2.57/0.98  --inst_learning_start                   3000
% 2.57/0.98  --inst_learning_factor                  2
% 2.57/0.98  --inst_start_prop_sim_after_learn       3
% 2.57/0.98  --inst_sel_renew                        solver
% 2.57/0.98  --inst_lit_activity_flag                true
% 2.57/0.98  --inst_restr_to_given                   false
% 2.57/0.98  --inst_activity_threshold               500
% 2.57/0.98  --inst_out_proof                        true
% 2.57/0.98  
% 2.57/0.98  ------ Resolution Options
% 2.57/0.98  
% 2.57/0.98  --resolution_flag                       true
% 2.57/0.98  --res_lit_sel                           adaptive
% 2.57/0.98  --res_lit_sel_side                      none
% 2.57/0.98  --res_ordering                          kbo
% 2.57/0.98  --res_to_prop_solver                    active
% 2.57/0.98  --res_prop_simpl_new                    false
% 2.57/0.98  --res_prop_simpl_given                  true
% 2.57/0.98  --res_passive_queue_type                priority_queues
% 2.57/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.57/0.98  --res_passive_queues_freq               [15;5]
% 2.57/0.98  --res_forward_subs                      full
% 2.57/0.98  --res_backward_subs                     full
% 2.57/0.98  --res_forward_subs_resolution           true
% 2.57/0.98  --res_backward_subs_resolution          true
% 2.57/0.98  --res_orphan_elimination                true
% 2.57/0.98  --res_time_limit                        2.
% 2.57/0.98  --res_out_proof                         true
% 2.57/0.98  
% 2.57/0.98  ------ Superposition Options
% 2.57/0.98  
% 2.57/0.98  --superposition_flag                    true
% 2.57/0.98  --sup_passive_queue_type                priority_queues
% 2.57/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.57/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.57/0.98  --demod_completeness_check              fast
% 2.57/0.98  --demod_use_ground                      true
% 2.57/0.98  --sup_to_prop_solver                    passive
% 2.57/0.98  --sup_prop_simpl_new                    true
% 2.57/0.98  --sup_prop_simpl_given                  true
% 2.57/0.98  --sup_fun_splitting                     false
% 2.57/0.98  --sup_smt_interval                      50000
% 2.57/0.98  
% 2.57/0.98  ------ Superposition Simplification Setup
% 2.57/0.98  
% 2.57/0.98  --sup_indices_passive                   []
% 2.57/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.57/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.98  --sup_full_bw                           [BwDemod]
% 2.57/0.98  --sup_immed_triv                        [TrivRules]
% 2.57/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.57/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.98  --sup_immed_bw_main                     []
% 2.57/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.57/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/0.98  
% 2.57/0.98  ------ Combination Options
% 2.57/0.98  
% 2.57/0.98  --comb_res_mult                         3
% 2.57/0.98  --comb_sup_mult                         2
% 2.57/0.98  --comb_inst_mult                        10
% 2.57/0.98  
% 2.57/0.98  ------ Debug Options
% 2.57/0.98  
% 2.57/0.98  --dbg_backtrace                         false
% 2.57/0.98  --dbg_dump_prop_clauses                 false
% 2.57/0.98  --dbg_dump_prop_clauses_file            -
% 2.57/0.98  --dbg_out_stat                          false
% 2.57/0.98  ------ Parsing...
% 2.57/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.57/0.98  
% 2.57/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.57/0.98  
% 2.57/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.57/0.98  
% 2.57/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.57/0.98  ------ Proving...
% 2.57/0.98  ------ Problem Properties 
% 2.57/0.98  
% 2.57/0.98  
% 2.57/0.98  clauses                                 6
% 2.57/0.98  conjectures                             2
% 2.57/0.98  EPR                                     1
% 2.57/0.98  Horn                                    6
% 2.57/0.98  unary                                   4
% 2.57/0.98  binary                                  2
% 2.57/0.98  lits                                    8
% 2.57/0.98  lits eq                                 4
% 2.57/0.98  fd_pure                                 0
% 2.57/0.98  fd_pseudo                               0
% 2.57/0.98  fd_cond                                 0
% 2.57/0.98  fd_pseudo_cond                          0
% 2.57/0.98  AC symbols                              0
% 2.57/0.98  
% 2.57/0.98  ------ Schedule dynamic 5 is on 
% 2.57/0.98  
% 2.57/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.57/0.98  
% 2.57/0.98  
% 2.57/0.98  ------ 
% 2.57/0.98  Current options:
% 2.57/0.98  ------ 
% 2.57/0.98  
% 2.57/0.98  ------ Input Options
% 2.57/0.98  
% 2.57/0.98  --out_options                           all
% 2.57/0.98  --tptp_safe_out                         true
% 2.57/0.98  --problem_path                          ""
% 2.57/0.98  --include_path                          ""
% 2.57/0.98  --clausifier                            res/vclausify_rel
% 2.57/0.98  --clausifier_options                    --mode clausify
% 2.57/0.98  --stdin                                 false
% 2.57/0.98  --stats_out                             all
% 2.57/0.98  
% 2.57/0.98  ------ General Options
% 2.57/0.98  
% 2.57/0.98  --fof                                   false
% 2.57/0.98  --time_out_real                         305.
% 2.57/0.98  --time_out_virtual                      -1.
% 2.57/0.98  --symbol_type_check                     false
% 2.57/0.98  --clausify_out                          false
% 2.57/0.98  --sig_cnt_out                           false
% 2.57/0.98  --trig_cnt_out                          false
% 2.57/0.98  --trig_cnt_out_tolerance                1.
% 2.57/0.98  --trig_cnt_out_sk_spl                   false
% 2.57/0.98  --abstr_cl_out                          false
% 2.57/0.98  
% 2.57/0.98  ------ Global Options
% 2.57/0.98  
% 2.57/0.98  --schedule                              default
% 2.57/0.98  --add_important_lit                     false
% 2.57/0.98  --prop_solver_per_cl                    1000
% 2.57/0.98  --min_unsat_core                        false
% 2.57/0.98  --soft_assumptions                      false
% 2.57/0.98  --soft_lemma_size                       3
% 2.57/0.98  --prop_impl_unit_size                   0
% 2.57/0.98  --prop_impl_unit                        []
% 2.57/0.98  --share_sel_clauses                     true
% 2.57/0.98  --reset_solvers                         false
% 2.57/0.98  --bc_imp_inh                            [conj_cone]
% 2.57/0.98  --conj_cone_tolerance                   3.
% 2.57/0.98  --extra_neg_conj                        none
% 2.57/0.98  --large_theory_mode                     true
% 2.57/0.98  --prolific_symb_bound                   200
% 2.57/0.98  --lt_threshold                          2000
% 2.57/0.98  --clause_weak_htbl                      true
% 2.57/0.98  --gc_record_bc_elim                     false
% 2.57/0.98  
% 2.57/0.98  ------ Preprocessing Options
% 2.57/0.98  
% 2.57/0.98  --preprocessing_flag                    true
% 2.57/0.98  --time_out_prep_mult                    0.1
% 2.57/0.98  --splitting_mode                        input
% 2.57/0.98  --splitting_grd                         true
% 2.57/0.98  --splitting_cvd                         false
% 2.57/0.98  --splitting_cvd_svl                     false
% 2.57/0.98  --splitting_nvd                         32
% 2.57/0.98  --sub_typing                            true
% 2.57/0.98  --prep_gs_sim                           true
% 2.57/0.98  --prep_unflatten                        true
% 2.57/0.98  --prep_res_sim                          true
% 2.57/0.98  --prep_upred                            true
% 2.57/0.98  --prep_sem_filter                       exhaustive
% 2.57/0.98  --prep_sem_filter_out                   false
% 2.57/0.98  --pred_elim                             true
% 2.57/0.98  --res_sim_input                         true
% 2.57/0.98  --eq_ax_congr_red                       true
% 2.57/0.98  --pure_diseq_elim                       true
% 2.57/0.98  --brand_transform                       false
% 2.57/0.98  --non_eq_to_eq                          false
% 2.57/0.98  --prep_def_merge                        true
% 2.57/0.98  --prep_def_merge_prop_impl              false
% 2.57/0.98  --prep_def_merge_mbd                    true
% 2.57/0.98  --prep_def_merge_tr_red                 false
% 2.57/0.98  --prep_def_merge_tr_cl                  false
% 2.57/0.98  --smt_preprocessing                     true
% 2.57/0.98  --smt_ac_axioms                         fast
% 2.57/0.98  --preprocessed_out                      false
% 2.57/0.98  --preprocessed_stats                    false
% 2.57/0.98  
% 2.57/0.98  ------ Abstraction refinement Options
% 2.57/0.98  
% 2.57/0.98  --abstr_ref                             []
% 2.57/0.98  --abstr_ref_prep                        false
% 2.57/0.98  --abstr_ref_until_sat                   false
% 2.57/0.98  --abstr_ref_sig_restrict                funpre
% 2.57/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.57/0.98  --abstr_ref_under                       []
% 2.57/0.98  
% 2.57/0.98  ------ SAT Options
% 2.57/0.98  
% 2.57/0.98  --sat_mode                              false
% 2.57/0.98  --sat_fm_restart_options                ""
% 2.57/0.98  --sat_gr_def                            false
% 2.57/0.98  --sat_epr_types                         true
% 2.57/0.98  --sat_non_cyclic_types                  false
% 2.57/0.98  --sat_finite_models                     false
% 2.57/0.98  --sat_fm_lemmas                         false
% 2.57/0.98  --sat_fm_prep                           false
% 2.57/0.98  --sat_fm_uc_incr                        true
% 2.57/0.98  --sat_out_model                         small
% 2.57/0.98  --sat_out_clauses                       false
% 2.57/0.98  
% 2.57/0.98  ------ QBF Options
% 2.57/0.98  
% 2.57/0.98  --qbf_mode                              false
% 2.57/0.98  --qbf_elim_univ                         false
% 2.57/0.98  --qbf_dom_inst                          none
% 2.57/0.98  --qbf_dom_pre_inst                      false
% 2.57/0.98  --qbf_sk_in                             false
% 2.57/0.98  --qbf_pred_elim                         true
% 2.57/0.98  --qbf_split                             512
% 2.57/0.98  
% 2.57/0.98  ------ BMC1 Options
% 2.57/0.98  
% 2.57/0.98  --bmc1_incremental                      false
% 2.57/0.98  --bmc1_axioms                           reachable_all
% 2.57/0.98  --bmc1_min_bound                        0
% 2.57/0.98  --bmc1_max_bound                        -1
% 2.57/0.98  --bmc1_max_bound_default                -1
% 2.57/0.98  --bmc1_symbol_reachability              true
% 2.57/0.98  --bmc1_property_lemmas                  false
% 2.57/0.98  --bmc1_k_induction                      false
% 2.57/0.98  --bmc1_non_equiv_states                 false
% 2.57/0.98  --bmc1_deadlock                         false
% 2.57/0.98  --bmc1_ucm                              false
% 2.57/0.98  --bmc1_add_unsat_core                   none
% 2.57/0.98  --bmc1_unsat_core_children              false
% 2.57/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.57/0.98  --bmc1_out_stat                         full
% 2.57/0.98  --bmc1_ground_init                      false
% 2.57/0.98  --bmc1_pre_inst_next_state              false
% 2.57/0.98  --bmc1_pre_inst_state                   false
% 2.57/0.98  --bmc1_pre_inst_reach_state             false
% 2.57/0.98  --bmc1_out_unsat_core                   false
% 2.57/0.98  --bmc1_aig_witness_out                  false
% 2.57/0.98  --bmc1_verbose                          false
% 2.57/0.98  --bmc1_dump_clauses_tptp                false
% 2.57/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.57/0.98  --bmc1_dump_file                        -
% 2.57/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.57/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.57/0.98  --bmc1_ucm_extend_mode                  1
% 2.57/0.98  --bmc1_ucm_init_mode                    2
% 2.57/0.98  --bmc1_ucm_cone_mode                    none
% 2.57/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.57/0.98  --bmc1_ucm_relax_model                  4
% 2.57/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.57/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.57/0.98  --bmc1_ucm_layered_model                none
% 2.57/0.98  --bmc1_ucm_max_lemma_size               10
% 2.57/0.98  
% 2.57/0.98  ------ AIG Options
% 2.57/0.98  
% 2.57/0.98  --aig_mode                              false
% 2.57/0.98  
% 2.57/0.98  ------ Instantiation Options
% 2.57/0.98  
% 2.57/0.98  --instantiation_flag                    true
% 2.57/0.98  --inst_sos_flag                         false
% 2.57/0.98  --inst_sos_phase                        true
% 2.57/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.57/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.57/0.98  --inst_lit_sel_side                     none
% 2.57/0.98  --inst_solver_per_active                1400
% 2.57/0.98  --inst_solver_calls_frac                1.
% 2.57/0.98  --inst_passive_queue_type               priority_queues
% 2.57/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.57/0.98  --inst_passive_queues_freq              [25;2]
% 2.57/0.98  --inst_dismatching                      true
% 2.57/0.98  --inst_eager_unprocessed_to_passive     true
% 2.57/0.98  --inst_prop_sim_given                   true
% 2.57/0.98  --inst_prop_sim_new                     false
% 2.57/0.98  --inst_subs_new                         false
% 2.57/0.98  --inst_eq_res_simp                      false
% 2.57/0.98  --inst_subs_given                       false
% 2.57/0.98  --inst_orphan_elimination               true
% 2.57/0.98  --inst_learning_loop_flag               true
% 2.57/0.98  --inst_learning_start                   3000
% 2.57/0.98  --inst_learning_factor                  2
% 2.57/0.98  --inst_start_prop_sim_after_learn       3
% 2.57/0.98  --inst_sel_renew                        solver
% 2.57/0.98  --inst_lit_activity_flag                true
% 2.57/0.98  --inst_restr_to_given                   false
% 2.57/0.98  --inst_activity_threshold               500
% 2.57/0.98  --inst_out_proof                        true
% 2.57/0.98  
% 2.57/0.98  ------ Resolution Options
% 2.57/0.98  
% 2.57/0.98  --resolution_flag                       false
% 2.57/0.98  --res_lit_sel                           adaptive
% 2.57/0.98  --res_lit_sel_side                      none
% 2.57/0.98  --res_ordering                          kbo
% 2.57/0.98  --res_to_prop_solver                    active
% 2.57/0.98  --res_prop_simpl_new                    false
% 2.57/0.98  --res_prop_simpl_given                  true
% 2.57/0.98  --res_passive_queue_type                priority_queues
% 2.57/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.57/0.98  --res_passive_queues_freq               [15;5]
% 2.57/0.98  --res_forward_subs                      full
% 2.57/0.98  --res_backward_subs                     full
% 2.57/0.98  --res_forward_subs_resolution           true
% 2.57/0.98  --res_backward_subs_resolution          true
% 2.57/0.98  --res_orphan_elimination                true
% 2.57/0.98  --res_time_limit                        2.
% 2.57/0.98  --res_out_proof                         true
% 2.57/0.98  
% 2.57/0.98  ------ Superposition Options
% 2.57/0.98  
% 2.57/0.98  --superposition_flag                    true
% 2.57/0.98  --sup_passive_queue_type                priority_queues
% 2.57/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.57/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.57/0.98  --demod_completeness_check              fast
% 2.57/0.98  --demod_use_ground                      true
% 2.57/0.98  --sup_to_prop_solver                    passive
% 2.57/0.98  --sup_prop_simpl_new                    true
% 2.57/0.98  --sup_prop_simpl_given                  true
% 2.57/0.98  --sup_fun_splitting                     false
% 2.57/0.98  --sup_smt_interval                      50000
% 2.57/0.98  
% 2.57/0.98  ------ Superposition Simplification Setup
% 2.57/0.98  
% 2.57/0.98  --sup_indices_passive                   []
% 2.57/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.57/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.98  --sup_full_bw                           [BwDemod]
% 2.57/0.98  --sup_immed_triv                        [TrivRules]
% 2.57/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.57/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.98  --sup_immed_bw_main                     []
% 2.57/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.57/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/0.98  
% 2.57/0.98  ------ Combination Options
% 2.57/0.98  
% 2.57/0.98  --comb_res_mult                         3
% 2.57/0.98  --comb_sup_mult                         2
% 2.57/0.98  --comb_inst_mult                        10
% 2.57/0.98  
% 2.57/0.98  ------ Debug Options
% 2.57/0.98  
% 2.57/0.98  --dbg_backtrace                         false
% 2.57/0.98  --dbg_dump_prop_clauses                 false
% 2.57/0.98  --dbg_dump_prop_clauses_file            -
% 2.57/0.98  --dbg_out_stat                          false
% 2.57/0.98  
% 2.57/0.98  
% 2.57/0.98  
% 2.57/0.98  
% 2.57/0.98  ------ Proving...
% 2.57/0.98  
% 2.57/0.98  
% 2.57/0.98  % SZS status Theorem for theBenchmark.p
% 2.57/0.98  
% 2.57/0.98   Resolution empty clause
% 2.57/0.98  
% 2.57/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.57/0.98  
% 2.57/0.98  fof(f7,conjecture,(
% 2.57/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1))),
% 2.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/0.98  
% 2.57/0.98  fof(f8,negated_conjecture,(
% 2.57/0.98    ~! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(X2,k3_xboole_0(X0,X1)) = k2_wellord1(k2_wellord1(X2,X0),X1))),
% 2.57/0.98    inference(negated_conjecture,[],[f7])).
% 2.57/0.98  
% 2.57/0.98  fof(f11,plain,(
% 2.57/0.98    ? [X0,X1,X2] : (k2_wellord1(X2,k3_xboole_0(X0,X1)) != k2_wellord1(k2_wellord1(X2,X0),X1) & v1_relat_1(X2))),
% 2.57/0.98    inference(ennf_transformation,[],[f8])).
% 2.57/0.98  
% 2.57/0.98  fof(f12,plain,(
% 2.57/0.98    ? [X0,X1,X2] : (k2_wellord1(X2,k3_xboole_0(X0,X1)) != k2_wellord1(k2_wellord1(X2,X0),X1) & v1_relat_1(X2)) => (k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) & v1_relat_1(sK2))),
% 2.57/0.98    introduced(choice_axiom,[])).
% 2.57/0.98  
% 2.57/0.98  fof(f13,plain,(
% 2.57/0.98    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1)) & v1_relat_1(sK2)),
% 2.57/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f12])).
% 2.57/0.98  
% 2.57/0.98  fof(f20,plain,(
% 2.57/0.98    v1_relat_1(sK2)),
% 2.57/0.98    inference(cnf_transformation,[],[f13])).
% 2.57/0.98  
% 2.57/0.98  fof(f6,axiom,(
% 2.57/0.98    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 2.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/0.98  
% 2.57/0.98  fof(f10,plain,(
% 2.57/0.98    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 2.57/0.98    inference(ennf_transformation,[],[f6])).
% 2.57/0.98  
% 2.57/0.98  fof(f19,plain,(
% 2.57/0.98    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.57/0.98    inference(cnf_transformation,[],[f10])).
% 2.57/0.98  
% 2.57/0.98  fof(f5,axiom,(
% 2.57/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1))),
% 2.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/0.98  
% 2.57/0.98  fof(f9,plain,(
% 2.57/0.98    ! [X0] : (! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) | ~v1_relat_1(X0))),
% 2.57/0.98    inference(ennf_transformation,[],[f5])).
% 2.57/0.98  
% 2.57/0.98  fof(f18,plain,(
% 2.57/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 2.57/0.98    inference(cnf_transformation,[],[f9])).
% 2.57/0.98  
% 2.57/0.98  fof(f4,axiom,(
% 2.57/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/0.98  
% 2.57/0.98  fof(f17,plain,(
% 2.57/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.57/0.98    inference(cnf_transformation,[],[f4])).
% 2.57/0.98  
% 2.57/0.98  fof(f2,axiom,(
% 2.57/0.98    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/0.98  
% 2.57/0.98  fof(f15,plain,(
% 2.57/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.57/0.98    inference(cnf_transformation,[],[f2])).
% 2.57/0.98  
% 2.57/0.98  fof(f22,plain,(
% 2.57/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 2.57/0.98    inference(definition_unfolding,[],[f17,f15])).
% 2.57/0.98  
% 2.57/0.98  fof(f25,plain,(
% 2.57/0.98    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k2_zfmisc_1(X1,X1))) = k2_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 2.57/0.98    inference(definition_unfolding,[],[f18,f22])).
% 2.57/0.98  
% 2.57/0.98  fof(f1,axiom,(
% 2.57/0.98    ! [X0,X1,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/0.98  
% 2.57/0.98  fof(f14,plain,(
% 2.57/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.57/0.98    inference(cnf_transformation,[],[f1])).
% 2.57/0.98  
% 2.57/0.98  fof(f23,plain,(
% 2.57/0.98    ( ! [X2,X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) = k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X1)),X2))) )),
% 2.57/0.98    inference(definition_unfolding,[],[f14,f22,f22,f22,f22])).
% 2.57/0.98  
% 2.57/0.98  fof(f3,axiom,(
% 2.57/0.98    ! [X0,X1,X2,X3] : k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))),
% 2.57/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/0.98  
% 2.57/0.98  fof(f16,plain,(
% 2.57/0.98    ( ! [X2,X0,X3,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) = k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3))) )),
% 2.57/0.98    inference(cnf_transformation,[],[f3])).
% 2.57/0.98  
% 2.57/0.98  fof(f24,plain,(
% 2.57/0.98    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X2,X2,X3))) = k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 2.57/0.98    inference(definition_unfolding,[],[f16,f22,f22,f22])).
% 2.57/0.98  
% 2.57/0.98  fof(f21,plain,(
% 2.57/0.98    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k3_xboole_0(sK0,sK1))),
% 2.57/0.98    inference(cnf_transformation,[],[f13])).
% 2.57/0.98  
% 2.57/0.98  fof(f26,plain,(
% 2.57/0.98    k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1)))),
% 2.57/0.98    inference(definition_unfolding,[],[f21,f22])).
% 2.57/0.98  
% 2.57/0.98  cnf(c_5,negated_conjecture,
% 2.57/0.98      ( v1_relat_1(sK2) ),
% 2.57/0.98      inference(cnf_transformation,[],[f20]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_46,negated_conjecture,
% 2.57/0.98      ( v1_relat_1(sK2) ),
% 2.57/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_134,plain,
% 2.57/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 2.57/0.98      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_3,plain,
% 2.57/0.98      ( ~ v1_relat_1(X0) | v1_relat_1(k2_wellord1(X0,X1)) ),
% 2.57/0.98      inference(cnf_transformation,[],[f19]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_48,plain,
% 2.57/0.98      ( ~ v1_relat_1(X0_36) | v1_relat_1(k2_wellord1(X0_36,X1_36)) ),
% 2.57/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_133,plain,
% 2.57/0.98      ( v1_relat_1(X0_36) != iProver_top
% 2.57/0.98      | v1_relat_1(k2_wellord1(X0_36,X1_36)) = iProver_top ),
% 2.57/0.98      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_2,plain,
% 2.57/0.98      ( ~ v1_relat_1(X0)
% 2.57/0.98      | k1_setfam_1(k1_enumset1(X0,X0,k2_zfmisc_1(X1,X1))) = k2_wellord1(X0,X1) ),
% 2.57/0.98      inference(cnf_transformation,[],[f25]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_49,plain,
% 2.57/0.98      ( ~ v1_relat_1(X0_36)
% 2.57/0.98      | k1_setfam_1(k1_enumset1(X0_36,X0_36,k2_zfmisc_1(X1_36,X1_36))) = k2_wellord1(X0_36,X1_36) ),
% 2.57/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_132,plain,
% 2.57/0.98      ( k1_setfam_1(k1_enumset1(X0_36,X0_36,k2_zfmisc_1(X1_36,X1_36))) = k2_wellord1(X0_36,X1_36)
% 2.57/0.98      | v1_relat_1(X0_36) != iProver_top ),
% 2.57/0.98      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_213,plain,
% 2.57/0.98      ( k1_setfam_1(k1_enumset1(k2_wellord1(X0_36,X1_36),k2_wellord1(X0_36,X1_36),k2_zfmisc_1(X2_36,X2_36))) = k2_wellord1(k2_wellord1(X0_36,X1_36),X2_36)
% 2.57/0.98      | v1_relat_1(X0_36) != iProver_top ),
% 2.57/0.98      inference(superposition,[status(thm)],[c_133,c_132]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1385,plain,
% 2.57/0.98      ( k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0_36),k2_wellord1(sK2,X0_36),k2_zfmisc_1(X1_36,X1_36))) = k2_wellord1(k2_wellord1(sK2,X0_36),X1_36) ),
% 2.57/0.98      inference(superposition,[status(thm)],[c_134,c_213]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_212,plain,
% 2.57/0.98      ( k1_setfam_1(k1_enumset1(sK2,sK2,k2_zfmisc_1(X0_36,X0_36))) = k2_wellord1(sK2,X0_36) ),
% 2.57/0.98      inference(superposition,[status(thm)],[c_134,c_132]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_0,plain,
% 2.57/0.98      ( k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X0,X0,X1)),X2)) = k1_setfam_1(k1_enumset1(X0,X0,k1_setfam_1(k1_enumset1(X1,X1,X2)))) ),
% 2.57/0.98      inference(cnf_transformation,[],[f23]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_51,plain,
% 2.57/0.98      ( k1_setfam_1(k1_enumset1(k1_setfam_1(k1_enumset1(X0_36,X0_36,X1_36)),k1_setfam_1(k1_enumset1(X0_36,X0_36,X1_36)),X2_36)) = k1_setfam_1(k1_enumset1(X0_36,X0_36,k1_setfam_1(k1_enumset1(X1_36,X1_36,X2_36)))) ),
% 2.57/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_459,plain,
% 2.57/0.98      ( k1_setfam_1(k1_enumset1(sK2,sK2,k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0_36,X0_36),k2_zfmisc_1(X0_36,X0_36),X1_36)))) = k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0_36),k2_wellord1(sK2,X0_36),X1_36)) ),
% 2.57/0.98      inference(superposition,[status(thm)],[c_212,c_51]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_1,plain,
% 2.57/0.98      ( k2_zfmisc_1(k1_setfam_1(k1_enumset1(X0,X0,X1)),k1_setfam_1(k1_enumset1(X2,X2,X3))) = k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
% 2.57/0.98      inference(cnf_transformation,[],[f24]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_50,plain,
% 2.57/0.98      ( k2_zfmisc_1(k1_setfam_1(k1_enumset1(X0_36,X0_36,X1_36)),k1_setfam_1(k1_enumset1(X2_36,X2_36,X3_36))) = k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0_36,X2_36),k2_zfmisc_1(X0_36,X2_36),k2_zfmisc_1(X1_36,X3_36))) ),
% 2.57/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_281,plain,
% 2.57/0.98      ( k1_setfam_1(k1_enumset1(sK2,sK2,k1_setfam_1(k1_enumset1(k2_zfmisc_1(X0_36,X0_36),k2_zfmisc_1(X0_36,X0_36),k2_zfmisc_1(X1_36,X1_36))))) = k2_wellord1(sK2,k1_setfam_1(k1_enumset1(X0_36,X0_36,X1_36))) ),
% 2.57/0.98      inference(superposition,[status(thm)],[c_50,c_212]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_575,plain,
% 2.57/0.98      ( k1_setfam_1(k1_enumset1(k2_wellord1(sK2,X0_36),k2_wellord1(sK2,X0_36),k2_zfmisc_1(X1_36,X1_36))) = k2_wellord1(sK2,k1_setfam_1(k1_enumset1(X0_36,X0_36,X1_36))) ),
% 2.57/0.98      inference(superposition,[status(thm)],[c_459,c_281]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_2047,plain,
% 2.57/0.98      ( k2_wellord1(sK2,k1_setfam_1(k1_enumset1(X0_36,X0_36,X1_36))) = k2_wellord1(k2_wellord1(sK2,X0_36),X1_36) ),
% 2.57/0.98      inference(demodulation,[status(thm)],[c_1385,c_575]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_4,negated_conjecture,
% 2.57/0.98      ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
% 2.57/0.98      inference(cnf_transformation,[],[f26]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_47,negated_conjecture,
% 2.57/0.98      ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(sK2,k1_setfam_1(k1_enumset1(sK0,sK0,sK1))) ),
% 2.57/0.98      inference(subtyping,[status(esa)],[c_4]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_2084,plain,
% 2.57/0.98      ( k2_wellord1(k2_wellord1(sK2,sK0),sK1) != k2_wellord1(k2_wellord1(sK2,sK0),sK1) ),
% 2.57/0.98      inference(demodulation,[status(thm)],[c_2047,c_47]) ).
% 2.57/0.98  
% 2.57/0.98  cnf(c_2100,plain,
% 2.57/0.98      ( $false ),
% 2.57/0.98      inference(equality_resolution_simp,[status(thm)],[c_2084]) ).
% 2.57/0.98  
% 2.57/0.98  
% 2.57/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.57/0.98  
% 2.57/0.98  ------                               Statistics
% 2.57/0.98  
% 2.57/0.98  ------ General
% 2.57/0.98  
% 2.57/0.98  abstr_ref_over_cycles:                  0
% 2.57/0.98  abstr_ref_under_cycles:                 0
% 2.57/0.98  gc_basic_clause_elim:                   0
% 2.57/0.98  forced_gc_time:                         0
% 2.57/0.98  parsing_time:                           0.008
% 2.57/0.98  unif_index_cands_time:                  0.
% 2.57/0.98  unif_index_add_time:                    0.
% 2.57/0.98  orderings_time:                         0.
% 2.57/0.98  out_proof_time:                         0.006
% 2.57/0.98  total_time:                             0.13
% 2.57/0.98  num_of_symbols:                         41
% 2.57/0.98  num_of_terms:                           5150
% 2.57/0.98  
% 2.57/0.98  ------ Preprocessing
% 2.57/0.98  
% 2.57/0.98  num_of_splits:                          0
% 2.57/0.98  num_of_split_atoms:                     0
% 2.57/0.98  num_of_reused_defs:                     0
% 2.57/0.98  num_eq_ax_congr_red:                    0
% 2.57/0.98  num_of_sem_filtered_clauses:            1
% 2.57/0.98  num_of_subtypes:                        2
% 2.57/0.98  monotx_restored_types:                  0
% 2.57/0.98  sat_num_of_epr_types:                   0
% 2.57/0.98  sat_num_of_non_cyclic_types:            0
% 2.57/0.98  sat_guarded_non_collapsed_types:        0
% 2.57/0.98  num_pure_diseq_elim:                    0
% 2.57/0.98  simp_replaced_by:                       0
% 2.57/0.98  res_preprocessed:                       35
% 2.57/0.98  prep_upred:                             0
% 2.57/0.98  prep_unflattend:                        0
% 2.57/0.98  smt_new_axioms:                         0
% 2.57/0.98  pred_elim_cands:                        1
% 2.57/0.98  pred_elim:                              0
% 2.57/0.98  pred_elim_cl:                           0
% 2.57/0.98  pred_elim_cycles:                       1
% 2.57/0.98  merged_defs:                            0
% 2.57/0.98  merged_defs_ncl:                        0
% 2.57/0.98  bin_hyper_res:                          0
% 2.57/0.98  prep_cycles:                            3
% 2.57/0.98  pred_elim_time:                         0.
% 2.57/0.98  splitting_time:                         0.
% 2.57/0.98  sem_filter_time:                        0.
% 2.57/0.98  monotx_time:                            0.
% 2.57/0.98  subtype_inf_time:                       0.
% 2.57/0.98  
% 2.57/0.98  ------ Problem properties
% 2.57/0.98  
% 2.57/0.98  clauses:                                6
% 2.57/0.98  conjectures:                            2
% 2.57/0.98  epr:                                    1
% 2.57/0.98  horn:                                   6
% 2.57/0.98  ground:                                 2
% 2.57/0.98  unary:                                  4
% 2.57/0.98  binary:                                 2
% 2.57/0.98  lits:                                   8
% 2.57/0.98  lits_eq:                                4
% 2.57/0.98  fd_pure:                                0
% 2.57/0.98  fd_pseudo:                              0
% 2.57/0.98  fd_cond:                                0
% 2.57/0.98  fd_pseudo_cond:                         0
% 2.57/0.98  ac_symbols:                             0
% 2.57/0.98  
% 2.57/0.98  ------ Propositional Solver
% 2.57/0.98  
% 2.57/0.98  prop_solver_calls:                      25
% 2.57/0.98  prop_fast_solver_calls:                 161
% 2.57/0.98  smt_solver_calls:                       0
% 2.57/0.98  smt_fast_solver_calls:                  0
% 2.57/0.98  prop_num_of_clauses:                    754
% 2.57/0.98  prop_preprocess_simplified:             1429
% 2.57/0.98  prop_fo_subsumed:                       0
% 2.57/0.98  prop_solver_time:                       0.
% 2.57/0.98  smt_solver_time:                        0.
% 2.57/0.98  smt_fast_solver_time:                   0.
% 2.57/0.98  prop_fast_solver_time:                  0.
% 2.57/0.98  prop_unsat_core_time:                   0.
% 2.57/0.98  
% 2.57/0.98  ------ QBF
% 2.57/0.98  
% 2.57/0.98  qbf_q_res:                              0
% 2.57/0.98  qbf_num_tautologies:                    0
% 2.57/0.98  qbf_prep_cycles:                        0
% 2.57/0.98  
% 2.57/0.98  ------ BMC1
% 2.57/0.98  
% 2.57/0.98  bmc1_current_bound:                     -1
% 2.57/0.98  bmc1_last_solved_bound:                 -1
% 2.57/0.98  bmc1_unsat_core_size:                   -1
% 2.57/0.98  bmc1_unsat_core_parents_size:           -1
% 2.57/0.98  bmc1_merge_next_fun:                    0
% 2.57/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.57/0.98  
% 2.57/0.98  ------ Instantiation
% 2.57/0.98  
% 2.57/0.98  inst_num_of_clauses:                    232
% 2.57/0.98  inst_num_in_passive:                    97
% 2.57/0.98  inst_num_in_active:                     135
% 2.57/0.98  inst_num_in_unprocessed:                0
% 2.57/0.98  inst_num_of_loops:                      140
% 2.57/0.98  inst_num_of_learning_restarts:          0
% 2.57/0.98  inst_num_moves_active_passive:          0
% 2.57/0.98  inst_lit_activity:                      0
% 2.57/0.98  inst_lit_activity_moves:                0
% 2.57/0.98  inst_num_tautologies:                   0
% 2.57/0.98  inst_num_prop_implied:                  0
% 2.57/0.98  inst_num_existing_simplified:           0
% 2.57/0.98  inst_num_eq_res_simplified:             0
% 2.57/0.98  inst_num_child_elim:                    0
% 2.57/0.98  inst_num_of_dismatching_blockings:      121
% 2.57/0.98  inst_num_of_non_proper_insts:           251
% 2.57/0.98  inst_num_of_duplicates:                 0
% 2.57/0.98  inst_inst_num_from_inst_to_res:         0
% 2.57/0.98  inst_dismatching_checking_time:         0.
% 2.57/0.98  
% 2.57/0.98  ------ Resolution
% 2.57/0.98  
% 2.57/0.98  res_num_of_clauses:                     0
% 2.57/0.98  res_num_in_passive:                     0
% 2.57/0.98  res_num_in_active:                      0
% 2.57/0.98  res_num_of_loops:                       38
% 2.57/0.98  res_forward_subset_subsumed:            33
% 2.57/0.98  res_backward_subset_subsumed:           0
% 2.57/0.98  res_forward_subsumed:                   0
% 2.57/0.98  res_backward_subsumed:                  0
% 2.57/0.98  res_forward_subsumption_resolution:     0
% 2.57/0.98  res_backward_subsumption_resolution:    0
% 2.57/0.98  res_clause_to_clause_subsumption:       235
% 2.57/0.98  res_orphan_elimination:                 0
% 2.57/0.98  res_tautology_del:                      75
% 2.57/0.98  res_num_eq_res_simplified:              0
% 2.57/0.98  res_num_sel_changes:                    0
% 2.57/0.98  res_moves_from_active_to_pass:          0
% 2.57/0.98  
% 2.57/0.98  ------ Superposition
% 2.57/0.98  
% 2.57/0.98  sup_time_total:                         0.
% 2.57/0.98  sup_time_generating:                    0.
% 2.57/0.98  sup_time_sim_full:                      0.
% 2.57/0.98  sup_time_sim_immed:                     0.
% 2.57/0.98  
% 2.57/0.98  sup_num_of_clauses:                     106
% 2.57/0.98  sup_num_in_active:                      18
% 2.57/0.98  sup_num_in_passive:                     88
% 2.57/0.98  sup_num_of_loops:                       27
% 2.57/0.98  sup_fw_superposition:                   158
% 2.57/0.98  sup_bw_superposition:                   159
% 2.57/0.98  sup_immediate_simplified:               131
% 2.57/0.98  sup_given_eliminated:                   0
% 2.57/0.98  comparisons_done:                       0
% 2.57/0.98  comparisons_avoided:                    0
% 2.57/0.98  
% 2.57/0.98  ------ Simplifications
% 2.57/0.98  
% 2.57/0.98  
% 2.57/0.98  sim_fw_subset_subsumed:                 0
% 2.57/0.98  sim_bw_subset_subsumed:                 0
% 2.57/0.98  sim_fw_subsumed:                        10
% 2.57/0.98  sim_bw_subsumed:                        0
% 2.57/0.98  sim_fw_subsumption_res:                 0
% 2.57/0.98  sim_bw_subsumption_res:                 0
% 2.57/0.98  sim_tautology_del:                      0
% 2.57/0.98  sim_eq_tautology_del:                   80
% 2.57/0.98  sim_eq_res_simp:                        0
% 2.57/0.98  sim_fw_demodulated:                     115
% 2.57/0.98  sim_bw_demodulated:                     15
% 2.57/0.98  sim_light_normalised:                   41
% 2.57/0.98  sim_joinable_taut:                      0
% 2.57/0.98  sim_joinable_simp:                      0
% 2.57/0.98  sim_ac_normalised:                      0
% 2.57/0.98  sim_smt_subsumption:                    0
% 2.57/0.98  
%------------------------------------------------------------------------------
