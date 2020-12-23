%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:11 EST 2020

% Result     : Theorem 15.18s
% Output     : CNFRefutation 15.18s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 124 expanded)
%              Number of clauses        :   28 (  52 expanded)
%              Number of leaves         :    6 (  25 expanded)
%              Depth                    :   14
%              Number of atoms          :   92 ( 257 expanded)
%              Number of equality atoms :   41 (  86 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))
      & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f11,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f10])).

fof(f12,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f12])).

fof(f21,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f13])).

fof(f19,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_4,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_367,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k2_xboole_0(X2,X0),X1) ),
    inference(superposition,[status(thm)],[c_4,c_0])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_158,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_797,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(k2_xboole_0(X1,X3),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_367,c_158])).

cnf(c_3,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_360,plain,
    ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k2_xboole_0(X2,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_3])).

cnf(c_795,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,k2_xboole_0(X2,X3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_360,c_158])).

cnf(c_796,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,k2_xboole_0(X3,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_158])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f16])).

cnf(c_157,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_5,negated_conjecture,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_156,plain,
    ( r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_544,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_157,c_156])).

cnf(c_16035,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),sK5)) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_796,c_544])).

cnf(c_29078,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),sK5)) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_16035])).

cnf(c_6,negated_conjecture,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_9,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_798,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(X0,k2_zfmisc_1(k2_xboole_0(X3,X1),X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_158])).

cnf(c_16286,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(sK3,sK5))) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_798,c_544])).

cnf(c_29077,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(sK3,sK5))) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_16286])).

cnf(c_34067,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) != iProver_top
    | r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_796,c_29077])).

cnf(c_34071,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29078,c_9,c_34067])).

cnf(c_34363,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_797,c_34071])).

cnf(c_7,negated_conjecture,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_8,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_34363,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 15.18/2.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.18/2.49  
% 15.18/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.18/2.49  
% 15.18/2.49  ------  iProver source info
% 15.18/2.49  
% 15.18/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.18/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.18/2.49  git: non_committed_changes: false
% 15.18/2.49  git: last_make_outside_of_git: false
% 15.18/2.49  
% 15.18/2.49  ------ 
% 15.18/2.49  
% 15.18/2.49  ------ Input Options
% 15.18/2.49  
% 15.18/2.49  --out_options                           all
% 15.18/2.49  --tptp_safe_out                         true
% 15.18/2.49  --problem_path                          ""
% 15.18/2.49  --include_path                          ""
% 15.18/2.49  --clausifier                            res/vclausify_rel
% 15.18/2.49  --clausifier_options                    ""
% 15.18/2.49  --stdin                                 false
% 15.18/2.49  --stats_out                             all
% 15.18/2.49  
% 15.18/2.49  ------ General Options
% 15.18/2.49  
% 15.18/2.49  --fof                                   false
% 15.18/2.49  --time_out_real                         305.
% 15.18/2.49  --time_out_virtual                      -1.
% 15.18/2.49  --symbol_type_check                     false
% 15.18/2.49  --clausify_out                          false
% 15.18/2.49  --sig_cnt_out                           false
% 15.18/2.49  --trig_cnt_out                          false
% 15.18/2.49  --trig_cnt_out_tolerance                1.
% 15.18/2.49  --trig_cnt_out_sk_spl                   false
% 15.18/2.49  --abstr_cl_out                          false
% 15.18/2.49  
% 15.18/2.49  ------ Global Options
% 15.18/2.49  
% 15.18/2.49  --schedule                              default
% 15.18/2.49  --add_important_lit                     false
% 15.18/2.49  --prop_solver_per_cl                    1000
% 15.18/2.49  --min_unsat_core                        false
% 15.18/2.49  --soft_assumptions                      false
% 15.18/2.49  --soft_lemma_size                       3
% 15.18/2.49  --prop_impl_unit_size                   0
% 15.18/2.49  --prop_impl_unit                        []
% 15.18/2.49  --share_sel_clauses                     true
% 15.18/2.49  --reset_solvers                         false
% 15.18/2.49  --bc_imp_inh                            [conj_cone]
% 15.18/2.49  --conj_cone_tolerance                   3.
% 15.18/2.49  --extra_neg_conj                        none
% 15.18/2.49  --large_theory_mode                     true
% 15.18/2.49  --prolific_symb_bound                   200
% 15.18/2.49  --lt_threshold                          2000
% 15.18/2.49  --clause_weak_htbl                      true
% 15.18/2.49  --gc_record_bc_elim                     false
% 15.18/2.49  
% 15.18/2.49  ------ Preprocessing Options
% 15.18/2.49  
% 15.18/2.49  --preprocessing_flag                    true
% 15.18/2.49  --time_out_prep_mult                    0.1
% 15.18/2.49  --splitting_mode                        input
% 15.18/2.49  --splitting_grd                         true
% 15.18/2.49  --splitting_cvd                         false
% 15.18/2.49  --splitting_cvd_svl                     false
% 15.18/2.49  --splitting_nvd                         32
% 15.18/2.49  --sub_typing                            true
% 15.18/2.49  --prep_gs_sim                           true
% 15.18/2.49  --prep_unflatten                        true
% 15.18/2.49  --prep_res_sim                          true
% 15.18/2.49  --prep_upred                            true
% 15.18/2.49  --prep_sem_filter                       exhaustive
% 15.18/2.49  --prep_sem_filter_out                   false
% 15.18/2.49  --pred_elim                             true
% 15.18/2.49  --res_sim_input                         true
% 15.18/2.49  --eq_ax_congr_red                       true
% 15.18/2.49  --pure_diseq_elim                       true
% 15.18/2.49  --brand_transform                       false
% 15.18/2.49  --non_eq_to_eq                          false
% 15.18/2.49  --prep_def_merge                        true
% 15.18/2.49  --prep_def_merge_prop_impl              false
% 15.18/2.49  --prep_def_merge_mbd                    true
% 15.18/2.49  --prep_def_merge_tr_red                 false
% 15.18/2.49  --prep_def_merge_tr_cl                  false
% 15.18/2.49  --smt_preprocessing                     true
% 15.18/2.49  --smt_ac_axioms                         fast
% 15.18/2.49  --preprocessed_out                      false
% 15.18/2.49  --preprocessed_stats                    false
% 15.18/2.49  
% 15.18/2.49  ------ Abstraction refinement Options
% 15.18/2.49  
% 15.18/2.49  --abstr_ref                             []
% 15.18/2.49  --abstr_ref_prep                        false
% 15.18/2.49  --abstr_ref_until_sat                   false
% 15.18/2.49  --abstr_ref_sig_restrict                funpre
% 15.18/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.18/2.49  --abstr_ref_under                       []
% 15.18/2.49  
% 15.18/2.49  ------ SAT Options
% 15.18/2.49  
% 15.18/2.49  --sat_mode                              false
% 15.18/2.49  --sat_fm_restart_options                ""
% 15.18/2.49  --sat_gr_def                            false
% 15.18/2.49  --sat_epr_types                         true
% 15.18/2.49  --sat_non_cyclic_types                  false
% 15.18/2.49  --sat_finite_models                     false
% 15.18/2.49  --sat_fm_lemmas                         false
% 15.18/2.49  --sat_fm_prep                           false
% 15.18/2.49  --sat_fm_uc_incr                        true
% 15.18/2.49  --sat_out_model                         small
% 15.18/2.49  --sat_out_clauses                       false
% 15.18/2.49  
% 15.18/2.49  ------ QBF Options
% 15.18/2.49  
% 15.18/2.49  --qbf_mode                              false
% 15.18/2.49  --qbf_elim_univ                         false
% 15.18/2.49  --qbf_dom_inst                          none
% 15.18/2.49  --qbf_dom_pre_inst                      false
% 15.18/2.49  --qbf_sk_in                             false
% 15.18/2.49  --qbf_pred_elim                         true
% 15.18/2.49  --qbf_split                             512
% 15.18/2.49  
% 15.18/2.49  ------ BMC1 Options
% 15.18/2.49  
% 15.18/2.49  --bmc1_incremental                      false
% 15.18/2.49  --bmc1_axioms                           reachable_all
% 15.18/2.49  --bmc1_min_bound                        0
% 15.18/2.49  --bmc1_max_bound                        -1
% 15.18/2.49  --bmc1_max_bound_default                -1
% 15.18/2.49  --bmc1_symbol_reachability              true
% 15.18/2.49  --bmc1_property_lemmas                  false
% 15.18/2.49  --bmc1_k_induction                      false
% 15.18/2.49  --bmc1_non_equiv_states                 false
% 15.18/2.49  --bmc1_deadlock                         false
% 15.18/2.49  --bmc1_ucm                              false
% 15.18/2.49  --bmc1_add_unsat_core                   none
% 15.18/2.49  --bmc1_unsat_core_children              false
% 15.18/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.18/2.49  --bmc1_out_stat                         full
% 15.18/2.49  --bmc1_ground_init                      false
% 15.18/2.49  --bmc1_pre_inst_next_state              false
% 15.18/2.49  --bmc1_pre_inst_state                   false
% 15.18/2.49  --bmc1_pre_inst_reach_state             false
% 15.18/2.49  --bmc1_out_unsat_core                   false
% 15.18/2.49  --bmc1_aig_witness_out                  false
% 15.18/2.49  --bmc1_verbose                          false
% 15.18/2.49  --bmc1_dump_clauses_tptp                false
% 15.18/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.18/2.49  --bmc1_dump_file                        -
% 15.18/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.18/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.18/2.49  --bmc1_ucm_extend_mode                  1
% 15.18/2.49  --bmc1_ucm_init_mode                    2
% 15.18/2.49  --bmc1_ucm_cone_mode                    none
% 15.18/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.18/2.49  --bmc1_ucm_relax_model                  4
% 15.18/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.18/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.18/2.49  --bmc1_ucm_layered_model                none
% 15.18/2.49  --bmc1_ucm_max_lemma_size               10
% 15.18/2.49  
% 15.18/2.49  ------ AIG Options
% 15.18/2.49  
% 15.18/2.49  --aig_mode                              false
% 15.18/2.49  
% 15.18/2.49  ------ Instantiation Options
% 15.18/2.49  
% 15.18/2.49  --instantiation_flag                    true
% 15.18/2.49  --inst_sos_flag                         true
% 15.18/2.49  --inst_sos_phase                        true
% 15.18/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.18/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.18/2.49  --inst_lit_sel_side                     num_symb
% 15.18/2.49  --inst_solver_per_active                1400
% 15.18/2.49  --inst_solver_calls_frac                1.
% 15.18/2.49  --inst_passive_queue_type               priority_queues
% 15.18/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.18/2.49  --inst_passive_queues_freq              [25;2]
% 15.18/2.49  --inst_dismatching                      true
% 15.18/2.49  --inst_eager_unprocessed_to_passive     true
% 15.18/2.49  --inst_prop_sim_given                   true
% 15.18/2.49  --inst_prop_sim_new                     false
% 15.18/2.49  --inst_subs_new                         false
% 15.18/2.49  --inst_eq_res_simp                      false
% 15.18/2.49  --inst_subs_given                       false
% 15.18/2.49  --inst_orphan_elimination               true
% 15.18/2.49  --inst_learning_loop_flag               true
% 15.18/2.49  --inst_learning_start                   3000
% 15.18/2.49  --inst_learning_factor                  2
% 15.18/2.49  --inst_start_prop_sim_after_learn       3
% 15.18/2.49  --inst_sel_renew                        solver
% 15.18/2.49  --inst_lit_activity_flag                true
% 15.18/2.49  --inst_restr_to_given                   false
% 15.18/2.49  --inst_activity_threshold               500
% 15.18/2.49  --inst_out_proof                        true
% 15.18/2.49  
% 15.18/2.49  ------ Resolution Options
% 15.18/2.49  
% 15.18/2.49  --resolution_flag                       true
% 15.18/2.49  --res_lit_sel                           adaptive
% 15.18/2.49  --res_lit_sel_side                      none
% 15.18/2.49  --res_ordering                          kbo
% 15.18/2.49  --res_to_prop_solver                    active
% 15.18/2.49  --res_prop_simpl_new                    false
% 15.18/2.49  --res_prop_simpl_given                  true
% 15.18/2.49  --res_passive_queue_type                priority_queues
% 15.18/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.18/2.49  --res_passive_queues_freq               [15;5]
% 15.18/2.49  --res_forward_subs                      full
% 15.18/2.49  --res_backward_subs                     full
% 15.18/2.49  --res_forward_subs_resolution           true
% 15.18/2.49  --res_backward_subs_resolution          true
% 15.18/2.49  --res_orphan_elimination                true
% 15.18/2.49  --res_time_limit                        2.
% 15.18/2.49  --res_out_proof                         true
% 15.18/2.49  
% 15.18/2.49  ------ Superposition Options
% 15.18/2.49  
% 15.18/2.49  --superposition_flag                    true
% 15.18/2.49  --sup_passive_queue_type                priority_queues
% 15.18/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.18/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.18/2.49  --demod_completeness_check              fast
% 15.18/2.49  --demod_use_ground                      true
% 15.18/2.49  --sup_to_prop_solver                    passive
% 15.18/2.49  --sup_prop_simpl_new                    true
% 15.18/2.49  --sup_prop_simpl_given                  true
% 15.18/2.49  --sup_fun_splitting                     true
% 15.18/2.49  --sup_smt_interval                      50000
% 15.18/2.49  
% 15.18/2.49  ------ Superposition Simplification Setup
% 15.18/2.49  
% 15.18/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.18/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.18/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.18/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.18/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.18/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.18/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.18/2.49  --sup_immed_triv                        [TrivRules]
% 15.18/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.18/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.18/2.49  --sup_immed_bw_main                     []
% 15.18/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.18/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.18/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.18/2.49  --sup_input_bw                          []
% 15.18/2.49  
% 15.18/2.49  ------ Combination Options
% 15.18/2.49  
% 15.18/2.49  --comb_res_mult                         3
% 15.18/2.49  --comb_sup_mult                         2
% 15.18/2.49  --comb_inst_mult                        10
% 15.18/2.49  
% 15.18/2.49  ------ Debug Options
% 15.18/2.49  
% 15.18/2.49  --dbg_backtrace                         false
% 15.18/2.49  --dbg_dump_prop_clauses                 false
% 15.18/2.49  --dbg_dump_prop_clauses_file            -
% 15.18/2.49  --dbg_out_stat                          false
% 15.18/2.49  ------ Parsing...
% 15.18/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.18/2.49  
% 15.18/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.18/2.49  
% 15.18/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.18/2.49  
% 15.18/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.18/2.49  ------ Proving...
% 15.18/2.49  ------ Problem Properties 
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  clauses                                 8
% 15.18/2.49  conjectures                             3
% 15.18/2.49  EPR                                     0
% 15.18/2.49  Horn                                    8
% 15.18/2.49  unary                                   6
% 15.18/2.49  binary                                  1
% 15.18/2.49  lits                                    11
% 15.18/2.49  lits eq                                 3
% 15.18/2.49  fd_pure                                 0
% 15.18/2.49  fd_pseudo                               0
% 15.18/2.49  fd_cond                                 0
% 15.18/2.49  fd_pseudo_cond                          0
% 15.18/2.49  AC symbols                              0
% 15.18/2.49  
% 15.18/2.49  ------ Schedule dynamic 5 is on 
% 15.18/2.49  
% 15.18/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  ------ 
% 15.18/2.49  Current options:
% 15.18/2.49  ------ 
% 15.18/2.49  
% 15.18/2.49  ------ Input Options
% 15.18/2.49  
% 15.18/2.49  --out_options                           all
% 15.18/2.49  --tptp_safe_out                         true
% 15.18/2.49  --problem_path                          ""
% 15.18/2.49  --include_path                          ""
% 15.18/2.49  --clausifier                            res/vclausify_rel
% 15.18/2.49  --clausifier_options                    ""
% 15.18/2.49  --stdin                                 false
% 15.18/2.49  --stats_out                             all
% 15.18/2.49  
% 15.18/2.49  ------ General Options
% 15.18/2.49  
% 15.18/2.49  --fof                                   false
% 15.18/2.49  --time_out_real                         305.
% 15.18/2.49  --time_out_virtual                      -1.
% 15.18/2.49  --symbol_type_check                     false
% 15.18/2.49  --clausify_out                          false
% 15.18/2.49  --sig_cnt_out                           false
% 15.18/2.49  --trig_cnt_out                          false
% 15.18/2.49  --trig_cnt_out_tolerance                1.
% 15.18/2.49  --trig_cnt_out_sk_spl                   false
% 15.18/2.49  --abstr_cl_out                          false
% 15.18/2.49  
% 15.18/2.49  ------ Global Options
% 15.18/2.49  
% 15.18/2.49  --schedule                              default
% 15.18/2.49  --add_important_lit                     false
% 15.18/2.49  --prop_solver_per_cl                    1000
% 15.18/2.49  --min_unsat_core                        false
% 15.18/2.49  --soft_assumptions                      false
% 15.18/2.49  --soft_lemma_size                       3
% 15.18/2.49  --prop_impl_unit_size                   0
% 15.18/2.49  --prop_impl_unit                        []
% 15.18/2.49  --share_sel_clauses                     true
% 15.18/2.49  --reset_solvers                         false
% 15.18/2.49  --bc_imp_inh                            [conj_cone]
% 15.18/2.49  --conj_cone_tolerance                   3.
% 15.18/2.49  --extra_neg_conj                        none
% 15.18/2.49  --large_theory_mode                     true
% 15.18/2.49  --prolific_symb_bound                   200
% 15.18/2.49  --lt_threshold                          2000
% 15.18/2.49  --clause_weak_htbl                      true
% 15.18/2.49  --gc_record_bc_elim                     false
% 15.18/2.49  
% 15.18/2.49  ------ Preprocessing Options
% 15.18/2.49  
% 15.18/2.49  --preprocessing_flag                    true
% 15.18/2.49  --time_out_prep_mult                    0.1
% 15.18/2.49  --splitting_mode                        input
% 15.18/2.49  --splitting_grd                         true
% 15.18/2.49  --splitting_cvd                         false
% 15.18/2.49  --splitting_cvd_svl                     false
% 15.18/2.49  --splitting_nvd                         32
% 15.18/2.49  --sub_typing                            true
% 15.18/2.49  --prep_gs_sim                           true
% 15.18/2.49  --prep_unflatten                        true
% 15.18/2.49  --prep_res_sim                          true
% 15.18/2.49  --prep_upred                            true
% 15.18/2.49  --prep_sem_filter                       exhaustive
% 15.18/2.49  --prep_sem_filter_out                   false
% 15.18/2.49  --pred_elim                             true
% 15.18/2.49  --res_sim_input                         true
% 15.18/2.49  --eq_ax_congr_red                       true
% 15.18/2.49  --pure_diseq_elim                       true
% 15.18/2.49  --brand_transform                       false
% 15.18/2.49  --non_eq_to_eq                          false
% 15.18/2.49  --prep_def_merge                        true
% 15.18/2.49  --prep_def_merge_prop_impl              false
% 15.18/2.49  --prep_def_merge_mbd                    true
% 15.18/2.49  --prep_def_merge_tr_red                 false
% 15.18/2.49  --prep_def_merge_tr_cl                  false
% 15.18/2.49  --smt_preprocessing                     true
% 15.18/2.49  --smt_ac_axioms                         fast
% 15.18/2.49  --preprocessed_out                      false
% 15.18/2.49  --preprocessed_stats                    false
% 15.18/2.49  
% 15.18/2.49  ------ Abstraction refinement Options
% 15.18/2.49  
% 15.18/2.49  --abstr_ref                             []
% 15.18/2.49  --abstr_ref_prep                        false
% 15.18/2.49  --abstr_ref_until_sat                   false
% 15.18/2.49  --abstr_ref_sig_restrict                funpre
% 15.18/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.18/2.49  --abstr_ref_under                       []
% 15.18/2.49  
% 15.18/2.49  ------ SAT Options
% 15.18/2.49  
% 15.18/2.49  --sat_mode                              false
% 15.18/2.49  --sat_fm_restart_options                ""
% 15.18/2.49  --sat_gr_def                            false
% 15.18/2.49  --sat_epr_types                         true
% 15.18/2.49  --sat_non_cyclic_types                  false
% 15.18/2.49  --sat_finite_models                     false
% 15.18/2.49  --sat_fm_lemmas                         false
% 15.18/2.49  --sat_fm_prep                           false
% 15.18/2.49  --sat_fm_uc_incr                        true
% 15.18/2.49  --sat_out_model                         small
% 15.18/2.49  --sat_out_clauses                       false
% 15.18/2.49  
% 15.18/2.49  ------ QBF Options
% 15.18/2.49  
% 15.18/2.49  --qbf_mode                              false
% 15.18/2.49  --qbf_elim_univ                         false
% 15.18/2.49  --qbf_dom_inst                          none
% 15.18/2.49  --qbf_dom_pre_inst                      false
% 15.18/2.49  --qbf_sk_in                             false
% 15.18/2.49  --qbf_pred_elim                         true
% 15.18/2.49  --qbf_split                             512
% 15.18/2.49  
% 15.18/2.49  ------ BMC1 Options
% 15.18/2.49  
% 15.18/2.49  --bmc1_incremental                      false
% 15.18/2.49  --bmc1_axioms                           reachable_all
% 15.18/2.49  --bmc1_min_bound                        0
% 15.18/2.49  --bmc1_max_bound                        -1
% 15.18/2.49  --bmc1_max_bound_default                -1
% 15.18/2.49  --bmc1_symbol_reachability              true
% 15.18/2.49  --bmc1_property_lemmas                  false
% 15.18/2.49  --bmc1_k_induction                      false
% 15.18/2.49  --bmc1_non_equiv_states                 false
% 15.18/2.49  --bmc1_deadlock                         false
% 15.18/2.49  --bmc1_ucm                              false
% 15.18/2.49  --bmc1_add_unsat_core                   none
% 15.18/2.49  --bmc1_unsat_core_children              false
% 15.18/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.18/2.49  --bmc1_out_stat                         full
% 15.18/2.49  --bmc1_ground_init                      false
% 15.18/2.49  --bmc1_pre_inst_next_state              false
% 15.18/2.49  --bmc1_pre_inst_state                   false
% 15.18/2.49  --bmc1_pre_inst_reach_state             false
% 15.18/2.49  --bmc1_out_unsat_core                   false
% 15.18/2.49  --bmc1_aig_witness_out                  false
% 15.18/2.49  --bmc1_verbose                          false
% 15.18/2.49  --bmc1_dump_clauses_tptp                false
% 15.18/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.18/2.49  --bmc1_dump_file                        -
% 15.18/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.18/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.18/2.49  --bmc1_ucm_extend_mode                  1
% 15.18/2.49  --bmc1_ucm_init_mode                    2
% 15.18/2.49  --bmc1_ucm_cone_mode                    none
% 15.18/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.18/2.49  --bmc1_ucm_relax_model                  4
% 15.18/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.18/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.18/2.49  --bmc1_ucm_layered_model                none
% 15.18/2.49  --bmc1_ucm_max_lemma_size               10
% 15.18/2.49  
% 15.18/2.49  ------ AIG Options
% 15.18/2.49  
% 15.18/2.49  --aig_mode                              false
% 15.18/2.49  
% 15.18/2.49  ------ Instantiation Options
% 15.18/2.49  
% 15.18/2.49  --instantiation_flag                    true
% 15.18/2.49  --inst_sos_flag                         true
% 15.18/2.49  --inst_sos_phase                        true
% 15.18/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.18/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.18/2.49  --inst_lit_sel_side                     none
% 15.18/2.49  --inst_solver_per_active                1400
% 15.18/2.49  --inst_solver_calls_frac                1.
% 15.18/2.49  --inst_passive_queue_type               priority_queues
% 15.18/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.18/2.49  --inst_passive_queues_freq              [25;2]
% 15.18/2.49  --inst_dismatching                      true
% 15.18/2.49  --inst_eager_unprocessed_to_passive     true
% 15.18/2.49  --inst_prop_sim_given                   true
% 15.18/2.49  --inst_prop_sim_new                     false
% 15.18/2.49  --inst_subs_new                         false
% 15.18/2.49  --inst_eq_res_simp                      false
% 15.18/2.49  --inst_subs_given                       false
% 15.18/2.49  --inst_orphan_elimination               true
% 15.18/2.49  --inst_learning_loop_flag               true
% 15.18/2.49  --inst_learning_start                   3000
% 15.18/2.49  --inst_learning_factor                  2
% 15.18/2.49  --inst_start_prop_sim_after_learn       3
% 15.18/2.49  --inst_sel_renew                        solver
% 15.18/2.49  --inst_lit_activity_flag                true
% 15.18/2.49  --inst_restr_to_given                   false
% 15.18/2.49  --inst_activity_threshold               500
% 15.18/2.49  --inst_out_proof                        true
% 15.18/2.49  
% 15.18/2.49  ------ Resolution Options
% 15.18/2.49  
% 15.18/2.49  --resolution_flag                       false
% 15.18/2.49  --res_lit_sel                           adaptive
% 15.18/2.49  --res_lit_sel_side                      none
% 15.18/2.49  --res_ordering                          kbo
% 15.18/2.49  --res_to_prop_solver                    active
% 15.18/2.49  --res_prop_simpl_new                    false
% 15.18/2.49  --res_prop_simpl_given                  true
% 15.18/2.49  --res_passive_queue_type                priority_queues
% 15.18/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.18/2.49  --res_passive_queues_freq               [15;5]
% 15.18/2.49  --res_forward_subs                      full
% 15.18/2.49  --res_backward_subs                     full
% 15.18/2.49  --res_forward_subs_resolution           true
% 15.18/2.49  --res_backward_subs_resolution          true
% 15.18/2.49  --res_orphan_elimination                true
% 15.18/2.49  --res_time_limit                        2.
% 15.18/2.49  --res_out_proof                         true
% 15.18/2.49  
% 15.18/2.49  ------ Superposition Options
% 15.18/2.49  
% 15.18/2.49  --superposition_flag                    true
% 15.18/2.49  --sup_passive_queue_type                priority_queues
% 15.18/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.18/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.18/2.49  --demod_completeness_check              fast
% 15.18/2.49  --demod_use_ground                      true
% 15.18/2.49  --sup_to_prop_solver                    passive
% 15.18/2.49  --sup_prop_simpl_new                    true
% 15.18/2.49  --sup_prop_simpl_given                  true
% 15.18/2.49  --sup_fun_splitting                     true
% 15.18/2.49  --sup_smt_interval                      50000
% 15.18/2.49  
% 15.18/2.49  ------ Superposition Simplification Setup
% 15.18/2.49  
% 15.18/2.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.18/2.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.18/2.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.18/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.18/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.18/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.18/2.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.18/2.49  --sup_immed_triv                        [TrivRules]
% 15.18/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.18/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.18/2.49  --sup_immed_bw_main                     []
% 15.18/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.18/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.18/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.18/2.49  --sup_input_bw                          []
% 15.18/2.49  
% 15.18/2.49  ------ Combination Options
% 15.18/2.49  
% 15.18/2.49  --comb_res_mult                         3
% 15.18/2.49  --comb_sup_mult                         2
% 15.18/2.49  --comb_inst_mult                        10
% 15.18/2.49  
% 15.18/2.49  ------ Debug Options
% 15.18/2.49  
% 15.18/2.49  --dbg_backtrace                         false
% 15.18/2.49  --dbg_dump_prop_clauses                 false
% 15.18/2.49  --dbg_dump_prop_clauses_file            -
% 15.18/2.49  --dbg_out_stat                          false
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  ------ Proving...
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  % SZS status Theorem for theBenchmark.p
% 15.18/2.49  
% 15.18/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.18/2.49  
% 15.18/2.49  fof(f4,axiom,(
% 15.18/2.49    ! [X0,X1,X2] : (k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) & k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2))),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f17,plain,(
% 15.18/2.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) = k2_zfmisc_1(k2_xboole_0(X0,X1),X2)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f4])).
% 15.18/2.49  
% 15.18/2.49  fof(f1,axiom,(
% 15.18/2.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f14,plain,(
% 15.18/2.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f1])).
% 15.18/2.49  
% 15.18/2.49  fof(f2,axiom,(
% 15.18/2.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f7,plain,(
% 15.18/2.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 15.18/2.49    inference(ennf_transformation,[],[f2])).
% 15.18/2.49  
% 15.18/2.49  fof(f15,plain,(
% 15.18/2.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f7])).
% 15.18/2.49  
% 15.18/2.49  fof(f18,plain,(
% 15.18/2.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(X2,k2_xboole_0(X0,X1))) )),
% 15.18/2.49    inference(cnf_transformation,[],[f4])).
% 15.18/2.49  
% 15.18/2.49  fof(f3,axiom,(
% 15.18/2.49    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f8,plain,(
% 15.18/2.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 15.18/2.49    inference(ennf_transformation,[],[f3])).
% 15.18/2.49  
% 15.18/2.49  fof(f9,plain,(
% 15.18/2.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 15.18/2.49    inference(flattening,[],[f8])).
% 15.18/2.49  
% 15.18/2.49  fof(f16,plain,(
% 15.18/2.49    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 15.18/2.49    inference(cnf_transformation,[],[f9])).
% 15.18/2.49  
% 15.18/2.49  fof(f5,conjecture,(
% 15.18/2.49    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 15.18/2.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.18/2.49  
% 15.18/2.49  fof(f6,negated_conjecture,(
% 15.18/2.49    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 15.18/2.49    inference(negated_conjecture,[],[f5])).
% 15.18/2.49  
% 15.18/2.49  fof(f10,plain,(
% 15.18/2.49    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 15.18/2.49    inference(ennf_transformation,[],[f6])).
% 15.18/2.49  
% 15.18/2.49  fof(f11,plain,(
% 15.18/2.49    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 15.18/2.49    inference(flattening,[],[f10])).
% 15.18/2.49  
% 15.18/2.49  fof(f12,plain,(
% 15.18/2.49    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 15.18/2.49    introduced(choice_axiom,[])).
% 15.18/2.49  
% 15.18/2.49  fof(f13,plain,(
% 15.18/2.49    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 15.18/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f12])).
% 15.18/2.49  
% 15.18/2.49  fof(f21,plain,(
% 15.18/2.49    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 15.18/2.49    inference(cnf_transformation,[],[f13])).
% 15.18/2.49  
% 15.18/2.49  fof(f20,plain,(
% 15.18/2.49    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 15.18/2.49    inference(cnf_transformation,[],[f13])).
% 15.18/2.49  
% 15.18/2.49  fof(f19,plain,(
% 15.18/2.49    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 15.18/2.49    inference(cnf_transformation,[],[f13])).
% 15.18/2.49  
% 15.18/2.49  cnf(c_4,plain,
% 15.18/2.49      ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k2_xboole_0(X0,X2),X1) ),
% 15.18/2.49      inference(cnf_transformation,[],[f17]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_0,plain,
% 15.18/2.49      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 15.18/2.49      inference(cnf_transformation,[],[f14]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_367,plain,
% 15.18/2.49      ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X1)) = k2_zfmisc_1(k2_xboole_0(X2,X0),X1) ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_4,c_0]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_1,plain,
% 15.18/2.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 15.18/2.49      inference(cnf_transformation,[],[f15]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_158,plain,
% 15.18/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.18/2.49      | r1_tarski(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_797,plain,
% 15.18/2.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 15.18/2.49      | r1_tarski(X0,k2_zfmisc_1(k2_xboole_0(X1,X3),X2)) = iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_367,c_158]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_3,plain,
% 15.18/2.49      ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k2_xboole_0(X1,X2)) ),
% 15.18/2.49      inference(cnf_transformation,[],[f18]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_360,plain,
% 15.18/2.49      ( k2_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k2_xboole_0(X2,X1)) ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_0,c_3]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_795,plain,
% 15.18/2.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 15.18/2.49      | r1_tarski(X0,k2_zfmisc_1(X1,k2_xboole_0(X2,X3))) = iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_360,c_158]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_796,plain,
% 15.18/2.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 15.18/2.49      | r1_tarski(X0,k2_zfmisc_1(X1,k2_xboole_0(X3,X2))) = iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_3,c_158]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_2,plain,
% 15.18/2.49      ( ~ r1_tarski(X0,X1)
% 15.18/2.49      | ~ r1_tarski(X2,X1)
% 15.18/2.49      | r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 15.18/2.49      inference(cnf_transformation,[],[f16]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_157,plain,
% 15.18/2.49      ( r1_tarski(X0,X1) != iProver_top
% 15.18/2.49      | r1_tarski(X2,X1) != iProver_top
% 15.18/2.49      | r1_tarski(k2_xboole_0(X0,X2),X1) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_5,negated_conjecture,
% 15.18/2.49      ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
% 15.18/2.49      inference(cnf_transformation,[],[f21]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_156,plain,
% 15.18/2.49      ( r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) != iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_544,plain,
% 15.18/2.49      ( r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) != iProver_top
% 15.18/2.49      | r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_157,c_156]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_16035,plain,
% 15.18/2.49      ( r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),sK5)) != iProver_top
% 15.18/2.49      | r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_796,c_544]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_29078,plain,
% 15.18/2.49      ( r1_tarski(sK1,k2_zfmisc_1(k2_xboole_0(sK2,sK4),sK5)) != iProver_top
% 15.18/2.49      | r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),sK3)) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_795,c_16035]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_6,negated_conjecture,
% 15.18/2.49      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
% 15.18/2.49      inference(cnf_transformation,[],[f20]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_9,plain,
% 15.18/2.49      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_798,plain,
% 15.18/2.49      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 15.18/2.49      | r1_tarski(X0,k2_zfmisc_1(k2_xboole_0(X3,X1),X2)) = iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_4,c_158]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_16286,plain,
% 15.18/2.49      ( r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(sK3,sK5))) != iProver_top
% 15.18/2.49      | r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_798,c_544]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_29077,plain,
% 15.18/2.49      ( r1_tarski(sK1,k2_zfmisc_1(sK4,k2_xboole_0(sK3,sK5))) != iProver_top
% 15.18/2.49      | r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),sK3)) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_795,c_16286]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_34067,plain,
% 15.18/2.49      ( r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) != iProver_top
% 15.18/2.49      | r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),sK3)) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_796,c_29077]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_34071,plain,
% 15.18/2.49      ( r1_tarski(sK0,k2_zfmisc_1(k2_xboole_0(sK2,sK4),sK3)) != iProver_top ),
% 15.18/2.49      inference(global_propositional_subsumption,
% 15.18/2.49                [status(thm)],
% 15.18/2.49                [c_29078,c_9,c_34067]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_34363,plain,
% 15.18/2.49      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) != iProver_top ),
% 15.18/2.49      inference(superposition,[status(thm)],[c_797,c_34071]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_7,negated_conjecture,
% 15.18/2.49      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
% 15.18/2.49      inference(cnf_transformation,[],[f19]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(c_8,plain,
% 15.18/2.49      ( r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 15.18/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.18/2.49  
% 15.18/2.49  cnf(contradiction,plain,
% 15.18/2.49      ( $false ),
% 15.18/2.49      inference(minisat,[status(thm)],[c_34363,c_8]) ).
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  % SZS output end CNFRefutation for theBenchmark.p
% 15.18/2.49  
% 15.18/2.49  ------                               Statistics
% 15.18/2.49  
% 15.18/2.49  ------ General
% 15.18/2.49  
% 15.18/2.49  abstr_ref_over_cycles:                  0
% 15.18/2.49  abstr_ref_under_cycles:                 0
% 15.18/2.49  gc_basic_clause_elim:                   0
% 15.18/2.49  forced_gc_time:                         0
% 15.18/2.49  parsing_time:                           0.008
% 15.18/2.49  unif_index_cands_time:                  0.
% 15.18/2.49  unif_index_add_time:                    0.
% 15.18/2.49  orderings_time:                         0.
% 15.18/2.49  out_proof_time:                         0.008
% 15.18/2.49  total_time:                             1.618
% 15.18/2.49  num_of_symbols:                         40
% 15.18/2.49  num_of_terms:                           68404
% 15.18/2.49  
% 15.18/2.49  ------ Preprocessing
% 15.18/2.49  
% 15.18/2.49  num_of_splits:                          0
% 15.18/2.49  num_of_split_atoms:                     0
% 15.18/2.49  num_of_reused_defs:                     0
% 15.18/2.49  num_eq_ax_congr_red:                    0
% 15.18/2.49  num_of_sem_filtered_clauses:            1
% 15.18/2.49  num_of_subtypes:                        1
% 15.18/2.49  monotx_restored_types:                  0
% 15.18/2.49  sat_num_of_epr_types:                   0
% 15.18/2.49  sat_num_of_non_cyclic_types:            0
% 15.18/2.49  sat_guarded_non_collapsed_types:        0
% 15.18/2.49  num_pure_diseq_elim:                    0
% 15.18/2.49  simp_replaced_by:                       0
% 15.18/2.49  res_preprocessed:                       35
% 15.18/2.49  prep_upred:                             0
% 15.18/2.49  prep_unflattend:                        0
% 15.18/2.49  smt_new_axioms:                         0
% 15.18/2.49  pred_elim_cands:                        1
% 15.18/2.49  pred_elim:                              0
% 15.18/2.49  pred_elim_cl:                           0
% 15.18/2.49  pred_elim_cycles:                       1
% 15.18/2.49  merged_defs:                            0
% 15.18/2.49  merged_defs_ncl:                        0
% 15.18/2.49  bin_hyper_res:                          0
% 15.18/2.49  prep_cycles:                            3
% 15.18/2.49  pred_elim_time:                         0.
% 15.18/2.49  splitting_time:                         0.
% 15.18/2.49  sem_filter_time:                        0.
% 15.18/2.49  monotx_time:                            0.
% 15.18/2.49  subtype_inf_time:                       0.
% 15.18/2.49  
% 15.18/2.49  ------ Problem properties
% 15.18/2.49  
% 15.18/2.49  clauses:                                8
% 15.18/2.49  conjectures:                            3
% 15.18/2.49  epr:                                    0
% 15.18/2.49  horn:                                   8
% 15.18/2.49  ground:                                 3
% 15.18/2.49  unary:                                  6
% 15.18/2.49  binary:                                 1
% 15.18/2.49  lits:                                   11
% 15.18/2.49  lits_eq:                                3
% 15.18/2.49  fd_pure:                                0
% 15.18/2.49  fd_pseudo:                              0
% 15.18/2.49  fd_cond:                                0
% 15.18/2.49  fd_pseudo_cond:                         0
% 15.18/2.49  ac_symbols:                             0
% 15.18/2.49  
% 15.18/2.49  ------ Propositional Solver
% 15.18/2.49  
% 15.18/2.49  prop_solver_calls:                      30
% 15.18/2.49  prop_fast_solver_calls:                 266
% 15.18/2.49  smt_solver_calls:                       0
% 15.18/2.49  smt_fast_solver_calls:                  0
% 15.18/2.49  prop_num_of_clauses:                    14737
% 15.18/2.49  prop_preprocess_simplified:             9282
% 15.18/2.49  prop_fo_subsumed:                       8
% 15.18/2.49  prop_solver_time:                       0.
% 15.18/2.49  smt_solver_time:                        0.
% 15.18/2.49  smt_fast_solver_time:                   0.
% 15.18/2.49  prop_fast_solver_time:                  0.
% 15.18/2.49  prop_unsat_core_time:                   0.001
% 15.18/2.49  
% 15.18/2.49  ------ QBF
% 15.18/2.49  
% 15.18/2.49  qbf_q_res:                              0
% 15.18/2.49  qbf_num_tautologies:                    0
% 15.18/2.49  qbf_prep_cycles:                        0
% 15.18/2.49  
% 15.18/2.49  ------ BMC1
% 15.18/2.49  
% 15.18/2.49  bmc1_current_bound:                     -1
% 15.18/2.49  bmc1_last_solved_bound:                 -1
% 15.18/2.49  bmc1_unsat_core_size:                   -1
% 15.18/2.49  bmc1_unsat_core_parents_size:           -1
% 15.18/2.49  bmc1_merge_next_fun:                    0
% 15.18/2.49  bmc1_unsat_core_clauses_time:           0.
% 15.18/2.49  
% 15.18/2.49  ------ Instantiation
% 15.18/2.49  
% 15.18/2.49  inst_num_of_clauses:                    1009
% 15.18/2.49  inst_num_in_passive:                    337
% 15.18/2.49  inst_num_in_active:                     496
% 15.18/2.49  inst_num_in_unprocessed:                176
% 15.18/2.49  inst_num_of_loops:                      530
% 15.18/2.49  inst_num_of_learning_restarts:          0
% 15.18/2.49  inst_num_moves_active_passive:          28
% 15.18/2.49  inst_lit_activity:                      0
% 15.18/2.49  inst_lit_activity_moves:                0
% 15.18/2.49  inst_num_tautologies:                   0
% 15.18/2.49  inst_num_prop_implied:                  0
% 15.18/2.49  inst_num_existing_simplified:           0
% 15.18/2.49  inst_num_eq_res_simplified:             0
% 15.18/2.49  inst_num_child_elim:                    0
% 15.18/2.49  inst_num_of_dismatching_blockings:      929
% 15.18/2.49  inst_num_of_non_proper_insts:           1323
% 15.18/2.49  inst_num_of_duplicates:                 0
% 15.18/2.49  inst_inst_num_from_inst_to_res:         0
% 15.18/2.49  inst_dismatching_checking_time:         0.
% 15.18/2.49  
% 15.18/2.49  ------ Resolution
% 15.18/2.49  
% 15.18/2.49  res_num_of_clauses:                     0
% 15.18/2.49  res_num_in_passive:                     0
% 15.18/2.49  res_num_in_active:                      0
% 15.18/2.49  res_num_of_loops:                       38
% 15.18/2.49  res_forward_subset_subsumed:            279
% 15.18/2.49  res_backward_subset_subsumed:           0
% 15.18/2.49  res_forward_subsumed:                   0
% 15.18/2.49  res_backward_subsumed:                  0
% 15.18/2.49  res_forward_subsumption_resolution:     0
% 15.18/2.49  res_backward_subsumption_resolution:    0
% 15.18/2.49  res_clause_to_clause_subsumption:       208103
% 15.18/2.49  res_orphan_elimination:                 0
% 15.18/2.49  res_tautology_del:                      157
% 15.18/2.49  res_num_eq_res_simplified:              0
% 15.18/2.49  res_num_sel_changes:                    0
% 15.18/2.49  res_moves_from_active_to_pass:          0
% 15.18/2.49  
% 15.18/2.49  ------ Superposition
% 15.18/2.49  
% 15.18/2.49  sup_time_total:                         0.
% 15.18/2.49  sup_time_generating:                    0.
% 15.18/2.49  sup_time_sim_full:                      0.
% 15.18/2.49  sup_time_sim_immed:                     0.
% 15.18/2.49  
% 15.18/2.49  sup_num_of_clauses:                     7276
% 15.18/2.49  sup_num_in_active:                      102
% 15.18/2.49  sup_num_in_passive:                     7174
% 15.18/2.49  sup_num_of_loops:                       105
% 15.18/2.49  sup_fw_superposition:                   10501
% 15.18/2.49  sup_bw_superposition:                   9615
% 15.18/2.49  sup_immediate_simplified:               2968
% 15.18/2.49  sup_given_eliminated:                   0
% 15.18/2.49  comparisons_done:                       0
% 15.18/2.49  comparisons_avoided:                    0
% 15.18/2.49  
% 15.18/2.49  ------ Simplifications
% 15.18/2.49  
% 15.18/2.49  
% 15.18/2.49  sim_fw_subset_subsumed:                 4
% 15.18/2.49  sim_bw_subset_subsumed:                 0
% 15.18/2.49  sim_fw_subsumed:                        667
% 15.18/2.49  sim_bw_subsumed:                        69
% 15.18/2.49  sim_fw_subsumption_res:                 0
% 15.18/2.49  sim_bw_subsumption_res:                 0
% 15.18/2.49  sim_tautology_del:                      0
% 15.18/2.49  sim_eq_tautology_del:                   277
% 15.18/2.49  sim_eq_res_simp:                        0
% 15.18/2.49  sim_fw_demodulated:                     2359
% 15.18/2.49  sim_bw_demodulated:                     21
% 15.18/2.49  sim_light_normalised:                   390
% 15.18/2.49  sim_joinable_taut:                      0
% 15.18/2.49  sim_joinable_simp:                      0
% 15.18/2.49  sim_ac_normalised:                      0
% 15.18/2.49  sim_smt_subsumption:                    0
% 15.18/2.49  
%------------------------------------------------------------------------------
