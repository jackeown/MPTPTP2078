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
% DateTime   : Thu Dec  3 12:08:25 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 176 expanded)
%              Number of clauses        :   27 (  50 expanded)
%              Number of leaves         :    6 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  159 (1056 expanded)
%              Number of equality atoms :   47 ( 258 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f68])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f36,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) )
         => ( v1_partfun1(X2,X0)
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f36])).

fof(f70,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f71,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f70])).

fof(f105,plain,
    ( ? [X0,X1,X2] :
        ( ~ v1_partfun1(X2,X0)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ~ v1_partfun1(sK15,sK13)
      & ( k1_xboole_0 = sK13
        | k1_xboole_0 != sK14 )
      & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
      & v1_funct_2(sK15,sK13,sK14)
      & v1_funct_1(sK15)
      & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
      & v1_funct_1(sK15) ) ),
    introduced(choice_axiom,[])).

fof(f106,plain,
    ( ~ v1_partfun1(sK15,sK13)
    & ( k1_xboole_0 = sK13
      | k1_xboole_0 != sK14 )
    & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
    & v1_funct_2(sK15,sK13,sK14)
    & v1_funct_1(sK15)
    & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
    & v1_funct_1(sK15) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f71,f105])).

fof(f192,plain,(
    v1_funct_2(sK15,sK13,sK14) ),
    inference(cnf_transformation,[],[f106])).

fof(f189,plain,(
    v1_funct_1(sK15) ),
    inference(cnf_transformation,[],[f106])).

fof(f190,plain,(
    m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) ),
    inference(cnf_transformation,[],[f106])).

fof(f195,plain,(
    ~ v1_partfun1(sK15,sK13) ),
    inference(cnf_transformation,[],[f106])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f112,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f194,plain,
    ( k1_xboole_0 = sK13
    | k1_xboole_0 != sK14 ),
    inference(cnf_transformation,[],[f106])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_78,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f186])).

cnf(c_85,negated_conjecture,
    ( v1_funct_2(sK15,sK13,sK14) ),
    inference(cnf_transformation,[],[f192])).

cnf(c_1010,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK14 != X2
    | sK13 != X1
    | sK15 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_78,c_85])).

cnf(c_1011,plain,
    ( v1_partfun1(sK15,sK13)
    | ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
    | ~ v1_funct_1(sK15)
    | v1_xboole_0(sK14) ),
    inference(unflattening,[status(thm)],[c_1010])).

cnf(c_88,negated_conjecture,
    ( v1_funct_1(sK15) ),
    inference(cnf_transformation,[],[f189])).

cnf(c_87,negated_conjecture,
    ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) ),
    inference(cnf_transformation,[],[f190])).

cnf(c_82,negated_conjecture,
    ( ~ v1_partfun1(sK15,sK13) ),
    inference(cnf_transformation,[],[f195])).

cnf(c_1013,plain,
    ( v1_xboole_0(sK14) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1011,c_88,c_87,c_82])).

cnf(c_4434,plain,
    ( v1_xboole_0(sK14) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1013])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_4500,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5611,plain,
    ( sK14 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4434,c_4500])).

cnf(c_83,negated_conjecture,
    ( k1_xboole_0 != sK14
    | k1_xboole_0 = sK13 ),
    inference(cnf_transformation,[],[f194])).

cnf(c_5743,plain,
    ( sK13 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5611,c_83])).

cnf(c_5744,plain,
    ( sK13 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5743])).

cnf(c_5741,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5611,c_4434])).

cnf(c_2920,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5116,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK13)
    | sK13 != X0 ),
    inference(instantiation,[status(thm)],[c_2920])).

cnf(c_5117,plain,
    ( sK13 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK13) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5116])).

cnf(c_5119,plain,
    ( sK13 != k1_xboole_0
    | v1_xboole_0(sK13) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5117])).

cnf(c_4437,plain,
    ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_87])).

cnf(c_77,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f184])).

cnf(c_1023,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | sK13 != X1
    | sK15 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_77,c_82])).

cnf(c_1024,plain,
    ( ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,X0)))
    | ~ v1_xboole_0(sK13) ),
    inference(unflattening,[status(thm)],[c_1023])).

cnf(c_4433,plain,
    ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,X0))) != iProver_top
    | v1_xboole_0(sK13) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1024])).

cnf(c_5048,plain,
    ( v1_xboole_0(sK13) != iProver_top ),
    inference(superposition,[status(thm)],[c_4437,c_4433])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5744,c_5741,c_5119,c_5048])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 21:02:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.07/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.00  
% 2.07/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.07/1.00  
% 2.07/1.00  ------  iProver source info
% 2.07/1.00  
% 2.07/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.07/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.07/1.00  git: non_committed_changes: false
% 2.07/1.00  git: last_make_outside_of_git: false
% 2.07/1.00  
% 2.07/1.00  ------ 
% 2.07/1.00  
% 2.07/1.00  ------ Input Options
% 2.07/1.00  
% 2.07/1.00  --out_options                           all
% 2.07/1.00  --tptp_safe_out                         true
% 2.07/1.00  --problem_path                          ""
% 2.07/1.00  --include_path                          ""
% 2.07/1.00  --clausifier                            res/vclausify_rel
% 2.07/1.00  --clausifier_options                    --mode clausify
% 2.07/1.00  --stdin                                 false
% 2.07/1.00  --stats_out                             all
% 2.07/1.00  
% 2.07/1.00  ------ General Options
% 2.07/1.00  
% 2.07/1.00  --fof                                   false
% 2.07/1.00  --time_out_real                         305.
% 2.07/1.00  --time_out_virtual                      -1.
% 2.07/1.00  --symbol_type_check                     false
% 2.07/1.00  --clausify_out                          false
% 2.07/1.00  --sig_cnt_out                           false
% 2.07/1.00  --trig_cnt_out                          false
% 2.07/1.00  --trig_cnt_out_tolerance                1.
% 2.07/1.00  --trig_cnt_out_sk_spl                   false
% 2.07/1.00  --abstr_cl_out                          false
% 2.07/1.00  
% 2.07/1.00  ------ Global Options
% 2.07/1.00  
% 2.07/1.00  --schedule                              default
% 2.07/1.00  --add_important_lit                     false
% 2.07/1.00  --prop_solver_per_cl                    1000
% 2.07/1.00  --min_unsat_core                        false
% 2.07/1.00  --soft_assumptions                      false
% 2.07/1.00  --soft_lemma_size                       3
% 2.07/1.00  --prop_impl_unit_size                   0
% 2.07/1.00  --prop_impl_unit                        []
% 2.07/1.00  --share_sel_clauses                     true
% 2.07/1.00  --reset_solvers                         false
% 2.07/1.00  --bc_imp_inh                            [conj_cone]
% 2.07/1.00  --conj_cone_tolerance                   3.
% 2.07/1.00  --extra_neg_conj                        none
% 2.07/1.00  --large_theory_mode                     true
% 2.07/1.00  --prolific_symb_bound                   200
% 2.07/1.00  --lt_threshold                          2000
% 2.07/1.00  --clause_weak_htbl                      true
% 2.07/1.00  --gc_record_bc_elim                     false
% 2.07/1.00  
% 2.07/1.00  ------ Preprocessing Options
% 2.07/1.00  
% 2.07/1.00  --preprocessing_flag                    true
% 2.07/1.00  --time_out_prep_mult                    0.1
% 2.07/1.00  --splitting_mode                        input
% 2.07/1.00  --splitting_grd                         true
% 2.07/1.00  --splitting_cvd                         false
% 2.07/1.00  --splitting_cvd_svl                     false
% 2.07/1.00  --splitting_nvd                         32
% 2.07/1.00  --sub_typing                            true
% 2.07/1.00  --prep_gs_sim                           true
% 2.07/1.00  --prep_unflatten                        true
% 2.07/1.00  --prep_res_sim                          true
% 2.07/1.00  --prep_upred                            true
% 2.07/1.00  --prep_sem_filter                       exhaustive
% 2.07/1.00  --prep_sem_filter_out                   false
% 2.07/1.00  --pred_elim                             true
% 2.07/1.00  --res_sim_input                         true
% 2.07/1.00  --eq_ax_congr_red                       true
% 2.07/1.00  --pure_diseq_elim                       true
% 2.07/1.00  --brand_transform                       false
% 2.07/1.00  --non_eq_to_eq                          false
% 2.07/1.00  --prep_def_merge                        true
% 2.07/1.00  --prep_def_merge_prop_impl              false
% 2.07/1.00  --prep_def_merge_mbd                    true
% 2.07/1.00  --prep_def_merge_tr_red                 false
% 2.07/1.00  --prep_def_merge_tr_cl                  false
% 2.07/1.00  --smt_preprocessing                     true
% 2.07/1.00  --smt_ac_axioms                         fast
% 2.07/1.00  --preprocessed_out                      false
% 2.07/1.00  --preprocessed_stats                    false
% 2.07/1.00  
% 2.07/1.00  ------ Abstraction refinement Options
% 2.07/1.00  
% 2.07/1.00  --abstr_ref                             []
% 2.07/1.00  --abstr_ref_prep                        false
% 2.07/1.00  --abstr_ref_until_sat                   false
% 2.07/1.00  --abstr_ref_sig_restrict                funpre
% 2.07/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.07/1.00  --abstr_ref_under                       []
% 2.07/1.00  
% 2.07/1.00  ------ SAT Options
% 2.07/1.00  
% 2.07/1.00  --sat_mode                              false
% 2.07/1.00  --sat_fm_restart_options                ""
% 2.07/1.00  --sat_gr_def                            false
% 2.07/1.00  --sat_epr_types                         true
% 2.07/1.00  --sat_non_cyclic_types                  false
% 2.07/1.00  --sat_finite_models                     false
% 2.07/1.00  --sat_fm_lemmas                         false
% 2.07/1.00  --sat_fm_prep                           false
% 2.07/1.00  --sat_fm_uc_incr                        true
% 2.07/1.00  --sat_out_model                         small
% 2.07/1.00  --sat_out_clauses                       false
% 2.07/1.00  
% 2.07/1.00  ------ QBF Options
% 2.07/1.00  
% 2.07/1.00  --qbf_mode                              false
% 2.07/1.00  --qbf_elim_univ                         false
% 2.07/1.00  --qbf_dom_inst                          none
% 2.07/1.00  --qbf_dom_pre_inst                      false
% 2.07/1.00  --qbf_sk_in                             false
% 2.07/1.00  --qbf_pred_elim                         true
% 2.07/1.00  --qbf_split                             512
% 2.07/1.00  
% 2.07/1.00  ------ BMC1 Options
% 2.07/1.00  
% 2.07/1.00  --bmc1_incremental                      false
% 2.07/1.00  --bmc1_axioms                           reachable_all
% 2.07/1.00  --bmc1_min_bound                        0
% 2.07/1.00  --bmc1_max_bound                        -1
% 2.07/1.00  --bmc1_max_bound_default                -1
% 2.07/1.00  --bmc1_symbol_reachability              true
% 2.07/1.00  --bmc1_property_lemmas                  false
% 2.07/1.00  --bmc1_k_induction                      false
% 2.07/1.00  --bmc1_non_equiv_states                 false
% 2.07/1.00  --bmc1_deadlock                         false
% 2.07/1.00  --bmc1_ucm                              false
% 2.07/1.00  --bmc1_add_unsat_core                   none
% 2.07/1.00  --bmc1_unsat_core_children              false
% 2.07/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.07/1.00  --bmc1_out_stat                         full
% 2.07/1.00  --bmc1_ground_init                      false
% 2.07/1.00  --bmc1_pre_inst_next_state              false
% 2.07/1.00  --bmc1_pre_inst_state                   false
% 2.07/1.00  --bmc1_pre_inst_reach_state             false
% 2.07/1.00  --bmc1_out_unsat_core                   false
% 2.07/1.00  --bmc1_aig_witness_out                  false
% 2.07/1.00  --bmc1_verbose                          false
% 2.07/1.00  --bmc1_dump_clauses_tptp                false
% 2.07/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.07/1.00  --bmc1_dump_file                        -
% 2.07/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.07/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.07/1.00  --bmc1_ucm_extend_mode                  1
% 2.07/1.00  --bmc1_ucm_init_mode                    2
% 2.07/1.00  --bmc1_ucm_cone_mode                    none
% 2.07/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.07/1.00  --bmc1_ucm_relax_model                  4
% 2.07/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.07/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.07/1.00  --bmc1_ucm_layered_model                none
% 2.07/1.00  --bmc1_ucm_max_lemma_size               10
% 2.07/1.00  
% 2.07/1.00  ------ AIG Options
% 2.07/1.00  
% 2.07/1.00  --aig_mode                              false
% 2.07/1.00  
% 2.07/1.00  ------ Instantiation Options
% 2.07/1.00  
% 2.07/1.00  --instantiation_flag                    true
% 2.07/1.00  --inst_sos_flag                         false
% 2.07/1.00  --inst_sos_phase                        true
% 2.07/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.07/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.07/1.00  --inst_lit_sel_side                     num_symb
% 2.07/1.00  --inst_solver_per_active                1400
% 2.07/1.00  --inst_solver_calls_frac                1.
% 2.07/1.00  --inst_passive_queue_type               priority_queues
% 2.07/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.07/1.00  --inst_passive_queues_freq              [25;2]
% 2.07/1.00  --inst_dismatching                      true
% 2.07/1.00  --inst_eager_unprocessed_to_passive     true
% 2.07/1.00  --inst_prop_sim_given                   true
% 2.07/1.00  --inst_prop_sim_new                     false
% 2.07/1.00  --inst_subs_new                         false
% 2.07/1.00  --inst_eq_res_simp                      false
% 2.07/1.00  --inst_subs_given                       false
% 2.07/1.00  --inst_orphan_elimination               true
% 2.07/1.00  --inst_learning_loop_flag               true
% 2.07/1.00  --inst_learning_start                   3000
% 2.07/1.00  --inst_learning_factor                  2
% 2.07/1.00  --inst_start_prop_sim_after_learn       3
% 2.07/1.00  --inst_sel_renew                        solver
% 2.07/1.00  --inst_lit_activity_flag                true
% 2.07/1.00  --inst_restr_to_given                   false
% 2.07/1.00  --inst_activity_threshold               500
% 2.07/1.00  --inst_out_proof                        true
% 2.07/1.00  
% 2.07/1.00  ------ Resolution Options
% 2.07/1.00  
% 2.07/1.00  --resolution_flag                       true
% 2.07/1.00  --res_lit_sel                           adaptive
% 2.07/1.00  --res_lit_sel_side                      none
% 2.07/1.00  --res_ordering                          kbo
% 2.07/1.00  --res_to_prop_solver                    active
% 2.07/1.00  --res_prop_simpl_new                    false
% 2.07/1.00  --res_prop_simpl_given                  true
% 2.07/1.00  --res_passive_queue_type                priority_queues
% 2.07/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.07/1.00  --res_passive_queues_freq               [15;5]
% 2.07/1.00  --res_forward_subs                      full
% 2.07/1.00  --res_backward_subs                     full
% 2.07/1.00  --res_forward_subs_resolution           true
% 2.07/1.00  --res_backward_subs_resolution          true
% 2.07/1.00  --res_orphan_elimination                true
% 2.07/1.00  --res_time_limit                        2.
% 2.07/1.00  --res_out_proof                         true
% 2.07/1.00  
% 2.07/1.00  ------ Superposition Options
% 2.07/1.00  
% 2.07/1.00  --superposition_flag                    true
% 2.07/1.00  --sup_passive_queue_type                priority_queues
% 2.07/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.07/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.07/1.00  --demod_completeness_check              fast
% 2.07/1.00  --demod_use_ground                      true
% 2.07/1.00  --sup_to_prop_solver                    passive
% 2.07/1.00  --sup_prop_simpl_new                    true
% 2.07/1.00  --sup_prop_simpl_given                  true
% 2.07/1.00  --sup_fun_splitting                     false
% 2.07/1.00  --sup_smt_interval                      50000
% 2.07/1.00  
% 2.07/1.00  ------ Superposition Simplification Setup
% 2.07/1.00  
% 2.07/1.00  --sup_indices_passive                   []
% 2.07/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.07/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/1.00  --sup_full_bw                           [BwDemod]
% 2.07/1.00  --sup_immed_triv                        [TrivRules]
% 2.07/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.07/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/1.00  --sup_immed_bw_main                     []
% 2.07/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.07/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/1.00  
% 2.07/1.00  ------ Combination Options
% 2.07/1.00  
% 2.07/1.00  --comb_res_mult                         3
% 2.07/1.00  --comb_sup_mult                         2
% 2.07/1.00  --comb_inst_mult                        10
% 2.07/1.00  
% 2.07/1.00  ------ Debug Options
% 2.07/1.00  
% 2.07/1.00  --dbg_backtrace                         false
% 2.07/1.00  --dbg_dump_prop_clauses                 false
% 2.07/1.00  --dbg_dump_prop_clauses_file            -
% 2.07/1.00  --dbg_out_stat                          false
% 2.07/1.00  ------ Parsing...
% 2.07/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.07/1.00  
% 2.07/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.07/1.00  
% 2.07/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.07/1.00  
% 2.07/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.07/1.00  ------ Proving...
% 2.07/1.00  ------ Problem Properties 
% 2.07/1.00  
% 2.07/1.00  
% 2.07/1.00  clauses                                 84
% 2.07/1.00  conjectures                             3
% 2.07/1.00  EPR                                     14
% 2.07/1.00  Horn                                    58
% 2.07/1.00  unary                                   25
% 2.07/1.00  binary                                  30
% 2.07/1.00  lits                                    190
% 2.07/1.00  lits eq                                 53
% 2.07/1.00  fd_pure                                 0
% 2.07/1.00  fd_pseudo                               0
% 2.07/1.00  fd_cond                                 9
% 2.07/1.00  fd_pseudo_cond                          5
% 2.07/1.00  AC symbols                              0
% 2.07/1.00  
% 2.07/1.00  ------ Schedule dynamic 5 is on 
% 2.07/1.00  
% 2.07/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.07/1.00  
% 2.07/1.00  
% 2.07/1.00  ------ 
% 2.07/1.00  Current options:
% 2.07/1.00  ------ 
% 2.07/1.00  
% 2.07/1.00  ------ Input Options
% 2.07/1.00  
% 2.07/1.00  --out_options                           all
% 2.07/1.00  --tptp_safe_out                         true
% 2.07/1.00  --problem_path                          ""
% 2.07/1.00  --include_path                          ""
% 2.07/1.00  --clausifier                            res/vclausify_rel
% 2.07/1.00  --clausifier_options                    --mode clausify
% 2.07/1.00  --stdin                                 false
% 2.07/1.00  --stats_out                             all
% 2.07/1.00  
% 2.07/1.00  ------ General Options
% 2.07/1.00  
% 2.07/1.00  --fof                                   false
% 2.07/1.00  --time_out_real                         305.
% 2.07/1.00  --time_out_virtual                      -1.
% 2.07/1.00  --symbol_type_check                     false
% 2.07/1.00  --clausify_out                          false
% 2.07/1.00  --sig_cnt_out                           false
% 2.07/1.00  --trig_cnt_out                          false
% 2.07/1.00  --trig_cnt_out_tolerance                1.
% 2.07/1.00  --trig_cnt_out_sk_spl                   false
% 2.07/1.00  --abstr_cl_out                          false
% 2.07/1.00  
% 2.07/1.00  ------ Global Options
% 2.07/1.00  
% 2.07/1.00  --schedule                              default
% 2.07/1.00  --add_important_lit                     false
% 2.07/1.00  --prop_solver_per_cl                    1000
% 2.07/1.00  --min_unsat_core                        false
% 2.07/1.00  --soft_assumptions                      false
% 2.07/1.00  --soft_lemma_size                       3
% 2.07/1.00  --prop_impl_unit_size                   0
% 2.07/1.00  --prop_impl_unit                        []
% 2.07/1.00  --share_sel_clauses                     true
% 2.07/1.00  --reset_solvers                         false
% 2.07/1.00  --bc_imp_inh                            [conj_cone]
% 2.07/1.00  --conj_cone_tolerance                   3.
% 2.07/1.00  --extra_neg_conj                        none
% 2.07/1.00  --large_theory_mode                     true
% 2.07/1.00  --prolific_symb_bound                   200
% 2.07/1.00  --lt_threshold                          2000
% 2.07/1.00  --clause_weak_htbl                      true
% 2.07/1.00  --gc_record_bc_elim                     false
% 2.07/1.00  
% 2.07/1.00  ------ Preprocessing Options
% 2.07/1.00  
% 2.07/1.00  --preprocessing_flag                    true
% 2.07/1.00  --time_out_prep_mult                    0.1
% 2.07/1.00  --splitting_mode                        input
% 2.07/1.00  --splitting_grd                         true
% 2.07/1.00  --splitting_cvd                         false
% 2.07/1.00  --splitting_cvd_svl                     false
% 2.07/1.00  --splitting_nvd                         32
% 2.07/1.00  --sub_typing                            true
% 2.07/1.00  --prep_gs_sim                           true
% 2.07/1.00  --prep_unflatten                        true
% 2.07/1.00  --prep_res_sim                          true
% 2.07/1.00  --prep_upred                            true
% 2.07/1.00  --prep_sem_filter                       exhaustive
% 2.07/1.00  --prep_sem_filter_out                   false
% 2.07/1.00  --pred_elim                             true
% 2.07/1.00  --res_sim_input                         true
% 2.07/1.00  --eq_ax_congr_red                       true
% 2.07/1.00  --pure_diseq_elim                       true
% 2.07/1.00  --brand_transform                       false
% 2.07/1.00  --non_eq_to_eq                          false
% 2.07/1.00  --prep_def_merge                        true
% 2.07/1.00  --prep_def_merge_prop_impl              false
% 2.07/1.00  --prep_def_merge_mbd                    true
% 2.07/1.00  --prep_def_merge_tr_red                 false
% 2.07/1.00  --prep_def_merge_tr_cl                  false
% 2.07/1.00  --smt_preprocessing                     true
% 2.07/1.00  --smt_ac_axioms                         fast
% 2.07/1.00  --preprocessed_out                      false
% 2.07/1.00  --preprocessed_stats                    false
% 2.07/1.00  
% 2.07/1.00  ------ Abstraction refinement Options
% 2.07/1.00  
% 2.07/1.00  --abstr_ref                             []
% 2.07/1.00  --abstr_ref_prep                        false
% 2.07/1.00  --abstr_ref_until_sat                   false
% 2.07/1.00  --abstr_ref_sig_restrict                funpre
% 2.07/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.07/1.00  --abstr_ref_under                       []
% 2.07/1.00  
% 2.07/1.00  ------ SAT Options
% 2.07/1.00  
% 2.07/1.00  --sat_mode                              false
% 2.07/1.00  --sat_fm_restart_options                ""
% 2.07/1.00  --sat_gr_def                            false
% 2.07/1.00  --sat_epr_types                         true
% 2.07/1.00  --sat_non_cyclic_types                  false
% 2.07/1.00  --sat_finite_models                     false
% 2.07/1.00  --sat_fm_lemmas                         false
% 2.07/1.00  --sat_fm_prep                           false
% 2.07/1.00  --sat_fm_uc_incr                        true
% 2.07/1.00  --sat_out_model                         small
% 2.07/1.00  --sat_out_clauses                       false
% 2.07/1.00  
% 2.07/1.00  ------ QBF Options
% 2.07/1.00  
% 2.07/1.00  --qbf_mode                              false
% 2.07/1.00  --qbf_elim_univ                         false
% 2.07/1.00  --qbf_dom_inst                          none
% 2.07/1.00  --qbf_dom_pre_inst                      false
% 2.07/1.00  --qbf_sk_in                             false
% 2.07/1.00  --qbf_pred_elim                         true
% 2.07/1.00  --qbf_split                             512
% 2.07/1.00  
% 2.07/1.00  ------ BMC1 Options
% 2.07/1.00  
% 2.07/1.00  --bmc1_incremental                      false
% 2.07/1.00  --bmc1_axioms                           reachable_all
% 2.07/1.00  --bmc1_min_bound                        0
% 2.07/1.00  --bmc1_max_bound                        -1
% 2.07/1.00  --bmc1_max_bound_default                -1
% 2.07/1.00  --bmc1_symbol_reachability              true
% 2.07/1.00  --bmc1_property_lemmas                  false
% 2.07/1.00  --bmc1_k_induction                      false
% 2.07/1.00  --bmc1_non_equiv_states                 false
% 2.07/1.00  --bmc1_deadlock                         false
% 2.07/1.00  --bmc1_ucm                              false
% 2.07/1.00  --bmc1_add_unsat_core                   none
% 2.07/1.00  --bmc1_unsat_core_children              false
% 2.07/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.07/1.00  --bmc1_out_stat                         full
% 2.07/1.00  --bmc1_ground_init                      false
% 2.07/1.00  --bmc1_pre_inst_next_state              false
% 2.07/1.00  --bmc1_pre_inst_state                   false
% 2.07/1.00  --bmc1_pre_inst_reach_state             false
% 2.07/1.00  --bmc1_out_unsat_core                   false
% 2.07/1.00  --bmc1_aig_witness_out                  false
% 2.07/1.00  --bmc1_verbose                          false
% 2.07/1.00  --bmc1_dump_clauses_tptp                false
% 2.07/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.07/1.00  --bmc1_dump_file                        -
% 2.07/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.07/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.07/1.00  --bmc1_ucm_extend_mode                  1
% 2.07/1.00  --bmc1_ucm_init_mode                    2
% 2.07/1.00  --bmc1_ucm_cone_mode                    none
% 2.07/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.07/1.00  --bmc1_ucm_relax_model                  4
% 2.07/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.07/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.07/1.00  --bmc1_ucm_layered_model                none
% 2.07/1.00  --bmc1_ucm_max_lemma_size               10
% 2.07/1.00  
% 2.07/1.00  ------ AIG Options
% 2.07/1.00  
% 2.07/1.00  --aig_mode                              false
% 2.07/1.00  
% 2.07/1.00  ------ Instantiation Options
% 2.07/1.00  
% 2.07/1.00  --instantiation_flag                    true
% 2.07/1.00  --inst_sos_flag                         false
% 2.07/1.00  --inst_sos_phase                        true
% 2.07/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.07/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.07/1.00  --inst_lit_sel_side                     none
% 2.07/1.00  --inst_solver_per_active                1400
% 2.07/1.00  --inst_solver_calls_frac                1.
% 2.07/1.00  --inst_passive_queue_type               priority_queues
% 2.07/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.07/1.00  --inst_passive_queues_freq              [25;2]
% 2.07/1.00  --inst_dismatching                      true
% 2.07/1.00  --inst_eager_unprocessed_to_passive     true
% 2.07/1.00  --inst_prop_sim_given                   true
% 2.07/1.00  --inst_prop_sim_new                     false
% 2.07/1.00  --inst_subs_new                         false
% 2.07/1.00  --inst_eq_res_simp                      false
% 2.07/1.00  --inst_subs_given                       false
% 2.07/1.00  --inst_orphan_elimination               true
% 2.07/1.00  --inst_learning_loop_flag               true
% 2.07/1.00  --inst_learning_start                   3000
% 2.07/1.00  --inst_learning_factor                  2
% 2.07/1.00  --inst_start_prop_sim_after_learn       3
% 2.07/1.00  --inst_sel_renew                        solver
% 2.07/1.00  --inst_lit_activity_flag                true
% 2.07/1.00  --inst_restr_to_given                   false
% 2.07/1.00  --inst_activity_threshold               500
% 2.07/1.00  --inst_out_proof                        true
% 2.07/1.00  
% 2.07/1.00  ------ Resolution Options
% 2.07/1.00  
% 2.07/1.00  --resolution_flag                       false
% 2.07/1.00  --res_lit_sel                           adaptive
% 2.07/1.00  --res_lit_sel_side                      none
% 2.07/1.00  --res_ordering                          kbo
% 2.07/1.00  --res_to_prop_solver                    active
% 2.07/1.00  --res_prop_simpl_new                    false
% 2.07/1.00  --res_prop_simpl_given                  true
% 2.07/1.00  --res_passive_queue_type                priority_queues
% 2.07/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.07/1.00  --res_passive_queues_freq               [15;5]
% 2.07/1.00  --res_forward_subs                      full
% 2.07/1.00  --res_backward_subs                     full
% 2.07/1.00  --res_forward_subs_resolution           true
% 2.07/1.00  --res_backward_subs_resolution          true
% 2.07/1.00  --res_orphan_elimination                true
% 2.07/1.00  --res_time_limit                        2.
% 2.07/1.00  --res_out_proof                         true
% 2.07/1.00  
% 2.07/1.00  ------ Superposition Options
% 2.07/1.00  
% 2.07/1.00  --superposition_flag                    true
% 2.07/1.00  --sup_passive_queue_type                priority_queues
% 2.07/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.07/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.07/1.00  --demod_completeness_check              fast
% 2.07/1.00  --demod_use_ground                      true
% 2.07/1.00  --sup_to_prop_solver                    passive
% 2.07/1.00  --sup_prop_simpl_new                    true
% 2.07/1.00  --sup_prop_simpl_given                  true
% 2.07/1.00  --sup_fun_splitting                     false
% 2.07/1.00  --sup_smt_interval                      50000
% 2.07/1.00  
% 2.07/1.00  ------ Superposition Simplification Setup
% 2.07/1.00  
% 2.07/1.00  --sup_indices_passive                   []
% 2.07/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.07/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/1.00  --sup_full_bw                           [BwDemod]
% 2.07/1.00  --sup_immed_triv                        [TrivRules]
% 2.07/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.07/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/1.00  --sup_immed_bw_main                     []
% 2.07/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.07/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/1.00  
% 2.07/1.00  ------ Combination Options
% 2.07/1.00  
% 2.07/1.00  --comb_res_mult                         3
% 2.07/1.00  --comb_sup_mult                         2
% 2.07/1.00  --comb_inst_mult                        10
% 2.07/1.00  
% 2.07/1.00  ------ Debug Options
% 2.07/1.00  
% 2.07/1.00  --dbg_backtrace                         false
% 2.07/1.00  --dbg_dump_prop_clauses                 false
% 2.07/1.00  --dbg_dump_prop_clauses_file            -
% 2.07/1.00  --dbg_out_stat                          false
% 2.07/1.00  
% 2.07/1.00  
% 2.07/1.00  
% 2.07/1.00  
% 2.07/1.00  ------ Proving...
% 2.07/1.00  
% 2.07/1.00  
% 2.07/1.00  % SZS status Theorem for theBenchmark.p
% 2.07/1.00  
% 2.07/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.07/1.00  
% 2.07/1.00  fof(f34,axiom,(
% 2.07/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f68,plain,(
% 2.07/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.07/1.00    inference(ennf_transformation,[],[f34])).
% 2.07/1.00  
% 2.07/1.00  fof(f69,plain,(
% 2.07/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.07/1.00    inference(flattening,[],[f68])).
% 2.07/1.00  
% 2.07/1.00  fof(f186,plain,(
% 2.07/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.07/1.00    inference(cnf_transformation,[],[f69])).
% 2.07/1.00  
% 2.07/1.00  fof(f36,conjecture,(
% 2.07/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f37,negated_conjecture,(
% 2.07/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.07/1.00    inference(negated_conjecture,[],[f36])).
% 2.07/1.00  
% 2.07/1.00  fof(f70,plain,(
% 2.07/1.00    ? [X0,X1,X2] : (((~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 2.07/1.00    inference(ennf_transformation,[],[f37])).
% 2.07/1.00  
% 2.07/1.00  fof(f71,plain,(
% 2.07/1.00    ? [X0,X1,X2] : (~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.07/1.00    inference(flattening,[],[f70])).
% 2.07/1.00  
% 2.07/1.00  fof(f105,plain,(
% 2.07/1.00    ? [X0,X1,X2] : (~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (~v1_partfun1(sK15,sK13) & (k1_xboole_0 = sK13 | k1_xboole_0 != sK14) & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) & v1_funct_2(sK15,sK13,sK14) & v1_funct_1(sK15) & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) & v1_funct_1(sK15))),
% 2.07/1.00    introduced(choice_axiom,[])).
% 2.07/1.00  
% 2.07/1.00  fof(f106,plain,(
% 2.07/1.00    ~v1_partfun1(sK15,sK13) & (k1_xboole_0 = sK13 | k1_xboole_0 != sK14) & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) & v1_funct_2(sK15,sK13,sK14) & v1_funct_1(sK15) & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) & v1_funct_1(sK15)),
% 2.07/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f71,f105])).
% 2.07/1.00  
% 2.07/1.00  fof(f192,plain,(
% 2.07/1.00    v1_funct_2(sK15,sK13,sK14)),
% 2.07/1.00    inference(cnf_transformation,[],[f106])).
% 2.07/1.00  
% 2.07/1.00  fof(f189,plain,(
% 2.07/1.00    v1_funct_1(sK15)),
% 2.07/1.00    inference(cnf_transformation,[],[f106])).
% 2.07/1.00  
% 2.07/1.00  fof(f190,plain,(
% 2.07/1.00    m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))),
% 2.07/1.00    inference(cnf_transformation,[],[f106])).
% 2.07/1.00  
% 2.07/1.00  fof(f195,plain,(
% 2.07/1.00    ~v1_partfun1(sK15,sK13)),
% 2.07/1.00    inference(cnf_transformation,[],[f106])).
% 2.07/1.00  
% 2.07/1.00  fof(f4,axiom,(
% 2.07/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f40,plain,(
% 2.07/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.07/1.00    inference(ennf_transformation,[],[f4])).
% 2.07/1.00  
% 2.07/1.00  fof(f112,plain,(
% 2.07/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.07/1.00    inference(cnf_transformation,[],[f40])).
% 2.07/1.00  
% 2.07/1.00  fof(f194,plain,(
% 2.07/1.00    k1_xboole_0 = sK13 | k1_xboole_0 != sK14),
% 2.07/1.00    inference(cnf_transformation,[],[f106])).
% 2.07/1.00  
% 2.07/1.00  fof(f33,axiom,(
% 2.07/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 2.07/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.07/1.00  
% 2.07/1.00  fof(f67,plain,(
% 2.07/1.00    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.07/1.00    inference(ennf_transformation,[],[f33])).
% 2.07/1.00  
% 2.07/1.00  fof(f184,plain,(
% 2.07/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.07/1.00    inference(cnf_transformation,[],[f67])).
% 2.07/1.00  
% 2.07/1.00  cnf(c_78,plain,
% 2.07/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.07/1.00      | v1_partfun1(X0,X1)
% 2.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/1.00      | ~ v1_funct_1(X0)
% 2.07/1.00      | v1_xboole_0(X2) ),
% 2.07/1.00      inference(cnf_transformation,[],[f186]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_85,negated_conjecture,
% 2.07/1.00      ( v1_funct_2(sK15,sK13,sK14) ),
% 2.07/1.00      inference(cnf_transformation,[],[f192]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_1010,plain,
% 2.07/1.00      ( v1_partfun1(X0,X1)
% 2.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/1.00      | ~ v1_funct_1(X0)
% 2.07/1.00      | v1_xboole_0(X2)
% 2.07/1.00      | sK14 != X2
% 2.07/1.00      | sK13 != X1
% 2.07/1.00      | sK15 != X0 ),
% 2.07/1.00      inference(resolution_lifted,[status(thm)],[c_78,c_85]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_1011,plain,
% 2.07/1.00      ( v1_partfun1(sK15,sK13)
% 2.07/1.00      | ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
% 2.07/1.00      | ~ v1_funct_1(sK15)
% 2.07/1.00      | v1_xboole_0(sK14) ),
% 2.07/1.00      inference(unflattening,[status(thm)],[c_1010]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_88,negated_conjecture,
% 2.07/1.00      ( v1_funct_1(sK15) ),
% 2.07/1.00      inference(cnf_transformation,[],[f189]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_87,negated_conjecture,
% 2.07/1.00      ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) ),
% 2.07/1.00      inference(cnf_transformation,[],[f190]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_82,negated_conjecture,
% 2.07/1.00      ( ~ v1_partfun1(sK15,sK13) ),
% 2.07/1.00      inference(cnf_transformation,[],[f195]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_1013,plain,
% 2.07/1.00      ( v1_xboole_0(sK14) ),
% 2.07/1.00      inference(global_propositional_subsumption,
% 2.07/1.00                [status(thm)],
% 2.07/1.00                [c_1011,c_88,c_87,c_82]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4434,plain,
% 2.07/1.00      ( v1_xboole_0(sK14) = iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_1013]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_5,plain,
% 2.07/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.07/1.00      inference(cnf_transformation,[],[f112]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4500,plain,
% 2.07/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_5611,plain,
% 2.07/1.00      ( sK14 = k1_xboole_0 ),
% 2.07/1.00      inference(superposition,[status(thm)],[c_4434,c_4500]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_83,negated_conjecture,
% 2.07/1.00      ( k1_xboole_0 != sK14 | k1_xboole_0 = sK13 ),
% 2.07/1.00      inference(cnf_transformation,[],[f194]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_5743,plain,
% 2.07/1.00      ( sK13 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.07/1.00      inference(demodulation,[status(thm)],[c_5611,c_83]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_5744,plain,
% 2.07/1.00      ( sK13 = k1_xboole_0 ),
% 2.07/1.00      inference(equality_resolution_simp,[status(thm)],[c_5743]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_5741,plain,
% 2.07/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.07/1.00      inference(demodulation,[status(thm)],[c_5611,c_4434]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_2920,plain,
% 2.07/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.07/1.00      theory(equality) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_5116,plain,
% 2.07/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK13) | sK13 != X0 ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_2920]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_5117,plain,
% 2.07/1.00      ( sK13 != X0
% 2.07/1.00      | v1_xboole_0(X0) != iProver_top
% 2.07/1.00      | v1_xboole_0(sK13) = iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_5116]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_5119,plain,
% 2.07/1.00      ( sK13 != k1_xboole_0
% 2.07/1.00      | v1_xboole_0(sK13) = iProver_top
% 2.07/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.07/1.00      inference(instantiation,[status(thm)],[c_5117]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4437,plain,
% 2.07/1.00      ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) = iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_87]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_77,plain,
% 2.07/1.00      ( v1_partfun1(X0,X1)
% 2.07/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/1.00      | ~ v1_xboole_0(X1) ),
% 2.07/1.00      inference(cnf_transformation,[],[f184]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_1023,plain,
% 2.07/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/1.00      | ~ v1_xboole_0(X1)
% 2.07/1.00      | sK13 != X1
% 2.07/1.00      | sK15 != X0 ),
% 2.07/1.00      inference(resolution_lifted,[status(thm)],[c_77,c_82]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_1024,plain,
% 2.07/1.00      ( ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,X0)))
% 2.07/1.00      | ~ v1_xboole_0(sK13) ),
% 2.07/1.00      inference(unflattening,[status(thm)],[c_1023]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_4433,plain,
% 2.07/1.00      ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,X0))) != iProver_top
% 2.07/1.00      | v1_xboole_0(sK13) != iProver_top ),
% 2.07/1.00      inference(predicate_to_equality,[status(thm)],[c_1024]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(c_5048,plain,
% 2.07/1.00      ( v1_xboole_0(sK13) != iProver_top ),
% 2.07/1.00      inference(superposition,[status(thm)],[c_4437,c_4433]) ).
% 2.07/1.00  
% 2.07/1.00  cnf(contradiction,plain,
% 2.07/1.00      ( $false ),
% 2.07/1.00      inference(minisat,[status(thm)],[c_5744,c_5741,c_5119,c_5048]) ).
% 2.07/1.00  
% 2.07/1.00  
% 2.07/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.07/1.00  
% 2.07/1.00  ------                               Statistics
% 2.07/1.00  
% 2.07/1.00  ------ General
% 2.07/1.00  
% 2.07/1.00  abstr_ref_over_cycles:                  0
% 2.07/1.00  abstr_ref_under_cycles:                 0
% 2.07/1.00  gc_basic_clause_elim:                   0
% 2.07/1.00  forced_gc_time:                         0
% 2.07/1.00  parsing_time:                           0.013
% 2.07/1.00  unif_index_cands_time:                  0.
% 2.07/1.00  unif_index_add_time:                    0.
% 2.07/1.00  orderings_time:                         0.
% 2.07/1.00  out_proof_time:                         0.009
% 2.07/1.00  total_time:                             0.149
% 2.07/1.00  num_of_symbols:                         70
% 2.07/1.00  num_of_terms:                           2391
% 2.07/1.00  
% 2.07/1.00  ------ Preprocessing
% 2.07/1.00  
% 2.07/1.00  num_of_splits:                          0
% 2.07/1.00  num_of_split_atoms:                     0
% 2.07/1.00  num_of_reused_defs:                     0
% 2.07/1.00  num_eq_ax_congr_red:                    53
% 2.07/1.00  num_of_sem_filtered_clauses:            1
% 2.07/1.00  num_of_subtypes:                        0
% 2.07/1.00  monotx_restored_types:                  0
% 2.07/1.00  sat_num_of_epr_types:                   0
% 2.07/1.00  sat_num_of_non_cyclic_types:            0
% 2.07/1.00  sat_guarded_non_collapsed_types:        0
% 2.07/1.00  num_pure_diseq_elim:                    0
% 2.07/1.00  simp_replaced_by:                       0
% 2.07/1.00  res_preprocessed:                       383
% 2.07/1.00  prep_upred:                             0
% 2.07/1.00  prep_unflattend:                        26
% 2.07/1.00  smt_new_axioms:                         0
% 2.07/1.00  pred_elim_cands:                        9
% 2.07/1.00  pred_elim:                              2
% 2.07/1.00  pred_elim_cl:                           2
% 2.07/1.00  pred_elim_cycles:                       6
% 2.07/1.00  merged_defs:                            16
% 2.07/1.00  merged_defs_ncl:                        0
% 2.07/1.00  bin_hyper_res:                          17
% 2.07/1.00  prep_cycles:                            4
% 2.07/1.00  pred_elim_time:                         0.022
% 2.07/1.00  splitting_time:                         0.
% 2.07/1.00  sem_filter_time:                        0.
% 2.07/1.00  monotx_time:                            0.
% 2.07/1.00  subtype_inf_time:                       0.
% 2.07/1.00  
% 2.07/1.00  ------ Problem properties
% 2.07/1.00  
% 2.07/1.00  clauses:                                84
% 2.07/1.00  conjectures:                            3
% 2.07/1.00  epr:                                    14
% 2.07/1.00  horn:                                   58
% 2.07/1.00  ground:                                 13
% 2.07/1.00  unary:                                  25
% 2.07/1.00  binary:                                 30
% 2.07/1.00  lits:                                   190
% 2.07/1.00  lits_eq:                                53
% 2.07/1.00  fd_pure:                                0
% 2.07/1.00  fd_pseudo:                              0
% 2.07/1.00  fd_cond:                                9
% 2.07/1.00  fd_pseudo_cond:                         5
% 2.07/1.00  ac_symbols:                             0
% 2.07/1.00  
% 2.07/1.00  ------ Propositional Solver
% 2.07/1.00  
% 2.07/1.00  prop_solver_calls:                      24
% 2.07/1.00  prop_fast_solver_calls:                 2107
% 2.07/1.00  smt_solver_calls:                       0
% 2.07/1.00  smt_fast_solver_calls:                  0
% 2.07/1.00  prop_num_of_clauses:                    843
% 2.07/1.00  prop_preprocess_simplified:             10802
% 2.07/1.00  prop_fo_subsumed:                       3
% 2.07/1.00  prop_solver_time:                       0.
% 2.07/1.00  smt_solver_time:                        0.
% 2.07/1.00  smt_fast_solver_time:                   0.
% 2.07/1.00  prop_fast_solver_time:                  0.
% 2.07/1.00  prop_unsat_core_time:                   0.
% 2.07/1.00  
% 2.07/1.00  ------ QBF
% 2.07/1.00  
% 2.07/1.00  qbf_q_res:                              0
% 2.07/1.00  qbf_num_tautologies:                    0
% 2.07/1.00  qbf_prep_cycles:                        0
% 2.07/1.00  
% 2.07/1.00  ------ BMC1
% 2.07/1.00  
% 2.07/1.00  bmc1_current_bound:                     -1
% 2.07/1.00  bmc1_last_solved_bound:                 -1
% 2.07/1.00  bmc1_unsat_core_size:                   -1
% 2.07/1.00  bmc1_unsat_core_parents_size:           -1
% 2.07/1.00  bmc1_merge_next_fun:                    0
% 2.07/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.07/1.00  
% 2.07/1.00  ------ Instantiation
% 2.07/1.00  
% 2.07/1.00  inst_num_of_clauses:                    239
% 2.07/1.00  inst_num_in_passive:                    49
% 2.07/1.00  inst_num_in_active:                     165
% 2.07/1.00  inst_num_in_unprocessed:                25
% 2.07/1.00  inst_num_of_loops:                      200
% 2.07/1.00  inst_num_of_learning_restarts:          0
% 2.07/1.00  inst_num_moves_active_passive:          34
% 2.07/1.00  inst_lit_activity:                      0
% 2.07/1.00  inst_lit_activity_moves:                0
% 2.07/1.00  inst_num_tautologies:                   0
% 2.07/1.00  inst_num_prop_implied:                  0
% 2.07/1.00  inst_num_existing_simplified:           0
% 2.07/1.00  inst_num_eq_res_simplified:             0
% 2.07/1.00  inst_num_child_elim:                    0
% 2.07/1.00  inst_num_of_dismatching_blockings:      5
% 2.07/1.00  inst_num_of_non_proper_insts:           119
% 2.07/1.00  inst_num_of_duplicates:                 0
% 2.07/1.00  inst_inst_num_from_inst_to_res:         0
% 2.07/1.00  inst_dismatching_checking_time:         0.
% 2.07/1.00  
% 2.07/1.00  ------ Resolution
% 2.07/1.00  
% 2.07/1.00  res_num_of_clauses:                     0
% 2.07/1.00  res_num_in_passive:                     0
% 2.07/1.00  res_num_in_active:                      0
% 2.07/1.00  res_num_of_loops:                       387
% 2.07/1.00  res_forward_subset_subsumed:            9
% 2.07/1.00  res_backward_subset_subsumed:           0
% 2.07/1.00  res_forward_subsumed:                   0
% 2.07/1.00  res_backward_subsumed:                  0
% 2.07/1.00  res_forward_subsumption_resolution:     0
% 2.07/1.00  res_backward_subsumption_resolution:    0
% 2.07/1.00  res_clause_to_clause_subsumption:       139
% 2.07/1.00  res_orphan_elimination:                 0
% 2.07/1.00  res_tautology_del:                      37
% 2.07/1.00  res_num_eq_res_simplified:              0
% 2.07/1.00  res_num_sel_changes:                    0
% 2.07/1.00  res_moves_from_active_to_pass:          0
% 2.07/1.00  
% 2.07/1.00  ------ Superposition
% 2.07/1.00  
% 2.07/1.00  sup_time_total:                         0.
% 2.07/1.00  sup_time_generating:                    0.
% 2.07/1.00  sup_time_sim_full:                      0.
% 2.07/1.00  sup_time_sim_immed:                     0.
% 2.07/1.00  
% 2.07/1.00  sup_num_of_clauses:                     88
% 2.07/1.00  sup_num_in_active:                      35
% 2.07/1.00  sup_num_in_passive:                     53
% 2.07/1.00  sup_num_of_loops:                       38
% 2.07/1.00  sup_fw_superposition:                   6
% 2.07/1.00  sup_bw_superposition:                   3
% 2.07/1.00  sup_immediate_simplified:               2
% 2.07/1.00  sup_given_eliminated:                   0
% 2.07/1.00  comparisons_done:                       0
% 2.07/1.00  comparisons_avoided:                    1
% 2.07/1.00  
% 2.07/1.00  ------ Simplifications
% 2.07/1.00  
% 2.07/1.00  
% 2.07/1.00  sim_fw_subset_subsumed:                 1
% 2.07/1.00  sim_bw_subset_subsumed:                 0
% 2.07/1.00  sim_fw_subsumed:                        1
% 2.07/1.00  sim_bw_subsumed:                        0
% 2.07/1.00  sim_fw_subsumption_res:                 0
% 2.07/1.00  sim_bw_subsumption_res:                 0
% 2.07/1.00  sim_tautology_del:                      0
% 2.07/1.00  sim_eq_tautology_del:                   1
% 2.07/1.00  sim_eq_res_simp:                        1
% 2.07/1.00  sim_fw_demodulated:                     1
% 2.07/1.00  sim_bw_demodulated:                     3
% 2.07/1.00  sim_light_normalised:                   2
% 2.07/1.00  sim_joinable_taut:                      0
% 2.07/1.00  sim_joinable_simp:                      0
% 2.07/1.00  sim_ac_normalised:                      0
% 2.07/1.00  sim_smt_subsumption:                    0
% 2.07/1.00  
%------------------------------------------------------------------------------
