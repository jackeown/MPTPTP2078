%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:46:09 EST 2020

% Result     : Theorem 1.07s
% Output     : CNFRefutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   44 (  66 expanded)
%              Number of clauses        :   16 (  24 expanded)
%              Number of leaves         :   10 (  14 expanded)
%              Depth                    :   13
%              Number of atoms          :  152 ( 200 expanded)
%              Number of equality atoms :   61 ( 103 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f13])).

fof(f17,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,X3),X0) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK0(X0,X1,X2)),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17,f16,f15])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)
      | r2_hidden(sK0(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f9,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK3(X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK3(X0)
        & r2_hidden(sK3(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f19])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f5])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK4) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f21])).

fof(f35,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK4) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_6,plain,
    ( r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_527,plain,
    ( k9_relat_1(X0,X1) = X2
    | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_530,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_633,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_530])).

cnf(c_1282,plain,
    ( k9_relat_1(k1_xboole_0,X0) = X1
    | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_527,c_633])).

cnf(c_11,plain,
    ( r2_hidden(sK3(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_522,plain,
    ( r2_hidden(sK3(X0),X0) = iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_870,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_522,c_633])).

cnf(c_2527,plain,
    ( r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top
    | k9_relat_1(k1_xboole_0,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1282,c_870])).

cnf(c_2528,plain,
    ( k9_relat_1(k1_xboole_0,X0) = X1
    | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2527])).

cnf(c_2535,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2528,c_633])).

cnf(c_12,negated_conjecture,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK4) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2606,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2535,c_12])).

cnf(c_2633,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2606])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:09:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.07/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.07/1.03  
% 1.07/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.07/1.03  
% 1.07/1.03  ------  iProver source info
% 1.07/1.03  
% 1.07/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.07/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.07/1.03  git: non_committed_changes: false
% 1.07/1.03  git: last_make_outside_of_git: false
% 1.07/1.03  
% 1.07/1.03  ------ 
% 1.07/1.03  
% 1.07/1.03  ------ Input Options
% 1.07/1.03  
% 1.07/1.03  --out_options                           all
% 1.07/1.03  --tptp_safe_out                         true
% 1.07/1.03  --problem_path                          ""
% 1.07/1.03  --include_path                          ""
% 1.07/1.03  --clausifier                            res/vclausify_rel
% 1.07/1.03  --clausifier_options                    --mode clausify
% 1.07/1.03  --stdin                                 false
% 1.07/1.03  --stats_out                             all
% 1.07/1.03  
% 1.07/1.03  ------ General Options
% 1.07/1.03  
% 1.07/1.03  --fof                                   false
% 1.07/1.03  --time_out_real                         305.
% 1.07/1.03  --time_out_virtual                      -1.
% 1.07/1.03  --symbol_type_check                     false
% 1.07/1.03  --clausify_out                          false
% 1.07/1.03  --sig_cnt_out                           false
% 1.07/1.03  --trig_cnt_out                          false
% 1.07/1.03  --trig_cnt_out_tolerance                1.
% 1.07/1.03  --trig_cnt_out_sk_spl                   false
% 1.07/1.03  --abstr_cl_out                          false
% 1.07/1.03  
% 1.07/1.03  ------ Global Options
% 1.07/1.03  
% 1.07/1.03  --schedule                              default
% 1.07/1.03  --add_important_lit                     false
% 1.07/1.03  --prop_solver_per_cl                    1000
% 1.07/1.03  --min_unsat_core                        false
% 1.07/1.03  --soft_assumptions                      false
% 1.07/1.03  --soft_lemma_size                       3
% 1.07/1.03  --prop_impl_unit_size                   0
% 1.07/1.03  --prop_impl_unit                        []
% 1.07/1.03  --share_sel_clauses                     true
% 1.07/1.03  --reset_solvers                         false
% 1.07/1.03  --bc_imp_inh                            [conj_cone]
% 1.07/1.03  --conj_cone_tolerance                   3.
% 1.07/1.03  --extra_neg_conj                        none
% 1.07/1.03  --large_theory_mode                     true
% 1.07/1.03  --prolific_symb_bound                   200
% 1.07/1.03  --lt_threshold                          2000
% 1.07/1.03  --clause_weak_htbl                      true
% 1.07/1.03  --gc_record_bc_elim                     false
% 1.07/1.03  
% 1.07/1.03  ------ Preprocessing Options
% 1.07/1.03  
% 1.07/1.03  --preprocessing_flag                    true
% 1.07/1.03  --time_out_prep_mult                    0.1
% 1.07/1.03  --splitting_mode                        input
% 1.07/1.03  --splitting_grd                         true
% 1.07/1.03  --splitting_cvd                         false
% 1.07/1.03  --splitting_cvd_svl                     false
% 1.07/1.03  --splitting_nvd                         32
% 1.07/1.03  --sub_typing                            true
% 1.07/1.03  --prep_gs_sim                           true
% 1.07/1.03  --prep_unflatten                        true
% 1.07/1.03  --prep_res_sim                          true
% 1.07/1.03  --prep_upred                            true
% 1.07/1.03  --prep_sem_filter                       exhaustive
% 1.07/1.03  --prep_sem_filter_out                   false
% 1.07/1.03  --pred_elim                             true
% 1.07/1.03  --res_sim_input                         true
% 1.07/1.03  --eq_ax_congr_red                       true
% 1.07/1.03  --pure_diseq_elim                       true
% 1.07/1.03  --brand_transform                       false
% 1.07/1.03  --non_eq_to_eq                          false
% 1.07/1.03  --prep_def_merge                        true
% 1.07/1.03  --prep_def_merge_prop_impl              false
% 1.07/1.03  --prep_def_merge_mbd                    true
% 1.07/1.03  --prep_def_merge_tr_red                 false
% 1.07/1.03  --prep_def_merge_tr_cl                  false
% 1.07/1.03  --smt_preprocessing                     true
% 1.07/1.03  --smt_ac_axioms                         fast
% 1.07/1.03  --preprocessed_out                      false
% 1.07/1.03  --preprocessed_stats                    false
% 1.07/1.03  
% 1.07/1.03  ------ Abstraction refinement Options
% 1.07/1.03  
% 1.07/1.03  --abstr_ref                             []
% 1.07/1.03  --abstr_ref_prep                        false
% 1.07/1.03  --abstr_ref_until_sat                   false
% 1.07/1.03  --abstr_ref_sig_restrict                funpre
% 1.07/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.07/1.03  --abstr_ref_under                       []
% 1.07/1.03  
% 1.07/1.03  ------ SAT Options
% 1.07/1.03  
% 1.07/1.03  --sat_mode                              false
% 1.07/1.03  --sat_fm_restart_options                ""
% 1.07/1.03  --sat_gr_def                            false
% 1.07/1.03  --sat_epr_types                         true
% 1.07/1.03  --sat_non_cyclic_types                  false
% 1.07/1.03  --sat_finite_models                     false
% 1.07/1.03  --sat_fm_lemmas                         false
% 1.07/1.03  --sat_fm_prep                           false
% 1.07/1.03  --sat_fm_uc_incr                        true
% 1.07/1.03  --sat_out_model                         small
% 1.07/1.03  --sat_out_clauses                       false
% 1.07/1.03  
% 1.07/1.03  ------ QBF Options
% 1.07/1.03  
% 1.07/1.03  --qbf_mode                              false
% 1.07/1.03  --qbf_elim_univ                         false
% 1.07/1.03  --qbf_dom_inst                          none
% 1.07/1.03  --qbf_dom_pre_inst                      false
% 1.07/1.03  --qbf_sk_in                             false
% 1.07/1.03  --qbf_pred_elim                         true
% 1.07/1.03  --qbf_split                             512
% 1.07/1.03  
% 1.07/1.03  ------ BMC1 Options
% 1.07/1.03  
% 1.07/1.03  --bmc1_incremental                      false
% 1.07/1.03  --bmc1_axioms                           reachable_all
% 1.07/1.03  --bmc1_min_bound                        0
% 1.07/1.03  --bmc1_max_bound                        -1
% 1.07/1.03  --bmc1_max_bound_default                -1
% 1.07/1.03  --bmc1_symbol_reachability              true
% 1.07/1.03  --bmc1_property_lemmas                  false
% 1.07/1.03  --bmc1_k_induction                      false
% 1.07/1.03  --bmc1_non_equiv_states                 false
% 1.07/1.03  --bmc1_deadlock                         false
% 1.07/1.03  --bmc1_ucm                              false
% 1.07/1.03  --bmc1_add_unsat_core                   none
% 1.07/1.03  --bmc1_unsat_core_children              false
% 1.07/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.07/1.03  --bmc1_out_stat                         full
% 1.07/1.03  --bmc1_ground_init                      false
% 1.07/1.03  --bmc1_pre_inst_next_state              false
% 1.07/1.03  --bmc1_pre_inst_state                   false
% 1.07/1.03  --bmc1_pre_inst_reach_state             false
% 1.07/1.03  --bmc1_out_unsat_core                   false
% 1.07/1.03  --bmc1_aig_witness_out                  false
% 1.07/1.03  --bmc1_verbose                          false
% 1.07/1.03  --bmc1_dump_clauses_tptp                false
% 1.07/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.07/1.03  --bmc1_dump_file                        -
% 1.07/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.07/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.07/1.03  --bmc1_ucm_extend_mode                  1
% 1.07/1.03  --bmc1_ucm_init_mode                    2
% 1.07/1.03  --bmc1_ucm_cone_mode                    none
% 1.07/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.07/1.03  --bmc1_ucm_relax_model                  4
% 1.07/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.07/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.07/1.03  --bmc1_ucm_layered_model                none
% 1.07/1.03  --bmc1_ucm_max_lemma_size               10
% 1.07/1.03  
% 1.07/1.03  ------ AIG Options
% 1.07/1.03  
% 1.07/1.03  --aig_mode                              false
% 1.07/1.03  
% 1.07/1.03  ------ Instantiation Options
% 1.07/1.03  
% 1.07/1.03  --instantiation_flag                    true
% 1.07/1.03  --inst_sos_flag                         false
% 1.07/1.03  --inst_sos_phase                        true
% 1.07/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.07/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.07/1.03  --inst_lit_sel_side                     num_symb
% 1.07/1.03  --inst_solver_per_active                1400
% 1.07/1.03  --inst_solver_calls_frac                1.
% 1.07/1.03  --inst_passive_queue_type               priority_queues
% 1.07/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.07/1.03  --inst_passive_queues_freq              [25;2]
% 1.07/1.03  --inst_dismatching                      true
% 1.07/1.03  --inst_eager_unprocessed_to_passive     true
% 1.07/1.03  --inst_prop_sim_given                   true
% 1.07/1.03  --inst_prop_sim_new                     false
% 1.07/1.03  --inst_subs_new                         false
% 1.07/1.03  --inst_eq_res_simp                      false
% 1.07/1.03  --inst_subs_given                       false
% 1.07/1.03  --inst_orphan_elimination               true
% 1.07/1.03  --inst_learning_loop_flag               true
% 1.07/1.03  --inst_learning_start                   3000
% 1.07/1.03  --inst_learning_factor                  2
% 1.07/1.03  --inst_start_prop_sim_after_learn       3
% 1.07/1.03  --inst_sel_renew                        solver
% 1.07/1.03  --inst_lit_activity_flag                true
% 1.07/1.03  --inst_restr_to_given                   false
% 1.07/1.03  --inst_activity_threshold               500
% 1.07/1.03  --inst_out_proof                        true
% 1.07/1.03  
% 1.07/1.03  ------ Resolution Options
% 1.07/1.03  
% 1.07/1.03  --resolution_flag                       true
% 1.07/1.03  --res_lit_sel                           adaptive
% 1.07/1.03  --res_lit_sel_side                      none
% 1.07/1.03  --res_ordering                          kbo
% 1.07/1.03  --res_to_prop_solver                    active
% 1.07/1.03  --res_prop_simpl_new                    false
% 1.07/1.03  --res_prop_simpl_given                  true
% 1.07/1.03  --res_passive_queue_type                priority_queues
% 1.07/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.07/1.03  --res_passive_queues_freq               [15;5]
% 1.07/1.03  --res_forward_subs                      full
% 1.07/1.03  --res_backward_subs                     full
% 1.07/1.03  --res_forward_subs_resolution           true
% 1.07/1.03  --res_backward_subs_resolution          true
% 1.07/1.03  --res_orphan_elimination                true
% 1.07/1.03  --res_time_limit                        2.
% 1.07/1.03  --res_out_proof                         true
% 1.07/1.03  
% 1.07/1.03  ------ Superposition Options
% 1.07/1.03  
% 1.07/1.03  --superposition_flag                    true
% 1.07/1.03  --sup_passive_queue_type                priority_queues
% 1.07/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.07/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.07/1.03  --demod_completeness_check              fast
% 1.07/1.03  --demod_use_ground                      true
% 1.07/1.03  --sup_to_prop_solver                    passive
% 1.07/1.03  --sup_prop_simpl_new                    true
% 1.07/1.03  --sup_prop_simpl_given                  true
% 1.07/1.03  --sup_fun_splitting                     false
% 1.07/1.03  --sup_smt_interval                      50000
% 1.07/1.03  
% 1.07/1.03  ------ Superposition Simplification Setup
% 1.07/1.03  
% 1.07/1.03  --sup_indices_passive                   []
% 1.07/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.07/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.03  --sup_full_bw                           [BwDemod]
% 1.07/1.03  --sup_immed_triv                        [TrivRules]
% 1.07/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.07/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.03  --sup_immed_bw_main                     []
% 1.07/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.07/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.03  
% 1.07/1.03  ------ Combination Options
% 1.07/1.03  
% 1.07/1.03  --comb_res_mult                         3
% 1.07/1.03  --comb_sup_mult                         2
% 1.07/1.03  --comb_inst_mult                        10
% 1.07/1.03  
% 1.07/1.03  ------ Debug Options
% 1.07/1.03  
% 1.07/1.03  --dbg_backtrace                         false
% 1.07/1.03  --dbg_dump_prop_clauses                 false
% 1.07/1.03  --dbg_dump_prop_clauses_file            -
% 1.07/1.03  --dbg_out_stat                          false
% 1.07/1.03  ------ Parsing...
% 1.07/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.07/1.03  
% 1.07/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.07/1.03  
% 1.07/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.07/1.03  
% 1.07/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.07/1.03  ------ Proving...
% 1.07/1.03  ------ Problem Properties 
% 1.07/1.03  
% 1.07/1.03  
% 1.07/1.03  clauses                                 13
% 1.07/1.03  conjectures                             1
% 1.07/1.03  EPR                                     0
% 1.07/1.03  Horn                                    9
% 1.07/1.03  unary                                   4
% 1.07/1.03  binary                                  2
% 1.07/1.03  lits                                    34
% 1.07/1.03  lits eq                                 10
% 1.07/1.03  fd_pure                                 0
% 1.07/1.03  fd_pseudo                               0
% 1.07/1.03  fd_cond                                 1
% 1.07/1.03  fd_pseudo_cond                          3
% 1.07/1.03  AC symbols                              0
% 1.07/1.03  
% 1.07/1.03  ------ Schedule dynamic 5 is on 
% 1.07/1.03  
% 1.07/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.07/1.03  
% 1.07/1.03  
% 1.07/1.03  ------ 
% 1.07/1.03  Current options:
% 1.07/1.03  ------ 
% 1.07/1.03  
% 1.07/1.03  ------ Input Options
% 1.07/1.03  
% 1.07/1.03  --out_options                           all
% 1.07/1.03  --tptp_safe_out                         true
% 1.07/1.03  --problem_path                          ""
% 1.07/1.03  --include_path                          ""
% 1.07/1.03  --clausifier                            res/vclausify_rel
% 1.07/1.03  --clausifier_options                    --mode clausify
% 1.07/1.03  --stdin                                 false
% 1.07/1.03  --stats_out                             all
% 1.07/1.03  
% 1.07/1.03  ------ General Options
% 1.07/1.03  
% 1.07/1.03  --fof                                   false
% 1.07/1.03  --time_out_real                         305.
% 1.07/1.03  --time_out_virtual                      -1.
% 1.07/1.03  --symbol_type_check                     false
% 1.07/1.03  --clausify_out                          false
% 1.07/1.03  --sig_cnt_out                           false
% 1.07/1.03  --trig_cnt_out                          false
% 1.07/1.03  --trig_cnt_out_tolerance                1.
% 1.07/1.03  --trig_cnt_out_sk_spl                   false
% 1.07/1.03  --abstr_cl_out                          false
% 1.07/1.03  
% 1.07/1.03  ------ Global Options
% 1.07/1.03  
% 1.07/1.03  --schedule                              default
% 1.07/1.03  --add_important_lit                     false
% 1.07/1.03  --prop_solver_per_cl                    1000
% 1.07/1.03  --min_unsat_core                        false
% 1.07/1.03  --soft_assumptions                      false
% 1.07/1.03  --soft_lemma_size                       3
% 1.07/1.03  --prop_impl_unit_size                   0
% 1.07/1.03  --prop_impl_unit                        []
% 1.07/1.03  --share_sel_clauses                     true
% 1.07/1.03  --reset_solvers                         false
% 1.07/1.03  --bc_imp_inh                            [conj_cone]
% 1.07/1.03  --conj_cone_tolerance                   3.
% 1.07/1.03  --extra_neg_conj                        none
% 1.07/1.03  --large_theory_mode                     true
% 1.07/1.03  --prolific_symb_bound                   200
% 1.07/1.03  --lt_threshold                          2000
% 1.07/1.03  --clause_weak_htbl                      true
% 1.07/1.03  --gc_record_bc_elim                     false
% 1.07/1.03  
% 1.07/1.03  ------ Preprocessing Options
% 1.07/1.03  
% 1.07/1.03  --preprocessing_flag                    true
% 1.07/1.03  --time_out_prep_mult                    0.1
% 1.07/1.03  --splitting_mode                        input
% 1.07/1.03  --splitting_grd                         true
% 1.07/1.03  --splitting_cvd                         false
% 1.07/1.03  --splitting_cvd_svl                     false
% 1.07/1.03  --splitting_nvd                         32
% 1.07/1.03  --sub_typing                            true
% 1.07/1.03  --prep_gs_sim                           true
% 1.07/1.03  --prep_unflatten                        true
% 1.07/1.03  --prep_res_sim                          true
% 1.07/1.03  --prep_upred                            true
% 1.07/1.03  --prep_sem_filter                       exhaustive
% 1.07/1.03  --prep_sem_filter_out                   false
% 1.07/1.03  --pred_elim                             true
% 1.07/1.03  --res_sim_input                         true
% 1.07/1.03  --eq_ax_congr_red                       true
% 1.07/1.03  --pure_diseq_elim                       true
% 1.07/1.03  --brand_transform                       false
% 1.07/1.03  --non_eq_to_eq                          false
% 1.07/1.03  --prep_def_merge                        true
% 1.07/1.03  --prep_def_merge_prop_impl              false
% 1.07/1.03  --prep_def_merge_mbd                    true
% 1.07/1.03  --prep_def_merge_tr_red                 false
% 1.07/1.03  --prep_def_merge_tr_cl                  false
% 1.07/1.03  --smt_preprocessing                     true
% 1.07/1.03  --smt_ac_axioms                         fast
% 1.07/1.03  --preprocessed_out                      false
% 1.07/1.03  --preprocessed_stats                    false
% 1.07/1.03  
% 1.07/1.03  ------ Abstraction refinement Options
% 1.07/1.03  
% 1.07/1.03  --abstr_ref                             []
% 1.07/1.03  --abstr_ref_prep                        false
% 1.07/1.03  --abstr_ref_until_sat                   false
% 1.07/1.03  --abstr_ref_sig_restrict                funpre
% 1.07/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.07/1.03  --abstr_ref_under                       []
% 1.07/1.03  
% 1.07/1.03  ------ SAT Options
% 1.07/1.03  
% 1.07/1.03  --sat_mode                              false
% 1.07/1.03  --sat_fm_restart_options                ""
% 1.07/1.03  --sat_gr_def                            false
% 1.07/1.03  --sat_epr_types                         true
% 1.07/1.03  --sat_non_cyclic_types                  false
% 1.07/1.03  --sat_finite_models                     false
% 1.07/1.03  --sat_fm_lemmas                         false
% 1.07/1.03  --sat_fm_prep                           false
% 1.07/1.03  --sat_fm_uc_incr                        true
% 1.07/1.03  --sat_out_model                         small
% 1.07/1.03  --sat_out_clauses                       false
% 1.07/1.03  
% 1.07/1.03  ------ QBF Options
% 1.07/1.03  
% 1.07/1.03  --qbf_mode                              false
% 1.07/1.03  --qbf_elim_univ                         false
% 1.07/1.03  --qbf_dom_inst                          none
% 1.07/1.03  --qbf_dom_pre_inst                      false
% 1.07/1.03  --qbf_sk_in                             false
% 1.07/1.03  --qbf_pred_elim                         true
% 1.07/1.03  --qbf_split                             512
% 1.07/1.03  
% 1.07/1.03  ------ BMC1 Options
% 1.07/1.03  
% 1.07/1.03  --bmc1_incremental                      false
% 1.07/1.03  --bmc1_axioms                           reachable_all
% 1.07/1.03  --bmc1_min_bound                        0
% 1.07/1.03  --bmc1_max_bound                        -1
% 1.07/1.03  --bmc1_max_bound_default                -1
% 1.07/1.03  --bmc1_symbol_reachability              true
% 1.07/1.03  --bmc1_property_lemmas                  false
% 1.07/1.03  --bmc1_k_induction                      false
% 1.07/1.03  --bmc1_non_equiv_states                 false
% 1.07/1.03  --bmc1_deadlock                         false
% 1.07/1.03  --bmc1_ucm                              false
% 1.07/1.03  --bmc1_add_unsat_core                   none
% 1.07/1.03  --bmc1_unsat_core_children              false
% 1.07/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.07/1.03  --bmc1_out_stat                         full
% 1.07/1.03  --bmc1_ground_init                      false
% 1.07/1.03  --bmc1_pre_inst_next_state              false
% 1.07/1.03  --bmc1_pre_inst_state                   false
% 1.07/1.03  --bmc1_pre_inst_reach_state             false
% 1.07/1.03  --bmc1_out_unsat_core                   false
% 1.07/1.03  --bmc1_aig_witness_out                  false
% 1.07/1.03  --bmc1_verbose                          false
% 1.07/1.03  --bmc1_dump_clauses_tptp                false
% 1.07/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.07/1.03  --bmc1_dump_file                        -
% 1.07/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.07/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.07/1.03  --bmc1_ucm_extend_mode                  1
% 1.07/1.03  --bmc1_ucm_init_mode                    2
% 1.07/1.03  --bmc1_ucm_cone_mode                    none
% 1.07/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.07/1.03  --bmc1_ucm_relax_model                  4
% 1.07/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.07/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.07/1.03  --bmc1_ucm_layered_model                none
% 1.07/1.03  --bmc1_ucm_max_lemma_size               10
% 1.07/1.03  
% 1.07/1.03  ------ AIG Options
% 1.07/1.03  
% 1.07/1.03  --aig_mode                              false
% 1.07/1.03  
% 1.07/1.03  ------ Instantiation Options
% 1.07/1.03  
% 1.07/1.03  --instantiation_flag                    true
% 1.07/1.03  --inst_sos_flag                         false
% 1.07/1.03  --inst_sos_phase                        true
% 1.07/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.07/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.07/1.03  --inst_lit_sel_side                     none
% 1.07/1.03  --inst_solver_per_active                1400
% 1.07/1.03  --inst_solver_calls_frac                1.
% 1.07/1.03  --inst_passive_queue_type               priority_queues
% 1.07/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.07/1.03  --inst_passive_queues_freq              [25;2]
% 1.07/1.03  --inst_dismatching                      true
% 1.07/1.03  --inst_eager_unprocessed_to_passive     true
% 1.07/1.03  --inst_prop_sim_given                   true
% 1.07/1.03  --inst_prop_sim_new                     false
% 1.07/1.03  --inst_subs_new                         false
% 1.07/1.03  --inst_eq_res_simp                      false
% 1.07/1.03  --inst_subs_given                       false
% 1.07/1.03  --inst_orphan_elimination               true
% 1.07/1.03  --inst_learning_loop_flag               true
% 1.07/1.03  --inst_learning_start                   3000
% 1.07/1.03  --inst_learning_factor                  2
% 1.07/1.03  --inst_start_prop_sim_after_learn       3
% 1.07/1.03  --inst_sel_renew                        solver
% 1.07/1.03  --inst_lit_activity_flag                true
% 1.07/1.03  --inst_restr_to_given                   false
% 1.07/1.03  --inst_activity_threshold               500
% 1.07/1.03  --inst_out_proof                        true
% 1.07/1.03  
% 1.07/1.03  ------ Resolution Options
% 1.07/1.03  
% 1.07/1.03  --resolution_flag                       false
% 1.07/1.03  --res_lit_sel                           adaptive
% 1.07/1.03  --res_lit_sel_side                      none
% 1.07/1.03  --res_ordering                          kbo
% 1.07/1.03  --res_to_prop_solver                    active
% 1.07/1.03  --res_prop_simpl_new                    false
% 1.07/1.03  --res_prop_simpl_given                  true
% 1.07/1.03  --res_passive_queue_type                priority_queues
% 1.07/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.07/1.03  --res_passive_queues_freq               [15;5]
% 1.07/1.03  --res_forward_subs                      full
% 1.07/1.03  --res_backward_subs                     full
% 1.07/1.03  --res_forward_subs_resolution           true
% 1.07/1.03  --res_backward_subs_resolution          true
% 1.07/1.03  --res_orphan_elimination                true
% 1.07/1.03  --res_time_limit                        2.
% 1.07/1.03  --res_out_proof                         true
% 1.07/1.03  
% 1.07/1.03  ------ Superposition Options
% 1.07/1.03  
% 1.07/1.03  --superposition_flag                    true
% 1.07/1.03  --sup_passive_queue_type                priority_queues
% 1.07/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.07/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.07/1.03  --demod_completeness_check              fast
% 1.07/1.03  --demod_use_ground                      true
% 1.07/1.03  --sup_to_prop_solver                    passive
% 1.07/1.03  --sup_prop_simpl_new                    true
% 1.07/1.03  --sup_prop_simpl_given                  true
% 1.07/1.03  --sup_fun_splitting                     false
% 1.07/1.03  --sup_smt_interval                      50000
% 1.07/1.03  
% 1.07/1.03  ------ Superposition Simplification Setup
% 1.07/1.03  
% 1.07/1.03  --sup_indices_passive                   []
% 1.07/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.07/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.07/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.03  --sup_full_bw                           [BwDemod]
% 1.07/1.03  --sup_immed_triv                        [TrivRules]
% 1.07/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.07/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.03  --sup_immed_bw_main                     []
% 1.07/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.07/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.07/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.07/1.03  
% 1.07/1.03  ------ Combination Options
% 1.07/1.03  
% 1.07/1.03  --comb_res_mult                         3
% 1.07/1.03  --comb_sup_mult                         2
% 1.07/1.03  --comb_inst_mult                        10
% 1.07/1.03  
% 1.07/1.03  ------ Debug Options
% 1.07/1.03  
% 1.07/1.03  --dbg_backtrace                         false
% 1.07/1.03  --dbg_dump_prop_clauses                 false
% 1.07/1.03  --dbg_dump_prop_clauses_file            -
% 1.07/1.03  --dbg_out_stat                          false
% 1.07/1.03  
% 1.07/1.03  
% 1.07/1.03  
% 1.07/1.03  
% 1.07/1.03  ------ Proving...
% 1.07/1.03  
% 1.07/1.03  
% 1.07/1.03  % SZS status Theorem for theBenchmark.p
% 1.07/1.03  
% 1.07/1.03   Resolution empty clause
% 1.07/1.03  
% 1.07/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.07/1.03  
% 1.07/1.03  fof(f3,axiom,(
% 1.07/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 1.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f8,plain,(
% 1.07/1.03    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 1.07/1.03    inference(ennf_transformation,[],[f3])).
% 1.07/1.03  
% 1.07/1.03  fof(f13,plain,(
% 1.07/1.03    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.07/1.03    inference(nnf_transformation,[],[f8])).
% 1.07/1.03  
% 1.07/1.03  fof(f14,plain,(
% 1.07/1.03    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.07/1.03    inference(rectify,[],[f13])).
% 1.07/1.03  
% 1.07/1.03  fof(f17,plain,(
% 1.07/1.03    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)))),
% 1.07/1.03    introduced(choice_axiom,[])).
% 1.07/1.03  
% 1.07/1.03  fof(f16,plain,(
% 1.07/1.03    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X3),X0)))) )),
% 1.07/1.03    introduced(choice_axiom,[])).
% 1.07/1.03  
% 1.07/1.03  fof(f15,plain,(
% 1.07/1.03    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK0(X0,X1,X2)),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.07/1.03    introduced(choice_axiom,[])).
% 1.07/1.03  
% 1.07/1.03  fof(f18,plain,(
% 1.07/1.03    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK0(X0,X1,X2)),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.07/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f17,f16,f15])).
% 1.07/1.03  
% 1.07/1.03  fof(f30,plain,(
% 1.07/1.03    ( ! [X2,X0,X1] : (k9_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0) | r2_hidden(sK0(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 1.07/1.03    inference(cnf_transformation,[],[f18])).
% 1.07/1.03  
% 1.07/1.03  fof(f1,axiom,(
% 1.07/1.03    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f11,plain,(
% 1.07/1.03    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.07/1.03    inference(nnf_transformation,[],[f1])).
% 1.07/1.03  
% 1.07/1.03  fof(f12,plain,(
% 1.07/1.03    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.07/1.03    inference(flattening,[],[f11])).
% 1.07/1.03  
% 1.07/1.03  fof(f25,plain,(
% 1.07/1.03    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.07/1.03    inference(cnf_transformation,[],[f12])).
% 1.07/1.03  
% 1.07/1.03  fof(f36,plain,(
% 1.07/1.03    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 1.07/1.03    inference(equality_resolution,[],[f25])).
% 1.07/1.03  
% 1.07/1.03  fof(f2,axiom,(
% 1.07/1.03    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f26,plain,(
% 1.07/1.03    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.07/1.03    inference(cnf_transformation,[],[f2])).
% 1.07/1.03  
% 1.07/1.03  fof(f4,axiom,(
% 1.07/1.03    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f7,plain,(
% 1.07/1.03    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 1.07/1.03    inference(unused_predicate_definition_removal,[],[f4])).
% 1.07/1.03  
% 1.07/1.03  fof(f9,plain,(
% 1.07/1.03    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.07/1.03    inference(ennf_transformation,[],[f7])).
% 1.07/1.03  
% 1.07/1.03  fof(f19,plain,(
% 1.07/1.03    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0)))),
% 1.07/1.03    introduced(choice_axiom,[])).
% 1.07/1.03  
% 1.07/1.03  fof(f20,plain,(
% 1.07/1.03    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK3(X0) & r2_hidden(sK3(X0),X0)))),
% 1.07/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f9,f19])).
% 1.07/1.03  
% 1.07/1.03  fof(f33,plain,(
% 1.07/1.03    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.07/1.03    inference(cnf_transformation,[],[f20])).
% 1.07/1.03  
% 1.07/1.03  fof(f5,conjecture,(
% 1.07/1.03    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.07/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.07/1.03  
% 1.07/1.03  fof(f6,negated_conjecture,(
% 1.07/1.03    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 1.07/1.03    inference(negated_conjecture,[],[f5])).
% 1.07/1.03  
% 1.07/1.03  fof(f10,plain,(
% 1.07/1.03    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 1.07/1.03    inference(ennf_transformation,[],[f6])).
% 1.07/1.03  
% 1.07/1.03  fof(f21,plain,(
% 1.07/1.03    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK4)),
% 1.07/1.03    introduced(choice_axiom,[])).
% 1.07/1.03  
% 1.07/1.03  fof(f22,plain,(
% 1.07/1.03    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK4)),
% 1.07/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f10,f21])).
% 1.07/1.03  
% 1.07/1.03  fof(f35,plain,(
% 1.07/1.03    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK4)),
% 1.07/1.03    inference(cnf_transformation,[],[f22])).
% 1.07/1.03  
% 1.07/1.03  cnf(c_6,plain,
% 1.07/1.03      ( r2_hidden(sK0(X0,X1,X2),X2)
% 1.07/1.03      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0)
% 1.07/1.03      | ~ v1_relat_1(X0)
% 1.07/1.03      | k9_relat_1(X0,X1) = X2 ),
% 1.07/1.03      inference(cnf_transformation,[],[f30]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_527,plain,
% 1.07/1.03      ( k9_relat_1(X0,X1) = X2
% 1.07/1.03      | r2_hidden(sK0(X0,X1,X2),X2) = iProver_top
% 1.07/1.03      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK0(X0,X1,X2)),X0) = iProver_top
% 1.07/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_0,plain,
% 1.07/1.03      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 1.07/1.03      inference(cnf_transformation,[],[f36]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_3,plain,
% 1.07/1.03      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 1.07/1.03      inference(cnf_transformation,[],[f26]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_530,plain,
% 1.07/1.03      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_633,plain,
% 1.07/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.07/1.03      inference(superposition,[status(thm)],[c_0,c_530]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_1282,plain,
% 1.07/1.03      ( k9_relat_1(k1_xboole_0,X0) = X1
% 1.07/1.03      | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top
% 1.07/1.03      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 1.07/1.03      inference(superposition,[status(thm)],[c_527,c_633]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_11,plain,
% 1.07/1.03      ( r2_hidden(sK3(X0),X0) | v1_relat_1(X0) ),
% 1.07/1.03      inference(cnf_transformation,[],[f33]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_522,plain,
% 1.07/1.03      ( r2_hidden(sK3(X0),X0) = iProver_top | v1_relat_1(X0) = iProver_top ),
% 1.07/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_870,plain,
% 1.07/1.03      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 1.07/1.03      inference(superposition,[status(thm)],[c_522,c_633]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_2527,plain,
% 1.07/1.03      ( r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top
% 1.07/1.03      | k9_relat_1(k1_xboole_0,X0) = X1 ),
% 1.07/1.03      inference(global_propositional_subsumption,[status(thm)],[c_1282,c_870]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_2528,plain,
% 1.07/1.03      ( k9_relat_1(k1_xboole_0,X0) = X1
% 1.07/1.03      | r2_hidden(sK0(k1_xboole_0,X0,X1),X1) = iProver_top ),
% 1.07/1.03      inference(renaming,[status(thm)],[c_2527]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_2535,plain,
% 1.07/1.03      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.07/1.03      inference(superposition,[status(thm)],[c_2528,c_633]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_12,negated_conjecture,
% 1.07/1.03      ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK4) ),
% 1.07/1.03      inference(cnf_transformation,[],[f35]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_2606,plain,
% 1.07/1.03      ( k1_xboole_0 != k1_xboole_0 ),
% 1.07/1.03      inference(demodulation,[status(thm)],[c_2535,c_12]) ).
% 1.07/1.03  
% 1.07/1.03  cnf(c_2633,plain,
% 1.07/1.03      ( $false ),
% 1.07/1.03      inference(equality_resolution_simp,[status(thm)],[c_2606]) ).
% 1.07/1.03  
% 1.07/1.03  
% 1.07/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.07/1.03  
% 1.07/1.03  ------                               Statistics
% 1.07/1.03  
% 1.07/1.03  ------ General
% 1.07/1.03  
% 1.07/1.03  abstr_ref_over_cycles:                  0
% 1.07/1.03  abstr_ref_under_cycles:                 0
% 1.07/1.03  gc_basic_clause_elim:                   0
% 1.07/1.03  forced_gc_time:                         0
% 1.07/1.03  parsing_time:                           0.011
% 1.07/1.03  unif_index_cands_time:                  0.
% 1.07/1.03  unif_index_add_time:                    0.
% 1.07/1.03  orderings_time:                         0.
% 1.07/1.03  out_proof_time:                         0.022
% 1.07/1.03  total_time:                             0.16
% 1.07/1.03  num_of_symbols:                         42
% 1.07/1.03  num_of_terms:                           3315
% 1.07/1.03  
% 1.07/1.03  ------ Preprocessing
% 1.07/1.03  
% 1.07/1.03  num_of_splits:                          0
% 1.07/1.03  num_of_split_atoms:                     0
% 1.07/1.03  num_of_reused_defs:                     0
% 1.07/1.03  num_eq_ax_congr_red:                    22
% 1.07/1.03  num_of_sem_filtered_clauses:            1
% 1.07/1.03  num_of_subtypes:                        0
% 1.07/1.03  monotx_restored_types:                  0
% 1.07/1.03  sat_num_of_epr_types:                   0
% 1.07/1.03  sat_num_of_non_cyclic_types:            0
% 1.07/1.03  sat_guarded_non_collapsed_types:        0
% 1.07/1.03  num_pure_diseq_elim:                    0
% 1.07/1.03  simp_replaced_by:                       0
% 1.07/1.03  res_preprocessed:                       52
% 1.07/1.03  prep_upred:                             0
% 1.07/1.03  prep_unflattend:                        8
% 1.07/1.03  smt_new_axioms:                         0
% 1.07/1.03  pred_elim_cands:                        2
% 1.07/1.03  pred_elim:                              0
% 1.07/1.03  pred_elim_cl:                           0
% 1.07/1.03  pred_elim_cycles:                       1
% 1.07/1.03  merged_defs:                            0
% 1.07/1.03  merged_defs_ncl:                        0
% 1.07/1.03  bin_hyper_res:                          0
% 1.07/1.03  prep_cycles:                            3
% 1.07/1.03  pred_elim_time:                         0.006
% 1.07/1.03  splitting_time:                         0.
% 1.07/1.03  sem_filter_time:                        0.
% 1.07/1.03  monotx_time:                            0.001
% 1.07/1.03  subtype_inf_time:                       0.
% 1.07/1.03  
% 1.07/1.03  ------ Problem properties
% 1.07/1.03  
% 1.07/1.03  clauses:                                13
% 1.07/1.03  conjectures:                            1
% 1.07/1.03  epr:                                    0
% 1.07/1.03  horn:                                   9
% 1.07/1.03  ground:                                 1
% 1.07/1.03  unary:                                  4
% 1.07/1.03  binary:                                 2
% 1.07/1.03  lits:                                   34
% 1.07/1.03  lits_eq:                                10
% 1.07/1.03  fd_pure:                                0
% 1.07/1.03  fd_pseudo:                              0
% 1.07/1.03  fd_cond:                                1
% 1.07/1.03  fd_pseudo_cond:                         3
% 1.07/1.03  ac_symbols:                             0
% 1.07/1.03  
% 1.07/1.03  ------ Propositional Solver
% 1.07/1.03  
% 1.07/1.03  prop_solver_calls:                      26
% 1.07/1.03  prop_fast_solver_calls:                 397
% 1.07/1.03  smt_solver_calls:                       0
% 1.07/1.03  smt_fast_solver_calls:                  0
% 1.07/1.03  prop_num_of_clauses:                    950
% 1.07/1.03  prop_preprocess_simplified:             2755
% 1.07/1.03  prop_fo_subsumed:                       2
% 1.07/1.03  prop_solver_time:                       0.
% 1.07/1.03  smt_solver_time:                        0.
% 1.07/1.03  smt_fast_solver_time:                   0.
% 1.07/1.03  prop_fast_solver_time:                  0.
% 1.07/1.03  prop_unsat_core_time:                   0.
% 1.07/1.03  
% 1.07/1.03  ------ QBF
% 1.07/1.03  
% 1.07/1.03  qbf_q_res:                              0
% 1.07/1.03  qbf_num_tautologies:                    0
% 1.07/1.03  qbf_prep_cycles:                        0
% 1.07/1.03  
% 1.07/1.03  ------ BMC1
% 1.07/1.03  
% 1.07/1.03  bmc1_current_bound:                     -1
% 1.07/1.03  bmc1_last_solved_bound:                 -1
% 1.07/1.03  bmc1_unsat_core_size:                   -1
% 1.07/1.03  bmc1_unsat_core_parents_size:           -1
% 1.07/1.03  bmc1_merge_next_fun:                    0
% 1.07/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.07/1.03  
% 1.07/1.03  ------ Instantiation
% 1.07/1.03  
% 1.07/1.03  inst_num_of_clauses:                    377
% 1.07/1.03  inst_num_in_passive:                    179
% 1.07/1.03  inst_num_in_active:                     176
% 1.07/1.03  inst_num_in_unprocessed:                22
% 1.07/1.03  inst_num_of_loops:                      190
% 1.07/1.03  inst_num_of_learning_restarts:          0
% 1.07/1.03  inst_num_moves_active_passive:          10
% 1.07/1.03  inst_lit_activity:                      0
% 1.07/1.03  inst_lit_activity_moves:                0
% 1.07/1.03  inst_num_tautologies:                   0
% 1.07/1.03  inst_num_prop_implied:                  0
% 1.07/1.03  inst_num_existing_simplified:           0
% 1.07/1.03  inst_num_eq_res_simplified:             0
% 1.07/1.03  inst_num_child_elim:                    0
% 1.07/1.03  inst_num_of_dismatching_blockings:      72
% 1.07/1.03  inst_num_of_non_proper_insts:           304
% 1.07/1.03  inst_num_of_duplicates:                 0
% 1.07/1.03  inst_inst_num_from_inst_to_res:         0
% 1.07/1.03  inst_dismatching_checking_time:         0.
% 1.07/1.03  
% 1.07/1.03  ------ Resolution
% 1.07/1.03  
% 1.07/1.03  res_num_of_clauses:                     0
% 1.07/1.03  res_num_in_passive:                     0
% 1.07/1.03  res_num_in_active:                      0
% 1.07/1.03  res_num_of_loops:                       55
% 1.07/1.03  res_forward_subset_subsumed:            48
% 1.07/1.03  res_backward_subset_subsumed:           0
% 1.07/1.03  res_forward_subsumed:                   0
% 1.07/1.03  res_backward_subsumed:                  0
% 1.07/1.03  res_forward_subsumption_resolution:     0
% 1.07/1.03  res_backward_subsumption_resolution:    0
% 1.07/1.03  res_clause_to_clause_subsumption:       298
% 1.07/1.03  res_orphan_elimination:                 0
% 1.07/1.03  res_tautology_del:                      31
% 1.07/1.03  res_num_eq_res_simplified:              0
% 1.07/1.03  res_num_sel_changes:                    0
% 1.07/1.03  res_moves_from_active_to_pass:          0
% 1.07/1.03  
% 1.07/1.03  ------ Superposition
% 1.07/1.03  
% 1.07/1.03  sup_time_total:                         0.
% 1.07/1.03  sup_time_generating:                    0.
% 1.07/1.03  sup_time_sim_full:                      0.
% 1.07/1.03  sup_time_sim_immed:                     0.
% 1.07/1.03  
% 1.07/1.03  sup_num_of_clauses:                     72
% 1.07/1.03  sup_num_in_active:                      17
% 1.07/1.03  sup_num_in_passive:                     55
% 1.07/1.03  sup_num_of_loops:                       37
% 1.07/1.03  sup_fw_superposition:                   59
% 1.07/1.03  sup_bw_superposition:                   33
% 1.07/1.03  sup_immediate_simplified:               18
% 1.07/1.03  sup_given_eliminated:                   1
% 1.07/1.03  comparisons_done:                       0
% 1.07/1.03  comparisons_avoided:                    0
% 1.07/1.03  
% 1.07/1.03  ------ Simplifications
% 1.07/1.03  
% 1.07/1.03  
% 1.07/1.03  sim_fw_subset_subsumed:                 0
% 1.07/1.03  sim_bw_subset_subsumed:                 0
% 1.07/1.03  sim_fw_subsumed:                        0
% 1.07/1.03  sim_bw_subsumed:                        1
% 1.07/1.03  sim_fw_subsumption_res:                 17
% 1.07/1.03  sim_bw_subsumption_res:                 0
% 1.07/1.03  sim_tautology_del:                      1
% 1.07/1.03  sim_eq_tautology_del:                   1
% 1.07/1.03  sim_eq_res_simp:                        0
% 1.07/1.03  sim_fw_demodulated:                     0
% 1.07/1.03  sim_bw_demodulated:                     31
% 1.07/1.03  sim_light_normalised:                   0
% 1.07/1.03  sim_joinable_taut:                      0
% 1.07/1.03  sim_joinable_simp:                      0
% 1.07/1.03  sim_ac_normalised:                      0
% 1.07/1.03  sim_smt_subsumption:                    0
% 1.07/1.03  
%------------------------------------------------------------------------------
