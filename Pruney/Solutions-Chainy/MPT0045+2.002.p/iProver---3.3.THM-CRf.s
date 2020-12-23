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
% DateTime   : Thu Dec  3 11:22:35 EST 2020

% Result     : Theorem 0.92s
% Output     : CNFRefutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   47 (  52 expanded)
%              Number of clauses        :   16 (  16 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :   10
%              Number of atoms          :  169 ( 181 expanded)
%              Number of equality atoms :   28 (  34 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k4_xboole_0(X1,X0))
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != X0
      & r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 != X0
        & r1_tarski(X0,k4_xboole_0(X1,X0)) )
   => ( k1_xboole_0 != sK4
      & r1_tarski(sK4,k4_xboole_0(sK5,sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k1_xboole_0 != sK4
    & r1_tarski(sK4,k4_xboole_0(sK5,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f20,f33])).

fof(f52,plain,(
    r1_tarski(sK4,k4_xboole_0(sK5,sK4)) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f21])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK1(X0,X1),X1)
          | ~ r2_hidden(sK1(X0,X1),X0) )
        & ( r2_hidden(sK1(X0,X1),X1)
          | r2_hidden(sK1(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(sK1(X0,X1),X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f53,plain,(
    k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_8,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_191,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_192,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_191])).

cnf(c_910,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK4),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_192])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_18,negated_conjecture,
    ( r1_tarski(sK4,k4_xboole_0(sK5,sK4)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_202,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | k4_xboole_0(sK5,sK4) != X2
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_18])).

cnf(c_203,plain,
    ( r2_hidden(X0,k4_xboole_0(sK5,sK4))
    | ~ r2_hidden(X0,sK4) ),
    inference(unflattening,[status(thm)],[c_202])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_211,plain,
    ( ~ r2_hidden(X0,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_203,c_6])).

cnf(c_877,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_211])).

cnf(c_10,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | r2_hidden(sK1(X0,X1),X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_853,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK4),sK4)
    | r2_hidden(sK1(k1_xboole_0,sK4),k1_xboole_0)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_17,negated_conjecture,
    ( k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f53])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_910,c_877,c_853,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:32:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.92/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.92/0.99  
% 0.92/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.92/0.99  
% 0.92/0.99  ------  iProver source info
% 0.92/0.99  
% 0.92/0.99  git: date: 2020-06-30 10:37:57 +0100
% 0.92/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.92/0.99  git: non_committed_changes: false
% 0.92/0.99  git: last_make_outside_of_git: false
% 0.92/0.99  
% 0.92/0.99  ------ 
% 0.92/0.99  
% 0.92/0.99  ------ Input Options
% 0.92/0.99  
% 0.92/0.99  --out_options                           all
% 0.92/0.99  --tptp_safe_out                         true
% 0.92/0.99  --problem_path                          ""
% 0.92/0.99  --include_path                          ""
% 0.92/0.99  --clausifier                            res/vclausify_rel
% 0.92/0.99  --clausifier_options                    --mode clausify
% 0.92/0.99  --stdin                                 false
% 0.92/0.99  --stats_out                             all
% 0.92/0.99  
% 0.92/0.99  ------ General Options
% 0.92/0.99  
% 0.92/0.99  --fof                                   false
% 0.92/0.99  --time_out_real                         305.
% 0.92/0.99  --time_out_virtual                      -1.
% 0.92/0.99  --symbol_type_check                     false
% 0.92/0.99  --clausify_out                          false
% 0.92/0.99  --sig_cnt_out                           false
% 0.92/0.99  --trig_cnt_out                          false
% 0.92/0.99  --trig_cnt_out_tolerance                1.
% 0.92/0.99  --trig_cnt_out_sk_spl                   false
% 0.92/0.99  --abstr_cl_out                          false
% 0.92/0.99  
% 0.92/0.99  ------ Global Options
% 0.92/0.99  
% 0.92/0.99  --schedule                              default
% 0.92/0.99  --add_important_lit                     false
% 0.92/0.99  --prop_solver_per_cl                    1000
% 0.92/0.99  --min_unsat_core                        false
% 0.92/0.99  --soft_assumptions                      false
% 0.92/0.99  --soft_lemma_size                       3
% 0.92/0.99  --prop_impl_unit_size                   0
% 0.92/0.99  --prop_impl_unit                        []
% 0.92/0.99  --share_sel_clauses                     true
% 0.92/0.99  --reset_solvers                         false
% 0.92/0.99  --bc_imp_inh                            [conj_cone]
% 0.92/0.99  --conj_cone_tolerance                   3.
% 0.92/0.99  --extra_neg_conj                        none
% 0.92/0.99  --large_theory_mode                     true
% 0.92/0.99  --prolific_symb_bound                   200
% 0.92/0.99  --lt_threshold                          2000
% 0.92/0.99  --clause_weak_htbl                      true
% 0.92/0.99  --gc_record_bc_elim                     false
% 0.92/0.99  
% 0.92/0.99  ------ Preprocessing Options
% 0.92/0.99  
% 0.92/0.99  --preprocessing_flag                    true
% 0.92/0.99  --time_out_prep_mult                    0.1
% 0.92/0.99  --splitting_mode                        input
% 0.92/0.99  --splitting_grd                         true
% 0.92/0.99  --splitting_cvd                         false
% 0.92/0.99  --splitting_cvd_svl                     false
% 0.92/0.99  --splitting_nvd                         32
% 0.92/0.99  --sub_typing                            true
% 0.92/0.99  --prep_gs_sim                           true
% 0.92/0.99  --prep_unflatten                        true
% 0.92/0.99  --prep_res_sim                          true
% 0.92/0.99  --prep_upred                            true
% 0.92/0.99  --prep_sem_filter                       exhaustive
% 0.92/0.99  --prep_sem_filter_out                   false
% 0.92/0.99  --pred_elim                             true
% 0.92/0.99  --res_sim_input                         true
% 0.92/0.99  --eq_ax_congr_red                       true
% 0.92/0.99  --pure_diseq_elim                       true
% 0.92/0.99  --brand_transform                       false
% 0.92/0.99  --non_eq_to_eq                          false
% 0.92/0.99  --prep_def_merge                        true
% 0.92/0.99  --prep_def_merge_prop_impl              false
% 0.92/0.99  --prep_def_merge_mbd                    true
% 0.92/0.99  --prep_def_merge_tr_red                 false
% 0.92/0.99  --prep_def_merge_tr_cl                  false
% 0.92/0.99  --smt_preprocessing                     true
% 0.92/0.99  --smt_ac_axioms                         fast
% 0.92/0.99  --preprocessed_out                      false
% 0.92/0.99  --preprocessed_stats                    false
% 0.92/0.99  
% 0.92/0.99  ------ Abstraction refinement Options
% 0.92/0.99  
% 0.92/0.99  --abstr_ref                             []
% 0.92/0.99  --abstr_ref_prep                        false
% 0.92/0.99  --abstr_ref_until_sat                   false
% 0.92/0.99  --abstr_ref_sig_restrict                funpre
% 0.92/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.92/0.99  --abstr_ref_under                       []
% 0.92/0.99  
% 0.92/0.99  ------ SAT Options
% 0.92/0.99  
% 0.92/0.99  --sat_mode                              false
% 0.92/0.99  --sat_fm_restart_options                ""
% 0.92/0.99  --sat_gr_def                            false
% 0.92/0.99  --sat_epr_types                         true
% 0.92/0.99  --sat_non_cyclic_types                  false
% 0.92/0.99  --sat_finite_models                     false
% 0.92/0.99  --sat_fm_lemmas                         false
% 0.92/0.99  --sat_fm_prep                           false
% 0.92/0.99  --sat_fm_uc_incr                        true
% 0.92/0.99  --sat_out_model                         small
% 0.92/0.99  --sat_out_clauses                       false
% 0.92/0.99  
% 0.92/0.99  ------ QBF Options
% 0.92/0.99  
% 0.92/0.99  --qbf_mode                              false
% 0.92/0.99  --qbf_elim_univ                         false
% 0.92/0.99  --qbf_dom_inst                          none
% 0.92/0.99  --qbf_dom_pre_inst                      false
% 0.92/0.99  --qbf_sk_in                             false
% 0.92/0.99  --qbf_pred_elim                         true
% 0.92/0.99  --qbf_split                             512
% 0.92/0.99  
% 0.92/0.99  ------ BMC1 Options
% 0.92/0.99  
% 0.92/0.99  --bmc1_incremental                      false
% 0.92/0.99  --bmc1_axioms                           reachable_all
% 0.92/0.99  --bmc1_min_bound                        0
% 0.92/0.99  --bmc1_max_bound                        -1
% 0.92/0.99  --bmc1_max_bound_default                -1
% 0.92/0.99  --bmc1_symbol_reachability              true
% 0.92/0.99  --bmc1_property_lemmas                  false
% 0.92/0.99  --bmc1_k_induction                      false
% 0.92/0.99  --bmc1_non_equiv_states                 false
% 0.92/0.99  --bmc1_deadlock                         false
% 0.92/0.99  --bmc1_ucm                              false
% 0.92/0.99  --bmc1_add_unsat_core                   none
% 0.92/0.99  --bmc1_unsat_core_children              false
% 0.92/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.92/0.99  --bmc1_out_stat                         full
% 0.92/0.99  --bmc1_ground_init                      false
% 0.92/0.99  --bmc1_pre_inst_next_state              false
% 0.92/0.99  --bmc1_pre_inst_state                   false
% 0.92/0.99  --bmc1_pre_inst_reach_state             false
% 0.92/0.99  --bmc1_out_unsat_core                   false
% 0.92/0.99  --bmc1_aig_witness_out                  false
% 0.92/0.99  --bmc1_verbose                          false
% 0.92/0.99  --bmc1_dump_clauses_tptp                false
% 0.92/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.92/0.99  --bmc1_dump_file                        -
% 0.92/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.92/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.92/0.99  --bmc1_ucm_extend_mode                  1
% 0.92/0.99  --bmc1_ucm_init_mode                    2
% 0.92/0.99  --bmc1_ucm_cone_mode                    none
% 0.92/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.92/0.99  --bmc1_ucm_relax_model                  4
% 0.92/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.92/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.92/0.99  --bmc1_ucm_layered_model                none
% 0.92/0.99  --bmc1_ucm_max_lemma_size               10
% 0.92/0.99  
% 0.92/0.99  ------ AIG Options
% 0.92/0.99  
% 0.92/0.99  --aig_mode                              false
% 0.92/0.99  
% 0.92/0.99  ------ Instantiation Options
% 0.92/0.99  
% 0.92/0.99  --instantiation_flag                    true
% 0.92/0.99  --inst_sos_flag                         false
% 0.92/0.99  --inst_sos_phase                        true
% 0.92/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.92/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.92/0.99  --inst_lit_sel_side                     num_symb
% 0.92/0.99  --inst_solver_per_active                1400
% 0.92/0.99  --inst_solver_calls_frac                1.
% 0.92/0.99  --inst_passive_queue_type               priority_queues
% 0.92/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.92/0.99  --inst_passive_queues_freq              [25;2]
% 0.92/0.99  --inst_dismatching                      true
% 0.92/0.99  --inst_eager_unprocessed_to_passive     true
% 0.92/0.99  --inst_prop_sim_given                   true
% 0.92/0.99  --inst_prop_sim_new                     false
% 0.92/0.99  --inst_subs_new                         false
% 0.92/0.99  --inst_eq_res_simp                      false
% 0.92/0.99  --inst_subs_given                       false
% 0.92/0.99  --inst_orphan_elimination               true
% 0.92/0.99  --inst_learning_loop_flag               true
% 0.92/0.99  --inst_learning_start                   3000
% 0.92/0.99  --inst_learning_factor                  2
% 0.92/0.99  --inst_start_prop_sim_after_learn       3
% 0.92/0.99  --inst_sel_renew                        solver
% 0.92/0.99  --inst_lit_activity_flag                true
% 0.92/0.99  --inst_restr_to_given                   false
% 0.92/0.99  --inst_activity_threshold               500
% 0.92/0.99  --inst_out_proof                        true
% 0.92/0.99  
% 0.92/0.99  ------ Resolution Options
% 0.92/0.99  
% 0.92/0.99  --resolution_flag                       true
% 0.92/0.99  --res_lit_sel                           adaptive
% 0.92/0.99  --res_lit_sel_side                      none
% 0.92/0.99  --res_ordering                          kbo
% 0.92/0.99  --res_to_prop_solver                    active
% 0.92/0.99  --res_prop_simpl_new                    false
% 0.92/0.99  --res_prop_simpl_given                  true
% 0.92/0.99  --res_passive_queue_type                priority_queues
% 0.92/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.92/0.99  --res_passive_queues_freq               [15;5]
% 0.92/0.99  --res_forward_subs                      full
% 0.92/0.99  --res_backward_subs                     full
% 0.92/0.99  --res_forward_subs_resolution           true
% 0.92/0.99  --res_backward_subs_resolution          true
% 0.92/0.99  --res_orphan_elimination                true
% 0.92/0.99  --res_time_limit                        2.
% 0.92/0.99  --res_out_proof                         true
% 0.92/0.99  
% 0.92/0.99  ------ Superposition Options
% 0.92/0.99  
% 0.92/0.99  --superposition_flag                    true
% 0.92/0.99  --sup_passive_queue_type                priority_queues
% 0.92/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.92/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.92/0.99  --demod_completeness_check              fast
% 0.92/0.99  --demod_use_ground                      true
% 0.92/0.99  --sup_to_prop_solver                    passive
% 0.92/0.99  --sup_prop_simpl_new                    true
% 0.92/0.99  --sup_prop_simpl_given                  true
% 0.92/0.99  --sup_fun_splitting                     false
% 0.92/0.99  --sup_smt_interval                      50000
% 0.92/0.99  
% 0.92/0.99  ------ Superposition Simplification Setup
% 0.92/0.99  
% 0.92/0.99  --sup_indices_passive                   []
% 0.92/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.92/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/0.99  --sup_full_bw                           [BwDemod]
% 0.92/0.99  --sup_immed_triv                        [TrivRules]
% 0.92/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.92/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/0.99  --sup_immed_bw_main                     []
% 0.92/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.92/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.92/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.92/0.99  
% 0.92/0.99  ------ Combination Options
% 0.92/0.99  
% 0.92/0.99  --comb_res_mult                         3
% 0.92/0.99  --comb_sup_mult                         2
% 0.92/0.99  --comb_inst_mult                        10
% 0.92/0.99  
% 0.92/0.99  ------ Debug Options
% 0.92/0.99  
% 0.92/0.99  --dbg_backtrace                         false
% 0.92/0.99  --dbg_dump_prop_clauses                 false
% 0.92/0.99  --dbg_dump_prop_clauses_file            -
% 0.92/0.99  --dbg_out_stat                          false
% 0.92/0.99  ------ Parsing...
% 0.92/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.92/0.99  
% 0.92/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.92/0.99  
% 0.92/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.92/0.99  
% 0.92/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.92/0.99  ------ Proving...
% 0.92/0.99  ------ Problem Properties 
% 0.92/0.99  
% 0.92/0.99  
% 0.92/0.99  clauses                                 17
% 0.92/0.99  conjectures                             1
% 0.92/0.99  EPR                                     4
% 0.92/0.99  Horn                                    9
% 0.92/0.99  unary                                   4
% 0.92/0.99  binary                                  6
% 0.92/0.99  lits                                    38
% 0.92/0.99  lits eq                                 7
% 0.92/0.99  fd_pure                                 0
% 0.92/0.99  fd_pseudo                               0
% 0.92/0.99  fd_cond                                 0
% 0.92/0.99  fd_pseudo_cond                          5
% 0.92/0.99  AC symbols                              0
% 0.92/0.99  
% 0.92/0.99  ------ Schedule dynamic 5 is on 
% 0.92/0.99  
% 0.92/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.92/0.99  
% 0.92/0.99  
% 0.92/0.99  ------ 
% 0.92/0.99  Current options:
% 0.92/0.99  ------ 
% 0.92/0.99  
% 0.92/0.99  ------ Input Options
% 0.92/0.99  
% 0.92/0.99  --out_options                           all
% 0.92/0.99  --tptp_safe_out                         true
% 0.92/0.99  --problem_path                          ""
% 0.92/0.99  --include_path                          ""
% 0.92/0.99  --clausifier                            res/vclausify_rel
% 0.92/0.99  --clausifier_options                    --mode clausify
% 0.92/0.99  --stdin                                 false
% 0.92/0.99  --stats_out                             all
% 0.92/0.99  
% 0.92/0.99  ------ General Options
% 0.92/0.99  
% 0.92/0.99  --fof                                   false
% 0.92/0.99  --time_out_real                         305.
% 0.92/0.99  --time_out_virtual                      -1.
% 0.92/0.99  --symbol_type_check                     false
% 0.92/0.99  --clausify_out                          false
% 0.92/0.99  --sig_cnt_out                           false
% 0.92/0.99  --trig_cnt_out                          false
% 0.92/0.99  --trig_cnt_out_tolerance                1.
% 0.92/0.99  --trig_cnt_out_sk_spl                   false
% 0.92/0.99  --abstr_cl_out                          false
% 0.92/0.99  
% 0.92/0.99  ------ Global Options
% 0.92/0.99  
% 0.92/0.99  --schedule                              default
% 0.92/0.99  --add_important_lit                     false
% 0.92/0.99  --prop_solver_per_cl                    1000
% 0.92/0.99  --min_unsat_core                        false
% 0.92/0.99  --soft_assumptions                      false
% 0.92/0.99  --soft_lemma_size                       3
% 0.92/0.99  --prop_impl_unit_size                   0
% 0.92/0.99  --prop_impl_unit                        []
% 0.92/0.99  --share_sel_clauses                     true
% 0.92/0.99  --reset_solvers                         false
% 0.92/0.99  --bc_imp_inh                            [conj_cone]
% 0.92/0.99  --conj_cone_tolerance                   3.
% 0.92/0.99  --extra_neg_conj                        none
% 0.92/0.99  --large_theory_mode                     true
% 0.92/0.99  --prolific_symb_bound                   200
% 0.92/0.99  --lt_threshold                          2000
% 0.92/0.99  --clause_weak_htbl                      true
% 0.92/0.99  --gc_record_bc_elim                     false
% 0.92/0.99  
% 0.92/0.99  ------ Preprocessing Options
% 0.92/0.99  
% 0.92/0.99  --preprocessing_flag                    true
% 0.92/0.99  --time_out_prep_mult                    0.1
% 0.92/0.99  --splitting_mode                        input
% 0.92/0.99  --splitting_grd                         true
% 0.92/0.99  --splitting_cvd                         false
% 0.92/0.99  --splitting_cvd_svl                     false
% 0.92/0.99  --splitting_nvd                         32
% 0.92/0.99  --sub_typing                            true
% 0.92/0.99  --prep_gs_sim                           true
% 0.92/0.99  --prep_unflatten                        true
% 0.92/0.99  --prep_res_sim                          true
% 0.92/0.99  --prep_upred                            true
% 0.92/0.99  --prep_sem_filter                       exhaustive
% 0.92/0.99  --prep_sem_filter_out                   false
% 0.92/0.99  --pred_elim                             true
% 0.92/0.99  --res_sim_input                         true
% 0.92/0.99  --eq_ax_congr_red                       true
% 0.92/0.99  --pure_diseq_elim                       true
% 0.92/0.99  --brand_transform                       false
% 0.92/0.99  --non_eq_to_eq                          false
% 0.92/0.99  --prep_def_merge                        true
% 0.92/0.99  --prep_def_merge_prop_impl              false
% 0.92/0.99  --prep_def_merge_mbd                    true
% 0.92/0.99  --prep_def_merge_tr_red                 false
% 0.92/0.99  --prep_def_merge_tr_cl                  false
% 0.92/0.99  --smt_preprocessing                     true
% 0.92/0.99  --smt_ac_axioms                         fast
% 0.92/0.99  --preprocessed_out                      false
% 0.92/0.99  --preprocessed_stats                    false
% 0.92/0.99  
% 0.92/0.99  ------ Abstraction refinement Options
% 0.92/0.99  
% 0.92/0.99  --abstr_ref                             []
% 0.92/0.99  --abstr_ref_prep                        false
% 0.92/0.99  --abstr_ref_until_sat                   false
% 0.92/0.99  --abstr_ref_sig_restrict                funpre
% 0.92/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.92/0.99  --abstr_ref_under                       []
% 0.92/0.99  
% 0.92/0.99  ------ SAT Options
% 0.92/0.99  
% 0.92/0.99  --sat_mode                              false
% 0.92/0.99  --sat_fm_restart_options                ""
% 0.92/0.99  --sat_gr_def                            false
% 0.92/0.99  --sat_epr_types                         true
% 0.92/0.99  --sat_non_cyclic_types                  false
% 0.92/0.99  --sat_finite_models                     false
% 0.92/0.99  --sat_fm_lemmas                         false
% 0.92/0.99  --sat_fm_prep                           false
% 0.92/0.99  --sat_fm_uc_incr                        true
% 0.92/0.99  --sat_out_model                         small
% 0.92/0.99  --sat_out_clauses                       false
% 0.92/0.99  
% 0.92/0.99  ------ QBF Options
% 0.92/0.99  
% 0.92/0.99  --qbf_mode                              false
% 0.92/0.99  --qbf_elim_univ                         false
% 0.92/0.99  --qbf_dom_inst                          none
% 0.92/0.99  --qbf_dom_pre_inst                      false
% 0.92/0.99  --qbf_sk_in                             false
% 0.92/0.99  --qbf_pred_elim                         true
% 0.92/0.99  --qbf_split                             512
% 0.92/0.99  
% 0.92/0.99  ------ BMC1 Options
% 0.92/0.99  
% 0.92/0.99  --bmc1_incremental                      false
% 0.92/0.99  --bmc1_axioms                           reachable_all
% 0.92/0.99  --bmc1_min_bound                        0
% 0.92/0.99  --bmc1_max_bound                        -1
% 0.92/0.99  --bmc1_max_bound_default                -1
% 0.92/0.99  --bmc1_symbol_reachability              true
% 0.92/0.99  --bmc1_property_lemmas                  false
% 0.92/0.99  --bmc1_k_induction                      false
% 0.92/0.99  --bmc1_non_equiv_states                 false
% 0.92/0.99  --bmc1_deadlock                         false
% 0.92/0.99  --bmc1_ucm                              false
% 0.92/0.99  --bmc1_add_unsat_core                   none
% 0.92/0.99  --bmc1_unsat_core_children              false
% 0.92/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.92/0.99  --bmc1_out_stat                         full
% 0.92/0.99  --bmc1_ground_init                      false
% 0.92/0.99  --bmc1_pre_inst_next_state              false
% 0.92/0.99  --bmc1_pre_inst_state                   false
% 0.92/0.99  --bmc1_pre_inst_reach_state             false
% 0.92/0.99  --bmc1_out_unsat_core                   false
% 0.92/0.99  --bmc1_aig_witness_out                  false
% 0.92/0.99  --bmc1_verbose                          false
% 0.92/0.99  --bmc1_dump_clauses_tptp                false
% 0.92/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.92/0.99  --bmc1_dump_file                        -
% 0.92/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.92/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.92/0.99  --bmc1_ucm_extend_mode                  1
% 0.92/0.99  --bmc1_ucm_init_mode                    2
% 0.92/0.99  --bmc1_ucm_cone_mode                    none
% 0.92/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.92/0.99  --bmc1_ucm_relax_model                  4
% 0.92/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.92/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.92/0.99  --bmc1_ucm_layered_model                none
% 0.92/0.99  --bmc1_ucm_max_lemma_size               10
% 0.92/0.99  
% 0.92/0.99  ------ AIG Options
% 0.92/0.99  
% 0.92/0.99  --aig_mode                              false
% 0.92/0.99  
% 0.92/0.99  ------ Instantiation Options
% 0.92/0.99  
% 0.92/0.99  --instantiation_flag                    true
% 0.92/0.99  --inst_sos_flag                         false
% 0.92/0.99  --inst_sos_phase                        true
% 0.92/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.92/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.92/0.99  --inst_lit_sel_side                     none
% 0.92/0.99  --inst_solver_per_active                1400
% 0.92/0.99  --inst_solver_calls_frac                1.
% 0.92/0.99  --inst_passive_queue_type               priority_queues
% 0.92/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.92/0.99  --inst_passive_queues_freq              [25;2]
% 0.92/0.99  --inst_dismatching                      true
% 0.92/0.99  --inst_eager_unprocessed_to_passive     true
% 0.92/0.99  --inst_prop_sim_given                   true
% 0.92/0.99  --inst_prop_sim_new                     false
% 0.92/0.99  --inst_subs_new                         false
% 0.92/0.99  --inst_eq_res_simp                      false
% 0.92/0.99  --inst_subs_given                       false
% 0.92/0.99  --inst_orphan_elimination               true
% 0.92/0.99  --inst_learning_loop_flag               true
% 0.92/0.99  --inst_learning_start                   3000
% 0.92/0.99  --inst_learning_factor                  2
% 0.92/0.99  --inst_start_prop_sim_after_learn       3
% 0.92/0.99  --inst_sel_renew                        solver
% 0.92/0.99  --inst_lit_activity_flag                true
% 0.92/0.99  --inst_restr_to_given                   false
% 0.92/0.99  --inst_activity_threshold               500
% 0.92/0.99  --inst_out_proof                        true
% 0.92/0.99  
% 0.92/0.99  ------ Resolution Options
% 0.92/0.99  
% 0.92/0.99  --resolution_flag                       false
% 0.92/0.99  --res_lit_sel                           adaptive
% 0.92/0.99  --res_lit_sel_side                      none
% 0.92/0.99  --res_ordering                          kbo
% 0.92/0.99  --res_to_prop_solver                    active
% 0.92/0.99  --res_prop_simpl_new                    false
% 0.92/0.99  --res_prop_simpl_given                  true
% 0.92/0.99  --res_passive_queue_type                priority_queues
% 0.92/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.92/0.99  --res_passive_queues_freq               [15;5]
% 0.92/0.99  --res_forward_subs                      full
% 0.92/0.99  --res_backward_subs                     full
% 0.92/0.99  --res_forward_subs_resolution           true
% 0.92/0.99  --res_backward_subs_resolution          true
% 0.92/0.99  --res_orphan_elimination                true
% 0.92/0.99  --res_time_limit                        2.
% 0.92/0.99  --res_out_proof                         true
% 0.92/0.99  
% 0.92/0.99  ------ Superposition Options
% 0.92/0.99  
% 0.92/0.99  --superposition_flag                    true
% 0.92/0.99  --sup_passive_queue_type                priority_queues
% 0.92/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.92/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.92/0.99  --demod_completeness_check              fast
% 0.92/0.99  --demod_use_ground                      true
% 0.92/0.99  --sup_to_prop_solver                    passive
% 0.92/0.99  --sup_prop_simpl_new                    true
% 0.92/0.99  --sup_prop_simpl_given                  true
% 0.92/0.99  --sup_fun_splitting                     false
% 0.92/0.99  --sup_smt_interval                      50000
% 0.92/0.99  
% 0.92/0.99  ------ Superposition Simplification Setup
% 0.92/0.99  
% 0.92/0.99  --sup_indices_passive                   []
% 0.92/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.92/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.92/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/0.99  --sup_full_bw                           [BwDemod]
% 0.92/0.99  --sup_immed_triv                        [TrivRules]
% 0.92/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.92/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/0.99  --sup_immed_bw_main                     []
% 0.92/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.92/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.92/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.92/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.92/0.99  
% 0.92/0.99  ------ Combination Options
% 0.92/0.99  
% 0.92/0.99  --comb_res_mult                         3
% 0.92/0.99  --comb_sup_mult                         2
% 0.92/0.99  --comb_inst_mult                        10
% 0.92/0.99  
% 0.92/0.99  ------ Debug Options
% 0.92/0.99  
% 0.92/0.99  --dbg_backtrace                         false
% 0.92/0.99  --dbg_dump_prop_clauses                 false
% 0.92/0.99  --dbg_dump_prop_clauses_file            -
% 0.92/0.99  --dbg_out_stat                          false
% 0.92/0.99  
% 0.92/0.99  
% 0.92/0.99  
% 0.92/0.99  
% 0.92/0.99  ------ Proving...
% 0.92/0.99  
% 0.92/0.99  
% 0.92/0.99  % SZS status Theorem for theBenchmark.p
% 0.92/0.99  
% 0.92/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 0.92/0.99  
% 0.92/0.99  fof(f1,axiom,(
% 0.92/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.92/0.99  
% 0.92/0.99  fof(f14,plain,(
% 0.92/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.92/0.99    inference(unused_predicate_definition_removal,[],[f1])).
% 0.92/0.99  
% 0.92/0.99  fof(f15,plain,(
% 0.92/0.99    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.92/0.99    inference(ennf_transformation,[],[f14])).
% 0.92/0.99  
% 0.92/0.99  fof(f35,plain,(
% 0.92/0.99    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.92/0.99    inference(cnf_transformation,[],[f15])).
% 0.92/0.99  
% 0.92/0.99  fof(f4,axiom,(
% 0.92/0.99    v1_xboole_0(k1_xboole_0)),
% 0.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.92/0.99  
% 0.92/0.99  fof(f43,plain,(
% 0.92/0.99    v1_xboole_0(k1_xboole_0)),
% 0.92/0.99    inference(cnf_transformation,[],[f4])).
% 0.92/0.99  
% 0.92/0.99  fof(f2,axiom,(
% 0.92/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.92/0.99  
% 0.92/0.99  fof(f13,plain,(
% 0.92/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.92/0.99    inference(unused_predicate_definition_removal,[],[f2])).
% 0.92/0.99  
% 0.92/0.99  fof(f16,plain,(
% 0.92/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.92/0.99    inference(ennf_transformation,[],[f13])).
% 0.92/0.99  
% 0.92/0.99  fof(f36,plain,(
% 0.92/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.92/0.99    inference(cnf_transformation,[],[f16])).
% 0.92/0.99  
% 0.92/0.99  fof(f9,conjecture,(
% 0.92/0.99    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.92/0.99  
% 0.92/0.99  fof(f10,negated_conjecture,(
% 0.92/0.99    ~! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.92/0.99    inference(negated_conjecture,[],[f9])).
% 0.92/0.99  
% 0.92/0.99  fof(f20,plain,(
% 0.92/0.99    ? [X0,X1] : (k1_xboole_0 != X0 & r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.92/0.99    inference(ennf_transformation,[],[f10])).
% 0.92/0.99  
% 0.92/0.99  fof(f33,plain,(
% 0.92/0.99    ? [X0,X1] : (k1_xboole_0 != X0 & r1_tarski(X0,k4_xboole_0(X1,X0))) => (k1_xboole_0 != sK4 & r1_tarski(sK4,k4_xboole_0(sK5,sK4)))),
% 0.92/0.99    introduced(choice_axiom,[])).
% 0.92/0.99  
% 0.92/0.99  fof(f34,plain,(
% 0.92/0.99    k1_xboole_0 != sK4 & r1_tarski(sK4,k4_xboole_0(sK5,sK4))),
% 0.92/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f20,f33])).
% 0.92/0.99  
% 0.92/0.99  fof(f52,plain,(
% 0.92/0.99    r1_tarski(sK4,k4_xboole_0(sK5,sK4))),
% 0.92/0.99    inference(cnf_transformation,[],[f34])).
% 0.92/0.99  
% 0.92/0.99  fof(f3,axiom,(
% 0.92/0.99    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.92/0.99  
% 0.92/0.99  fof(f21,plain,(
% 0.92/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.92/0.99    inference(nnf_transformation,[],[f3])).
% 0.92/0.99  
% 0.92/0.99  fof(f22,plain,(
% 0.92/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.92/0.99    inference(flattening,[],[f21])).
% 0.92/0.99  
% 0.92/0.99  fof(f23,plain,(
% 0.92/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.92/0.99    inference(rectify,[],[f22])).
% 0.92/0.99  
% 0.92/0.99  fof(f24,plain,(
% 0.92/0.99    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 0.92/0.99    introduced(choice_axiom,[])).
% 0.92/0.99  
% 0.92/0.99  fof(f25,plain,(
% 0.92/0.99    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.92/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 0.92/0.99  
% 0.92/0.99  fof(f38,plain,(
% 0.92/0.99    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.92/0.99    inference(cnf_transformation,[],[f25])).
% 0.92/0.99  
% 0.92/0.99  fof(f55,plain,(
% 0.92/0.99    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 0.92/0.99    inference(equality_resolution,[],[f38])).
% 0.92/0.99  
% 0.92/0.99  fof(f5,axiom,(
% 0.92/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 0.92/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.92/0.99  
% 0.92/0.99  fof(f17,plain,(
% 0.92/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 0.92/0.99    inference(ennf_transformation,[],[f5])).
% 0.92/0.99  
% 0.92/0.99  fof(f26,plain,(
% 0.92/0.99    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 0.92/0.99    inference(nnf_transformation,[],[f17])).
% 0.92/0.99  
% 0.92/0.99  fof(f27,plain,(
% 0.92/0.99    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 0.92/0.99    introduced(choice_axiom,[])).
% 0.92/0.99  
% 0.92/0.99  fof(f28,plain,(
% 0.92/0.99    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK1(X0,X1),X1) | ~r2_hidden(sK1(X0,X1),X0)) & (r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0))))),
% 0.92/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 0.92/0.99  
% 0.92/0.99  fof(f44,plain,(
% 0.92/0.99    ( ! [X0,X1] : (X0 = X1 | r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 0.92/0.99    inference(cnf_transformation,[],[f28])).
% 0.92/0.99  
% 0.92/0.99  fof(f53,plain,(
% 0.92/0.99    k1_xboole_0 != sK4),
% 0.92/0.99    inference(cnf_transformation,[],[f34])).
% 0.92/0.99  
% 0.92/0.99  cnf(c_0,plain,
% 0.92/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 0.92/0.99      inference(cnf_transformation,[],[f35]) ).
% 0.92/0.99  
% 0.92/0.99  cnf(c_8,plain,
% 0.92/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 0.92/0.99      inference(cnf_transformation,[],[f43]) ).
% 0.92/0.99  
% 0.92/0.99  cnf(c_191,plain,
% 0.92/0.99      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 0.92/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_8]) ).
% 0.92/0.99  
% 0.92/0.99  cnf(c_192,plain,
% 0.92/0.99      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 0.92/0.99      inference(unflattening,[status(thm)],[c_191]) ).
% 0.92/0.99  
% 0.92/0.99  cnf(c_910,plain,
% 0.92/0.99      ( ~ r2_hidden(sK1(k1_xboole_0,sK4),k1_xboole_0) ),
% 0.92/0.99      inference(instantiation,[status(thm)],[c_192]) ).
% 0.92/0.99  
% 0.92/0.99  cnf(c_1,plain,
% 0.92/0.99      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 0.92/0.99      inference(cnf_transformation,[],[f36]) ).
% 0.92/0.99  
% 0.92/0.99  cnf(c_18,negated_conjecture,
% 0.92/0.99      ( r1_tarski(sK4,k4_xboole_0(sK5,sK4)) ),
% 0.92/0.99      inference(cnf_transformation,[],[f52]) ).
% 0.92/0.99  
% 0.92/0.99  cnf(c_202,plain,
% 0.92/0.99      ( ~ r2_hidden(X0,X1)
% 0.92/0.99      | r2_hidden(X0,X2)
% 0.92/0.99      | k4_xboole_0(sK5,sK4) != X2
% 0.92/0.99      | sK4 != X1 ),
% 0.92/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_18]) ).
% 0.92/0.99  
% 0.92/0.99  cnf(c_203,plain,
% 0.92/0.99      ( r2_hidden(X0,k4_xboole_0(sK5,sK4)) | ~ r2_hidden(X0,sK4) ),
% 0.92/0.99      inference(unflattening,[status(thm)],[c_202]) ).
% 0.92/0.99  
% 0.92/0.99  cnf(c_6,plain,
% 0.92/0.99      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 0.92/0.99      inference(cnf_transformation,[],[f55]) ).
% 0.92/0.99  
% 0.92/0.99  cnf(c_211,plain,
% 0.92/0.99      ( ~ r2_hidden(X0,sK4) ),
% 0.92/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_203,c_6]) ).
% 0.92/0.99  
% 0.92/0.99  cnf(c_877,plain,
% 0.92/0.99      ( ~ r2_hidden(sK1(k1_xboole_0,sK4),sK4) ),
% 0.92/0.99      inference(instantiation,[status(thm)],[c_211]) ).
% 0.92/0.99  
% 0.92/0.99  cnf(c_10,plain,
% 0.92/0.99      ( r2_hidden(sK1(X0,X1),X1) | r2_hidden(sK1(X0,X1),X0) | X0 = X1 ),
% 0.92/0.99      inference(cnf_transformation,[],[f44]) ).
% 0.92/0.99  
% 0.92/0.99  cnf(c_853,plain,
% 0.92/0.99      ( r2_hidden(sK1(k1_xboole_0,sK4),sK4)
% 0.92/0.99      | r2_hidden(sK1(k1_xboole_0,sK4),k1_xboole_0)
% 0.92/0.99      | k1_xboole_0 = sK4 ),
% 0.92/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 0.92/0.99  
% 0.92/0.99  cnf(c_17,negated_conjecture,
% 0.92/0.99      ( k1_xboole_0 != sK4 ),
% 0.92/0.99      inference(cnf_transformation,[],[f53]) ).
% 0.92/0.99  
% 0.92/0.99  cnf(contradiction,plain,
% 0.92/0.99      ( $false ),
% 0.92/0.99      inference(minisat,[status(thm)],[c_910,c_877,c_853,c_17]) ).
% 0.92/0.99  
% 0.92/0.99  
% 0.92/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 0.92/0.99  
% 0.92/0.99  ------                               Statistics
% 0.92/0.99  
% 0.92/0.99  ------ General
% 0.92/0.99  
% 0.92/0.99  abstr_ref_over_cycles:                  0
% 0.92/0.99  abstr_ref_under_cycles:                 0
% 0.92/0.99  gc_basic_clause_elim:                   0
% 0.92/0.99  forced_gc_time:                         0
% 0.92/0.99  parsing_time:                           0.01
% 0.92/0.99  unif_index_cands_time:                  0.
% 0.92/0.99  unif_index_add_time:                    0.
% 0.92/0.99  orderings_time:                         0.
% 0.92/0.99  out_proof_time:                         0.009
% 0.92/0.99  total_time:                             0.065
% 0.92/0.99  num_of_symbols:                         44
% 0.92/0.99  num_of_terms:                           439
% 0.92/0.99  
% 0.92/0.99  ------ Preprocessing
% 0.92/0.99  
% 0.92/0.99  num_of_splits:                          0
% 0.92/0.99  num_of_split_atoms:                     0
% 0.92/0.99  num_of_reused_defs:                     0
% 0.92/0.99  num_eq_ax_congr_red:                    40
% 0.92/0.99  num_of_sem_filtered_clauses:            1
% 0.92/0.99  num_of_subtypes:                        0
% 0.92/0.99  monotx_restored_types:                  0
% 0.92/0.99  sat_num_of_epr_types:                   0
% 0.92/0.99  sat_num_of_non_cyclic_types:            0
% 0.92/0.99  sat_guarded_non_collapsed_types:        0
% 0.92/0.99  num_pure_diseq_elim:                    0
% 0.92/0.99  simp_replaced_by:                       0
% 0.92/0.99  res_preprocessed:                       79
% 0.92/0.99  prep_upred:                             0
% 0.92/0.99  prep_unflattend:                        3
% 0.92/0.99  smt_new_axioms:                         0
% 0.92/0.99  pred_elim_cands:                        2
% 0.92/0.99  pred_elim:                              2
% 0.92/0.99  pred_elim_cl:                           2
% 0.92/0.99  pred_elim_cycles:                       4
% 0.92/0.99  merged_defs:                            0
% 0.92/0.99  merged_defs_ncl:                        0
% 0.92/0.99  bin_hyper_res:                          0
% 0.92/0.99  prep_cycles:                            4
% 0.92/0.99  pred_elim_time:                         0.003
% 0.92/0.99  splitting_time:                         0.
% 0.92/0.99  sem_filter_time:                        0.
% 0.92/0.99  monotx_time:                            0.
% 0.92/0.99  subtype_inf_time:                       0.
% 0.92/0.99  
% 0.92/0.99  ------ Problem properties
% 0.92/0.99  
% 0.92/0.99  clauses:                                17
% 0.92/0.99  conjectures:                            1
% 0.92/0.99  epr:                                    4
% 0.92/0.99  horn:                                   9
% 0.92/0.99  ground:                                 1
% 0.92/0.99  unary:                                  4
% 0.92/0.99  binary:                                 6
% 0.92/0.99  lits:                                   38
% 0.92/0.99  lits_eq:                                7
% 0.92/0.99  fd_pure:                                0
% 0.92/0.99  fd_pseudo:                              0
% 0.92/0.99  fd_cond:                                0
% 0.92/0.99  fd_pseudo_cond:                         5
% 0.92/0.99  ac_symbols:                             0
% 0.92/0.99  
% 0.92/0.99  ------ Propositional Solver
% 0.92/0.99  
% 0.92/0.99  prop_solver_calls:                      24
% 0.92/0.99  prop_fast_solver_calls:                 393
% 0.92/0.99  smt_solver_calls:                       0
% 0.92/0.99  smt_fast_solver_calls:                  0
% 0.92/0.99  prop_num_of_clauses:                    139
% 0.92/0.99  prop_preprocess_simplified:             2280
% 0.92/0.99  prop_fo_subsumed:                       0
% 0.92/0.99  prop_solver_time:                       0.
% 0.92/0.99  smt_solver_time:                        0.
% 0.92/0.99  smt_fast_solver_time:                   0.
% 0.92/0.99  prop_fast_solver_time:                  0.
% 0.92/0.99  prop_unsat_core_time:                   0.
% 0.92/0.99  
% 0.92/0.99  ------ QBF
% 0.92/0.99  
% 0.92/0.99  qbf_q_res:                              0
% 0.92/0.99  qbf_num_tautologies:                    0
% 0.92/0.99  qbf_prep_cycles:                        0
% 0.92/0.99  
% 0.92/0.99  ------ BMC1
% 0.92/0.99  
% 0.92/0.99  bmc1_current_bound:                     -1
% 0.92/0.99  bmc1_last_solved_bound:                 -1
% 0.92/0.99  bmc1_unsat_core_size:                   -1
% 0.92/0.99  bmc1_unsat_core_parents_size:           -1
% 0.92/0.99  bmc1_merge_next_fun:                    0
% 0.92/0.99  bmc1_unsat_core_clauses_time:           0.
% 0.92/0.99  
% 0.92/0.99  ------ Instantiation
% 0.92/0.99  
% 0.92/0.99  inst_num_of_clauses:                    35
% 0.92/0.99  inst_num_in_passive:                    7
% 0.92/0.99  inst_num_in_active:                     23
% 0.92/0.99  inst_num_in_unprocessed:                4
% 0.92/0.99  inst_num_of_loops:                      28
% 0.92/0.99  inst_num_of_learning_restarts:          0
% 0.92/0.99  inst_num_moves_active_passive:          1
% 0.92/0.99  inst_lit_activity:                      0
% 0.92/0.99  inst_lit_activity_moves:                0
% 0.92/0.99  inst_num_tautologies:                   0
% 0.92/0.99  inst_num_prop_implied:                  0
% 0.92/0.99  inst_num_existing_simplified:           0
% 0.92/0.99  inst_num_eq_res_simplified:             0
% 0.92/0.99  inst_num_child_elim:                    0
% 0.92/0.99  inst_num_of_dismatching_blockings:      0
% 0.92/0.99  inst_num_of_non_proper_insts:           11
% 0.92/0.99  inst_num_of_duplicates:                 0
% 0.92/0.99  inst_inst_num_from_inst_to_res:         0
% 0.92/0.99  inst_dismatching_checking_time:         0.
% 0.92/0.99  
% 0.92/0.99  ------ Resolution
% 0.92/0.99  
% 0.92/0.99  res_num_of_clauses:                     0
% 0.92/0.99  res_num_in_passive:                     0
% 0.92/0.99  res_num_in_active:                      0
% 0.92/0.99  res_num_of_loops:                       83
% 0.92/0.99  res_forward_subset_subsumed:            1
% 0.92/0.99  res_backward_subset_subsumed:           2
% 0.92/0.99  res_forward_subsumed:                   0
% 0.92/0.99  res_backward_subsumed:                  0
% 0.92/0.99  res_forward_subsumption_resolution:     1
% 0.92/0.99  res_backward_subsumption_resolution:    0
% 0.92/0.99  res_clause_to_clause_subsumption:       39
% 0.92/0.99  res_orphan_elimination:                 0
% 0.92/0.99  res_tautology_del:                      0
% 0.92/0.99  res_num_eq_res_simplified:              0
% 0.92/0.99  res_num_sel_changes:                    0
% 0.92/0.99  res_moves_from_active_to_pass:          0
% 0.92/0.99  
% 0.92/0.99  ------ Superposition
% 0.92/0.99  
% 0.92/0.99  sup_time_total:                         0.
% 0.92/0.99  sup_time_generating:                    0.
% 0.92/0.99  sup_time_sim_full:                      0.
% 0.92/0.99  sup_time_sim_immed:                     0.
% 0.92/0.99  
% 0.92/0.99  sup_num_of_clauses:                     17
% 0.92/0.99  sup_num_in_active:                      4
% 0.92/0.99  sup_num_in_passive:                     13
% 0.92/0.99  sup_num_of_loops:                       4
% 0.92/0.99  sup_fw_superposition:                   0
% 0.92/0.99  sup_bw_superposition:                   0
% 0.92/0.99  sup_immediate_simplified:               0
% 0.92/0.99  sup_given_eliminated:                   0
% 0.92/0.99  comparisons_done:                       0
% 0.92/0.99  comparisons_avoided:                    0
% 0.92/0.99  
% 0.92/0.99  ------ Simplifications
% 0.92/0.99  
% 0.92/0.99  
% 0.92/0.99  sim_fw_subset_subsumed:                 0
% 0.92/0.99  sim_bw_subset_subsumed:                 0
% 0.92/0.99  sim_fw_subsumed:                        0
% 0.92/0.99  sim_bw_subsumed:                        0
% 0.92/0.99  sim_fw_subsumption_res:                 0
% 0.92/0.99  sim_bw_subsumption_res:                 0
% 0.92/0.99  sim_tautology_del:                      0
% 0.92/0.99  sim_eq_tautology_del:                   0
% 0.92/0.99  sim_eq_res_simp:                        0
% 0.92/0.99  sim_fw_demodulated:                     0
% 0.92/0.99  sim_bw_demodulated:                     0
% 0.92/0.99  sim_light_normalised:                   0
% 0.92/0.99  sim_joinable_taut:                      0
% 0.92/0.99  sim_joinable_simp:                      0
% 0.92/0.99  sim_ac_normalised:                      0
% 0.92/0.99  sim_smt_subsumption:                    0
% 0.92/0.99  
%------------------------------------------------------------------------------
