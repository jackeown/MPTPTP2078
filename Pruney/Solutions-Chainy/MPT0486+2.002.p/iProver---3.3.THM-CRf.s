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
% DateTime   : Thu Dec  3 11:44:38 EST 2020

% Result     : Theorem 0.95s
% Output     : CNFRefutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :   49 (  63 expanded)
%              Number of clauses        :   26 (  30 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :   12
%              Number of atoms          :  171 ( 193 expanded)
%              Number of equality atoms :   86 ( 100 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   15 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) = X1
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
                | X2 != X3
                | ~ r2_hidden(X2,X0) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ? [X2,X3] :
              ( ( X2 != X3
                | ~ r2_hidden(X2,X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( ( X2 = X3
                  & r2_hidden(X2,X0) )
                | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK0(X0,X1) != sK1(X0,X1)
          | ~ r2_hidden(sK0(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
        & ( ( sK0(X0,X1) = sK1(X0,X1)
            & r2_hidden(sK0(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK0(X0,X1) != sK1(X0,X1)
              | ~ r2_hidden(sK0(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) )
            & ( ( sK0(X0,X1) = sK1(X0,X1)
                & r2_hidden(sK0(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) = X1
      | r2_hidden(sK0(X0,X1),X0)
      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f11,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] : k4_tarski(X2,X3) != sK2(X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ( ! [X2,X3] : k4_tarski(X2,X3) != sK2(X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f17])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,conjecture,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
    k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f6])).

fof(f29,plain,(
    k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_1,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_2140,plain,
    ( k2_xboole_0(k1_tarski(sK0(k1_xboole_0,X0)),k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2143,plain,
    ( k2_xboole_0(k1_tarski(sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2140])).

cnf(c_1221,plain,
    ( k2_xboole_0(k1_tarski(k4_tarski(sK0(X0,k1_xboole_0),sK1(X0,k1_xboole_0))),k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1224,plain,
    ( k2_xboole_0(k1_tarski(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0))),k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1221])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_1008,plain,
    ( ~ r2_hidden(sK0(X0,X1),X0)
    | k2_xboole_0(k1_tarski(sK0(X0,X1)),X0) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1010,plain,
    ( ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k2_xboole_0(k1_tarski(sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1008])).

cnf(c_4,plain,
    ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
    | r2_hidden(sK0(X0,X1),X0)
    | ~ v1_relat_1(X1)
    | k6_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_539,plain,
    ( k6_relat_1(X0) = X1
    | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_542,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) = X1
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_810,plain,
    ( k2_xboole_0(k1_tarski(k4_tarski(sK0(X0,X1),sK1(X0,X1))),X1) = X1
    | k6_relat_1(X0) = X1
    | r2_hidden(sK0(X0,X1),X0) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_539,c_542])).

cnf(c_850,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | ~ v1_relat_1(X1)
    | k2_xboole_0(k1_tarski(k4_tarski(sK0(X0,X1),sK1(X0,X1))),X1) = X1
    | k6_relat_1(X0) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_810])).

cnf(c_852,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k2_xboole_0(k1_tarski(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0))),k1_xboole_0) = k1_xboole_0
    | k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_850])).

cnf(c_671,plain,
    ( k2_xboole_0(k1_tarski(sK2(k1_xboole_0)),k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_646,plain,
    ( ~ r2_hidden(sK2(X0),X0)
    | k2_xboole_0(k1_tarski(sK2(X0)),X0) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_648,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | k2_xboole_0(k1_tarski(sK2(k1_xboole_0)),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_646])).

cnf(c_363,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_643,plain,
    ( k6_relat_1(k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_363])).

cnf(c_644,plain,
    ( k6_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_643])).

cnf(c_362,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_375,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_9,plain,
    ( r2_hidden(sK2(X0),X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_12,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_10,negated_conjecture,
    ( k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2143,c_1224,c_1010,c_852,c_671,c_648,c_644,c_375,c_12,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:13:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.95/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.95/0.99  
% 0.95/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.95/0.99  
% 0.95/0.99  ------  iProver source info
% 0.95/0.99  
% 0.95/0.99  git: date: 2020-06-30 10:37:57 +0100
% 0.95/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.95/0.99  git: non_committed_changes: false
% 0.95/0.99  git: last_make_outside_of_git: false
% 0.95/0.99  
% 0.95/0.99  ------ 
% 0.95/0.99  
% 0.95/0.99  ------ Input Options
% 0.95/0.99  
% 0.95/0.99  --out_options                           all
% 0.95/0.99  --tptp_safe_out                         true
% 0.95/0.99  --problem_path                          ""
% 0.95/0.99  --include_path                          ""
% 0.95/0.99  --clausifier                            res/vclausify_rel
% 0.95/0.99  --clausifier_options                    --mode clausify
% 0.95/0.99  --stdin                                 false
% 0.95/0.99  --stats_out                             all
% 0.95/0.99  
% 0.95/0.99  ------ General Options
% 0.95/0.99  
% 0.95/0.99  --fof                                   false
% 0.95/0.99  --time_out_real                         305.
% 0.95/0.99  --time_out_virtual                      -1.
% 0.95/0.99  --symbol_type_check                     false
% 0.95/0.99  --clausify_out                          false
% 0.95/0.99  --sig_cnt_out                           false
% 0.95/0.99  --trig_cnt_out                          false
% 0.95/0.99  --trig_cnt_out_tolerance                1.
% 0.95/0.99  --trig_cnt_out_sk_spl                   false
% 0.95/0.99  --abstr_cl_out                          false
% 0.95/0.99  
% 0.95/0.99  ------ Global Options
% 0.95/0.99  
% 0.95/0.99  --schedule                              default
% 0.95/0.99  --add_important_lit                     false
% 0.95/0.99  --prop_solver_per_cl                    1000
% 0.95/0.99  --min_unsat_core                        false
% 0.95/0.99  --soft_assumptions                      false
% 0.95/0.99  --soft_lemma_size                       3
% 0.95/0.99  --prop_impl_unit_size                   0
% 0.95/0.99  --prop_impl_unit                        []
% 0.95/0.99  --share_sel_clauses                     true
% 0.95/0.99  --reset_solvers                         false
% 0.95/0.99  --bc_imp_inh                            [conj_cone]
% 0.95/0.99  --conj_cone_tolerance                   3.
% 0.95/0.99  --extra_neg_conj                        none
% 0.95/0.99  --large_theory_mode                     true
% 0.95/0.99  --prolific_symb_bound                   200
% 0.95/0.99  --lt_threshold                          2000
% 0.95/0.99  --clause_weak_htbl                      true
% 0.95/0.99  --gc_record_bc_elim                     false
% 0.95/0.99  
% 0.95/0.99  ------ Preprocessing Options
% 0.95/0.99  
% 0.95/0.99  --preprocessing_flag                    true
% 0.95/0.99  --time_out_prep_mult                    0.1
% 0.95/0.99  --splitting_mode                        input
% 0.95/0.99  --splitting_grd                         true
% 0.95/0.99  --splitting_cvd                         false
% 0.95/0.99  --splitting_cvd_svl                     false
% 0.95/0.99  --splitting_nvd                         32
% 0.95/0.99  --sub_typing                            true
% 0.95/0.99  --prep_gs_sim                           true
% 0.95/0.99  --prep_unflatten                        true
% 0.95/0.99  --prep_res_sim                          true
% 0.95/0.99  --prep_upred                            true
% 0.95/0.99  --prep_sem_filter                       exhaustive
% 0.95/0.99  --prep_sem_filter_out                   false
% 0.95/0.99  --pred_elim                             true
% 0.95/0.99  --res_sim_input                         true
% 0.95/0.99  --eq_ax_congr_red                       true
% 0.95/0.99  --pure_diseq_elim                       true
% 0.95/0.99  --brand_transform                       false
% 0.95/0.99  --non_eq_to_eq                          false
% 0.95/0.99  --prep_def_merge                        true
% 0.95/0.99  --prep_def_merge_prop_impl              false
% 0.95/0.99  --prep_def_merge_mbd                    true
% 0.95/0.99  --prep_def_merge_tr_red                 false
% 0.95/0.99  --prep_def_merge_tr_cl                  false
% 0.95/0.99  --smt_preprocessing                     true
% 0.95/0.99  --smt_ac_axioms                         fast
% 0.95/0.99  --preprocessed_out                      false
% 0.95/0.99  --preprocessed_stats                    false
% 0.95/0.99  
% 0.95/0.99  ------ Abstraction refinement Options
% 0.95/0.99  
% 0.95/0.99  --abstr_ref                             []
% 0.95/0.99  --abstr_ref_prep                        false
% 0.95/0.99  --abstr_ref_until_sat                   false
% 0.95/0.99  --abstr_ref_sig_restrict                funpre
% 0.95/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.95/0.99  --abstr_ref_under                       []
% 0.95/0.99  
% 0.95/0.99  ------ SAT Options
% 0.95/0.99  
% 0.95/0.99  --sat_mode                              false
% 0.95/0.99  --sat_fm_restart_options                ""
% 0.95/0.99  --sat_gr_def                            false
% 0.95/0.99  --sat_epr_types                         true
% 0.95/0.99  --sat_non_cyclic_types                  false
% 0.95/0.99  --sat_finite_models                     false
% 0.95/0.99  --sat_fm_lemmas                         false
% 0.95/0.99  --sat_fm_prep                           false
% 0.95/0.99  --sat_fm_uc_incr                        true
% 0.95/0.99  --sat_out_model                         small
% 0.95/0.99  --sat_out_clauses                       false
% 0.95/0.99  
% 0.95/0.99  ------ QBF Options
% 0.95/0.99  
% 0.95/0.99  --qbf_mode                              false
% 0.95/0.99  --qbf_elim_univ                         false
% 0.95/0.99  --qbf_dom_inst                          none
% 0.95/0.99  --qbf_dom_pre_inst                      false
% 0.95/0.99  --qbf_sk_in                             false
% 0.95/0.99  --qbf_pred_elim                         true
% 0.95/0.99  --qbf_split                             512
% 0.95/0.99  
% 0.95/0.99  ------ BMC1 Options
% 0.95/0.99  
% 0.95/0.99  --bmc1_incremental                      false
% 0.95/0.99  --bmc1_axioms                           reachable_all
% 0.95/0.99  --bmc1_min_bound                        0
% 0.95/0.99  --bmc1_max_bound                        -1
% 0.95/0.99  --bmc1_max_bound_default                -1
% 0.95/0.99  --bmc1_symbol_reachability              true
% 0.95/0.99  --bmc1_property_lemmas                  false
% 0.95/0.99  --bmc1_k_induction                      false
% 0.95/0.99  --bmc1_non_equiv_states                 false
% 0.95/0.99  --bmc1_deadlock                         false
% 0.95/0.99  --bmc1_ucm                              false
% 0.95/0.99  --bmc1_add_unsat_core                   none
% 0.95/0.99  --bmc1_unsat_core_children              false
% 0.95/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.95/0.99  --bmc1_out_stat                         full
% 0.95/0.99  --bmc1_ground_init                      false
% 0.95/0.99  --bmc1_pre_inst_next_state              false
% 0.95/0.99  --bmc1_pre_inst_state                   false
% 0.95/0.99  --bmc1_pre_inst_reach_state             false
% 0.95/0.99  --bmc1_out_unsat_core                   false
% 0.95/0.99  --bmc1_aig_witness_out                  false
% 0.95/0.99  --bmc1_verbose                          false
% 0.95/0.99  --bmc1_dump_clauses_tptp                false
% 0.95/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.95/0.99  --bmc1_dump_file                        -
% 0.95/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.95/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.95/0.99  --bmc1_ucm_extend_mode                  1
% 0.95/0.99  --bmc1_ucm_init_mode                    2
% 0.95/0.99  --bmc1_ucm_cone_mode                    none
% 0.95/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.95/0.99  --bmc1_ucm_relax_model                  4
% 0.95/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.95/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.95/0.99  --bmc1_ucm_layered_model                none
% 0.95/0.99  --bmc1_ucm_max_lemma_size               10
% 0.95/0.99  
% 0.95/0.99  ------ AIG Options
% 0.95/0.99  
% 0.95/0.99  --aig_mode                              false
% 0.95/0.99  
% 0.95/0.99  ------ Instantiation Options
% 0.95/0.99  
% 0.95/0.99  --instantiation_flag                    true
% 0.95/0.99  --inst_sos_flag                         false
% 0.95/0.99  --inst_sos_phase                        true
% 0.95/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.95/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.95/0.99  --inst_lit_sel_side                     num_symb
% 0.95/0.99  --inst_solver_per_active                1400
% 0.95/0.99  --inst_solver_calls_frac                1.
% 0.95/0.99  --inst_passive_queue_type               priority_queues
% 0.95/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.95/0.99  --inst_passive_queues_freq              [25;2]
% 0.95/0.99  --inst_dismatching                      true
% 0.95/0.99  --inst_eager_unprocessed_to_passive     true
% 0.95/0.99  --inst_prop_sim_given                   true
% 0.95/0.99  --inst_prop_sim_new                     false
% 0.95/0.99  --inst_subs_new                         false
% 0.95/0.99  --inst_eq_res_simp                      false
% 0.95/0.99  --inst_subs_given                       false
% 0.95/0.99  --inst_orphan_elimination               true
% 0.95/0.99  --inst_learning_loop_flag               true
% 0.95/0.99  --inst_learning_start                   3000
% 0.95/0.99  --inst_learning_factor                  2
% 0.95/0.99  --inst_start_prop_sim_after_learn       3
% 0.95/0.99  --inst_sel_renew                        solver
% 0.95/0.99  --inst_lit_activity_flag                true
% 0.95/0.99  --inst_restr_to_given                   false
% 0.95/0.99  --inst_activity_threshold               500
% 0.95/0.99  --inst_out_proof                        true
% 0.95/0.99  
% 0.95/0.99  ------ Resolution Options
% 0.95/0.99  
% 0.95/0.99  --resolution_flag                       true
% 0.95/0.99  --res_lit_sel                           adaptive
% 0.95/0.99  --res_lit_sel_side                      none
% 0.95/0.99  --res_ordering                          kbo
% 0.95/0.99  --res_to_prop_solver                    active
% 0.95/0.99  --res_prop_simpl_new                    false
% 0.95/0.99  --res_prop_simpl_given                  true
% 0.95/0.99  --res_passive_queue_type                priority_queues
% 0.95/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.95/0.99  --res_passive_queues_freq               [15;5]
% 0.95/0.99  --res_forward_subs                      full
% 0.95/0.99  --res_backward_subs                     full
% 0.95/0.99  --res_forward_subs_resolution           true
% 0.95/0.99  --res_backward_subs_resolution          true
% 0.95/0.99  --res_orphan_elimination                true
% 0.95/0.99  --res_time_limit                        2.
% 0.95/0.99  --res_out_proof                         true
% 0.95/0.99  
% 0.95/0.99  ------ Superposition Options
% 0.95/0.99  
% 0.95/0.99  --superposition_flag                    true
% 0.95/0.99  --sup_passive_queue_type                priority_queues
% 0.95/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.95/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.95/0.99  --demod_completeness_check              fast
% 0.95/0.99  --demod_use_ground                      true
% 0.95/0.99  --sup_to_prop_solver                    passive
% 0.95/0.99  --sup_prop_simpl_new                    true
% 0.95/0.99  --sup_prop_simpl_given                  true
% 0.95/0.99  --sup_fun_splitting                     false
% 0.95/0.99  --sup_smt_interval                      50000
% 0.95/0.99  
% 0.95/0.99  ------ Superposition Simplification Setup
% 0.95/0.99  
% 0.95/0.99  --sup_indices_passive                   []
% 0.95/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.95/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.99  --sup_full_bw                           [BwDemod]
% 0.95/0.99  --sup_immed_triv                        [TrivRules]
% 0.95/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.95/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.99  --sup_immed_bw_main                     []
% 0.95/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.95/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/0.99  
% 0.95/0.99  ------ Combination Options
% 0.95/0.99  
% 0.95/0.99  --comb_res_mult                         3
% 0.95/0.99  --comb_sup_mult                         2
% 0.95/0.99  --comb_inst_mult                        10
% 0.95/0.99  
% 0.95/0.99  ------ Debug Options
% 0.95/0.99  
% 0.95/0.99  --dbg_backtrace                         false
% 0.95/0.99  --dbg_dump_prop_clauses                 false
% 0.95/0.99  --dbg_dump_prop_clauses_file            -
% 0.95/0.99  --dbg_out_stat                          false
% 0.95/0.99  ------ Parsing...
% 0.95/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.95/0.99  
% 0.95/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.95/0.99  
% 0.95/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.95/0.99  
% 0.95/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.95/0.99  ------ Proving...
% 0.95/0.99  ------ Problem Properties 
% 0.95/0.99  
% 0.95/0.99  
% 0.95/0.99  clauses                                 11
% 0.95/0.99  conjectures                             1
% 0.95/0.99  EPR                                     0
% 0.95/0.99  Horn                                    8
% 0.95/0.99  unary                                   2
% 0.95/0.99  binary                                  3
% 0.95/0.99  lits                                    30
% 0.95/0.99  lits eq                                 10
% 0.95/0.99  fd_pure                                 0
% 0.95/0.99  fd_pseudo                               0
% 0.95/0.99  fd_cond                                 0
% 0.95/0.99  fd_pseudo_cond                          4
% 0.95/0.99  AC symbols                              0
% 0.95/0.99  
% 0.95/0.99  ------ Schedule dynamic 5 is on 
% 0.95/0.99  
% 0.95/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.95/0.99  
% 0.95/0.99  
% 0.95/0.99  ------ 
% 0.95/0.99  Current options:
% 0.95/0.99  ------ 
% 0.95/0.99  
% 0.95/0.99  ------ Input Options
% 0.95/0.99  
% 0.95/0.99  --out_options                           all
% 0.95/0.99  --tptp_safe_out                         true
% 0.95/0.99  --problem_path                          ""
% 0.95/0.99  --include_path                          ""
% 0.95/0.99  --clausifier                            res/vclausify_rel
% 0.95/0.99  --clausifier_options                    --mode clausify
% 0.95/0.99  --stdin                                 false
% 0.95/0.99  --stats_out                             all
% 0.95/0.99  
% 0.95/0.99  ------ General Options
% 0.95/0.99  
% 0.95/0.99  --fof                                   false
% 0.95/0.99  --time_out_real                         305.
% 0.95/0.99  --time_out_virtual                      -1.
% 0.95/0.99  --symbol_type_check                     false
% 0.95/0.99  --clausify_out                          false
% 0.95/0.99  --sig_cnt_out                           false
% 0.95/0.99  --trig_cnt_out                          false
% 0.95/0.99  --trig_cnt_out_tolerance                1.
% 0.95/0.99  --trig_cnt_out_sk_spl                   false
% 0.95/0.99  --abstr_cl_out                          false
% 0.95/0.99  
% 0.95/0.99  ------ Global Options
% 0.95/0.99  
% 0.95/0.99  --schedule                              default
% 0.95/0.99  --add_important_lit                     false
% 0.95/0.99  --prop_solver_per_cl                    1000
% 0.95/0.99  --min_unsat_core                        false
% 0.95/0.99  --soft_assumptions                      false
% 0.95/0.99  --soft_lemma_size                       3
% 0.95/0.99  --prop_impl_unit_size                   0
% 0.95/0.99  --prop_impl_unit                        []
% 0.95/0.99  --share_sel_clauses                     true
% 0.95/0.99  --reset_solvers                         false
% 0.95/0.99  --bc_imp_inh                            [conj_cone]
% 0.95/0.99  --conj_cone_tolerance                   3.
% 0.95/0.99  --extra_neg_conj                        none
% 0.95/0.99  --large_theory_mode                     true
% 0.95/0.99  --prolific_symb_bound                   200
% 0.95/0.99  --lt_threshold                          2000
% 0.95/0.99  --clause_weak_htbl                      true
% 0.95/0.99  --gc_record_bc_elim                     false
% 0.95/0.99  
% 0.95/0.99  ------ Preprocessing Options
% 0.95/0.99  
% 0.95/0.99  --preprocessing_flag                    true
% 0.95/0.99  --time_out_prep_mult                    0.1
% 0.95/0.99  --splitting_mode                        input
% 0.95/0.99  --splitting_grd                         true
% 0.95/0.99  --splitting_cvd                         false
% 0.95/0.99  --splitting_cvd_svl                     false
% 0.95/0.99  --splitting_nvd                         32
% 0.95/0.99  --sub_typing                            true
% 0.95/0.99  --prep_gs_sim                           true
% 0.95/0.99  --prep_unflatten                        true
% 0.95/0.99  --prep_res_sim                          true
% 0.95/0.99  --prep_upred                            true
% 0.95/0.99  --prep_sem_filter                       exhaustive
% 0.95/0.99  --prep_sem_filter_out                   false
% 0.95/0.99  --pred_elim                             true
% 0.95/0.99  --res_sim_input                         true
% 0.95/0.99  --eq_ax_congr_red                       true
% 0.95/0.99  --pure_diseq_elim                       true
% 0.95/0.99  --brand_transform                       false
% 0.95/0.99  --non_eq_to_eq                          false
% 0.95/0.99  --prep_def_merge                        true
% 0.95/0.99  --prep_def_merge_prop_impl              false
% 0.95/0.99  --prep_def_merge_mbd                    true
% 0.95/0.99  --prep_def_merge_tr_red                 false
% 0.95/0.99  --prep_def_merge_tr_cl                  false
% 0.95/0.99  --smt_preprocessing                     true
% 0.95/0.99  --smt_ac_axioms                         fast
% 0.95/0.99  --preprocessed_out                      false
% 0.95/0.99  --preprocessed_stats                    false
% 0.95/0.99  
% 0.95/0.99  ------ Abstraction refinement Options
% 0.95/0.99  
% 0.95/0.99  --abstr_ref                             []
% 0.95/0.99  --abstr_ref_prep                        false
% 0.95/0.99  --abstr_ref_until_sat                   false
% 0.95/0.99  --abstr_ref_sig_restrict                funpre
% 0.95/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.95/0.99  --abstr_ref_under                       []
% 0.95/0.99  
% 0.95/0.99  ------ SAT Options
% 0.95/0.99  
% 0.95/0.99  --sat_mode                              false
% 0.95/0.99  --sat_fm_restart_options                ""
% 0.95/0.99  --sat_gr_def                            false
% 0.95/0.99  --sat_epr_types                         true
% 0.95/0.99  --sat_non_cyclic_types                  false
% 0.95/0.99  --sat_finite_models                     false
% 0.95/0.99  --sat_fm_lemmas                         false
% 0.95/0.99  --sat_fm_prep                           false
% 0.95/0.99  --sat_fm_uc_incr                        true
% 0.95/0.99  --sat_out_model                         small
% 0.95/0.99  --sat_out_clauses                       false
% 0.95/0.99  
% 0.95/0.99  ------ QBF Options
% 0.95/0.99  
% 0.95/0.99  --qbf_mode                              false
% 0.95/0.99  --qbf_elim_univ                         false
% 0.95/0.99  --qbf_dom_inst                          none
% 0.95/0.99  --qbf_dom_pre_inst                      false
% 0.95/0.99  --qbf_sk_in                             false
% 0.95/0.99  --qbf_pred_elim                         true
% 0.95/0.99  --qbf_split                             512
% 0.95/0.99  
% 0.95/0.99  ------ BMC1 Options
% 0.95/0.99  
% 0.95/0.99  --bmc1_incremental                      false
% 0.95/0.99  --bmc1_axioms                           reachable_all
% 0.95/0.99  --bmc1_min_bound                        0
% 0.95/0.99  --bmc1_max_bound                        -1
% 0.95/0.99  --bmc1_max_bound_default                -1
% 0.95/0.99  --bmc1_symbol_reachability              true
% 0.95/0.99  --bmc1_property_lemmas                  false
% 0.95/0.99  --bmc1_k_induction                      false
% 0.95/0.99  --bmc1_non_equiv_states                 false
% 0.95/0.99  --bmc1_deadlock                         false
% 0.95/0.99  --bmc1_ucm                              false
% 0.95/0.99  --bmc1_add_unsat_core                   none
% 0.95/0.99  --bmc1_unsat_core_children              false
% 0.95/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.95/0.99  --bmc1_out_stat                         full
% 0.95/0.99  --bmc1_ground_init                      false
% 0.95/0.99  --bmc1_pre_inst_next_state              false
% 0.95/0.99  --bmc1_pre_inst_state                   false
% 0.95/0.99  --bmc1_pre_inst_reach_state             false
% 0.95/0.99  --bmc1_out_unsat_core                   false
% 0.95/0.99  --bmc1_aig_witness_out                  false
% 0.95/0.99  --bmc1_verbose                          false
% 0.95/0.99  --bmc1_dump_clauses_tptp                false
% 0.95/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.95/0.99  --bmc1_dump_file                        -
% 0.95/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.95/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.95/0.99  --bmc1_ucm_extend_mode                  1
% 0.95/0.99  --bmc1_ucm_init_mode                    2
% 0.95/0.99  --bmc1_ucm_cone_mode                    none
% 0.95/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.95/0.99  --bmc1_ucm_relax_model                  4
% 0.95/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.95/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.95/0.99  --bmc1_ucm_layered_model                none
% 0.95/0.99  --bmc1_ucm_max_lemma_size               10
% 0.95/0.99  
% 0.95/0.99  ------ AIG Options
% 0.95/0.99  
% 0.95/0.99  --aig_mode                              false
% 0.95/0.99  
% 0.95/0.99  ------ Instantiation Options
% 0.95/0.99  
% 0.95/0.99  --instantiation_flag                    true
% 0.95/0.99  --inst_sos_flag                         false
% 0.95/0.99  --inst_sos_phase                        true
% 0.95/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.95/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.95/0.99  --inst_lit_sel_side                     none
% 0.95/0.99  --inst_solver_per_active                1400
% 0.95/0.99  --inst_solver_calls_frac                1.
% 0.95/0.99  --inst_passive_queue_type               priority_queues
% 0.95/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.95/0.99  --inst_passive_queues_freq              [25;2]
% 0.95/0.99  --inst_dismatching                      true
% 0.95/0.99  --inst_eager_unprocessed_to_passive     true
% 0.95/0.99  --inst_prop_sim_given                   true
% 0.95/0.99  --inst_prop_sim_new                     false
% 0.95/0.99  --inst_subs_new                         false
% 0.95/0.99  --inst_eq_res_simp                      false
% 0.95/0.99  --inst_subs_given                       false
% 0.95/0.99  --inst_orphan_elimination               true
% 0.95/0.99  --inst_learning_loop_flag               true
% 0.95/0.99  --inst_learning_start                   3000
% 0.95/0.99  --inst_learning_factor                  2
% 0.95/0.99  --inst_start_prop_sim_after_learn       3
% 0.95/0.99  --inst_sel_renew                        solver
% 0.95/0.99  --inst_lit_activity_flag                true
% 0.95/0.99  --inst_restr_to_given                   false
% 0.95/0.99  --inst_activity_threshold               500
% 0.95/0.99  --inst_out_proof                        true
% 0.95/0.99  
% 0.95/0.99  ------ Resolution Options
% 0.95/0.99  
% 0.95/0.99  --resolution_flag                       false
% 0.95/0.99  --res_lit_sel                           adaptive
% 0.95/0.99  --res_lit_sel_side                      none
% 0.95/0.99  --res_ordering                          kbo
% 0.95/0.99  --res_to_prop_solver                    active
% 0.95/1.00  --res_prop_simpl_new                    false
% 0.95/1.00  --res_prop_simpl_given                  true
% 0.95/1.00  --res_passive_queue_type                priority_queues
% 0.95/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.95/1.00  --res_passive_queues_freq               [15;5]
% 0.95/1.00  --res_forward_subs                      full
% 0.95/1.00  --res_backward_subs                     full
% 0.95/1.00  --res_forward_subs_resolution           true
% 0.95/1.00  --res_backward_subs_resolution          true
% 0.95/1.00  --res_orphan_elimination                true
% 0.95/1.00  --res_time_limit                        2.
% 0.95/1.00  --res_out_proof                         true
% 0.95/1.00  
% 0.95/1.00  ------ Superposition Options
% 0.95/1.00  
% 0.95/1.00  --superposition_flag                    true
% 0.95/1.00  --sup_passive_queue_type                priority_queues
% 0.95/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.95/1.00  --sup_passive_queues_freq               [8;1;4]
% 0.95/1.00  --demod_completeness_check              fast
% 0.95/1.00  --demod_use_ground                      true
% 0.95/1.00  --sup_to_prop_solver                    passive
% 0.95/1.00  --sup_prop_simpl_new                    true
% 0.95/1.00  --sup_prop_simpl_given                  true
% 0.95/1.00  --sup_fun_splitting                     false
% 0.95/1.00  --sup_smt_interval                      50000
% 0.95/1.00  
% 0.95/1.00  ------ Superposition Simplification Setup
% 0.95/1.00  
% 0.95/1.00  --sup_indices_passive                   []
% 0.95/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 0.95/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/1.00  --sup_full_bw                           [BwDemod]
% 0.95/1.00  --sup_immed_triv                        [TrivRules]
% 0.95/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.95/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/1.00  --sup_immed_bw_main                     []
% 0.95/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 0.95/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/1.00  
% 0.95/1.00  ------ Combination Options
% 0.95/1.00  
% 0.95/1.00  --comb_res_mult                         3
% 0.95/1.00  --comb_sup_mult                         2
% 0.95/1.00  --comb_inst_mult                        10
% 0.95/1.00  
% 0.95/1.00  ------ Debug Options
% 0.95/1.00  
% 0.95/1.00  --dbg_backtrace                         false
% 0.95/1.00  --dbg_dump_prop_clauses                 false
% 0.95/1.00  --dbg_dump_prop_clauses_file            -
% 0.95/1.00  --dbg_out_stat                          false
% 0.95/1.00  
% 0.95/1.00  
% 0.95/1.00  
% 0.95/1.00  
% 0.95/1.00  ------ Proving...
% 0.95/1.00  
% 0.95/1.00  
% 0.95/1.00  % SZS status Theorem for theBenchmark.p
% 0.95/1.00  
% 0.95/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 0.95/1.00  
% 0.95/1.00  fof(f2,axiom,(
% 0.95/1.00    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/1.00  
% 0.95/1.00  fof(f20,plain,(
% 0.95/1.00    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.95/1.00    inference(cnf_transformation,[],[f2])).
% 0.95/1.00  
% 0.95/1.00  fof(f1,axiom,(
% 0.95/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/1.00  
% 0.95/1.00  fof(f9,plain,(
% 0.95/1.00    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1))),
% 0.95/1.00    inference(ennf_transformation,[],[f1])).
% 0.95/1.00  
% 0.95/1.00  fof(f19,plain,(
% 0.95/1.00    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) = X1 | ~r2_hidden(X0,X1)) )),
% 0.95/1.00    inference(cnf_transformation,[],[f9])).
% 0.95/1.00  
% 0.95/1.00  fof(f3,axiom,(
% 0.95/1.00    ! [X0,X1] : (v1_relat_1(X1) => (k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))))),
% 0.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/1.00  
% 0.95/1.00  fof(f10,plain,(
% 0.95/1.00    ! [X0,X1] : ((k6_relat_1(X0) = X1 <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) <=> (X2 = X3 & r2_hidden(X2,X0)))) | ~v1_relat_1(X1))),
% 0.95/1.00    inference(ennf_transformation,[],[f3])).
% 0.95/1.00  
% 0.95/1.00  fof(f12,plain,(
% 0.95/1.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : (((X2 != X3 | ~r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | (X2 != X3 | ~r2_hidden(X2,X0))) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 0.95/1.00    inference(nnf_transformation,[],[f10])).
% 0.95/1.00  
% 0.95/1.00  fof(f13,plain,(
% 0.95/1.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) | X2 != X3 | ~r2_hidden(X2,X0)) & ((X2 = X3 & r2_hidden(X2,X0)) | ~r2_hidden(k4_tarski(X2,X3),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 0.95/1.00    inference(flattening,[],[f12])).
% 0.95/1.00  
% 0.95/1.00  fof(f14,plain,(
% 0.95/1.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 0.95/1.00    inference(rectify,[],[f13])).
% 0.95/1.00  
% 0.95/1.00  fof(f15,plain,(
% 0.95/1.00    ! [X1,X0] : (? [X2,X3] : ((X2 != X3 | ~r2_hidden(X2,X0) | ~r2_hidden(k4_tarski(X2,X3),X1)) & ((X2 = X3 & r2_hidden(X2,X0)) | r2_hidden(k4_tarski(X2,X3),X1))) => ((sK0(X0,X1) != sK1(X0,X1) | ~r2_hidden(sK0(X0,X1),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & ((sK0(X0,X1) = sK1(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1))))),
% 0.95/1.00    introduced(choice_axiom,[])).
% 0.95/1.00  
% 0.95/1.00  fof(f16,plain,(
% 0.95/1.00    ! [X0,X1] : (((k6_relat_1(X0) = X1 | ((sK0(X0,X1) != sK1(X0,X1) | ~r2_hidden(sK0(X0,X1),X0) | ~r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)) & ((sK0(X0,X1) = sK1(X0,X1) & r2_hidden(sK0(X0,X1),X0)) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)))) & (! [X4,X5] : ((r2_hidden(k4_tarski(X4,X5),X1) | X4 != X5 | ~r2_hidden(X4,X0)) & ((X4 = X5 & r2_hidden(X4,X0)) | ~r2_hidden(k4_tarski(X4,X5),X1))) | k6_relat_1(X0) != X1)) | ~v1_relat_1(X1))),
% 0.95/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f15])).
% 0.95/1.00  
% 0.95/1.00  fof(f24,plain,(
% 0.95/1.00    ( ! [X0,X1] : (k6_relat_1(X0) = X1 | r2_hidden(sK0(X0,X1),X0) | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) | ~v1_relat_1(X1)) )),
% 0.95/1.00    inference(cnf_transformation,[],[f16])).
% 0.95/1.00  
% 0.95/1.00  fof(f4,axiom,(
% 0.95/1.00    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/1.00  
% 0.95/1.00  fof(f8,plain,(
% 0.95/1.00    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.95/1.00    inference(unused_predicate_definition_removal,[],[f4])).
% 0.95/1.00  
% 0.95/1.00  fof(f11,plain,(
% 0.95/1.00    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.95/1.00    inference(ennf_transformation,[],[f8])).
% 0.95/1.00  
% 0.95/1.00  fof(f17,plain,(
% 0.95/1.00    ! [X0] : (? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => (! [X3,X2] : k4_tarski(X2,X3) != sK2(X0) & r2_hidden(sK2(X0),X0)))),
% 0.95/1.00    introduced(choice_axiom,[])).
% 0.95/1.00  
% 0.95/1.00  fof(f18,plain,(
% 0.95/1.00    ! [X0] : (v1_relat_1(X0) | (! [X2,X3] : k4_tarski(X2,X3) != sK2(X0) & r2_hidden(sK2(X0),X0)))),
% 0.95/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f17])).
% 0.95/1.00  
% 0.95/1.00  fof(f27,plain,(
% 0.95/1.00    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK2(X0),X0)) )),
% 0.95/1.00    inference(cnf_transformation,[],[f18])).
% 0.95/1.00  
% 0.95/1.00  fof(f5,conjecture,(
% 0.95/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.95/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/1.00  
% 0.95/1.00  fof(f6,negated_conjecture,(
% 0.95/1.00    ~k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.95/1.00    inference(negated_conjecture,[],[f5])).
% 0.95/1.00  
% 0.95/1.00  fof(f7,plain,(
% 0.95/1.00    k1_xboole_0 != k6_relat_1(k1_xboole_0)),
% 0.95/1.00    inference(flattening,[],[f6])).
% 0.95/1.00  
% 0.95/1.00  fof(f29,plain,(
% 0.95/1.00    k1_xboole_0 != k6_relat_1(k1_xboole_0)),
% 0.95/1.00    inference(cnf_transformation,[],[f7])).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1,plain,
% 0.95/1.00      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 0.95/1.00      inference(cnf_transformation,[],[f20]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_2140,plain,
% 0.95/1.00      ( k2_xboole_0(k1_tarski(sK0(k1_xboole_0,X0)),k1_xboole_0) != k1_xboole_0 ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_2143,plain,
% 0.95/1.00      ( k2_xboole_0(k1_tarski(sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0) != k1_xboole_0 ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_2140]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1221,plain,
% 0.95/1.00      ( k2_xboole_0(k1_tarski(k4_tarski(sK0(X0,k1_xboole_0),sK1(X0,k1_xboole_0))),k1_xboole_0) != k1_xboole_0 ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1224,plain,
% 0.95/1.00      ( k2_xboole_0(k1_tarski(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0))),k1_xboole_0) != k1_xboole_0 ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_1221]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_0,plain,
% 0.95/1.00      ( ~ r2_hidden(X0,X1) | k2_xboole_0(k1_tarski(X0),X1) = X1 ),
% 0.95/1.00      inference(cnf_transformation,[],[f19]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1008,plain,
% 0.95/1.00      ( ~ r2_hidden(sK0(X0,X1),X0)
% 0.95/1.00      | k2_xboole_0(k1_tarski(sK0(X0,X1)),X0) = X0 ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_1010,plain,
% 0.95/1.00      ( ~ r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 0.95/1.00      | k2_xboole_0(k1_tarski(sK0(k1_xboole_0,k1_xboole_0)),k1_xboole_0) = k1_xboole_0 ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_1008]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_4,plain,
% 0.95/1.00      ( r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1)
% 0.95/1.00      | r2_hidden(sK0(X0,X1),X0)
% 0.95/1.00      | ~ v1_relat_1(X1)
% 0.95/1.00      | k6_relat_1(X0) = X1 ),
% 0.95/1.00      inference(cnf_transformation,[],[f24]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_539,plain,
% 0.95/1.00      ( k6_relat_1(X0) = X1
% 0.95/1.00      | r2_hidden(k4_tarski(sK0(X0,X1),sK1(X0,X1)),X1) = iProver_top
% 0.95/1.00      | r2_hidden(sK0(X0,X1),X0) = iProver_top
% 0.95/1.00      | v1_relat_1(X1) != iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_542,plain,
% 0.95/1.00      ( k2_xboole_0(k1_tarski(X0),X1) = X1
% 0.95/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 0.95/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_810,plain,
% 0.95/1.00      ( k2_xboole_0(k1_tarski(k4_tarski(sK0(X0,X1),sK1(X0,X1))),X1) = X1
% 0.95/1.00      | k6_relat_1(X0) = X1
% 0.95/1.00      | r2_hidden(sK0(X0,X1),X0) = iProver_top
% 0.95/1.00      | v1_relat_1(X1) != iProver_top ),
% 0.95/1.00      inference(superposition,[status(thm)],[c_539,c_542]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_850,plain,
% 0.95/1.00      ( r2_hidden(sK0(X0,X1),X0)
% 0.95/1.00      | ~ v1_relat_1(X1)
% 0.95/1.00      | k2_xboole_0(k1_tarski(k4_tarski(sK0(X0,X1),sK1(X0,X1))),X1) = X1
% 0.95/1.00      | k6_relat_1(X0) = X1 ),
% 0.95/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_810]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_852,plain,
% 0.95/1.00      ( r2_hidden(sK0(k1_xboole_0,k1_xboole_0),k1_xboole_0)
% 0.95/1.00      | ~ v1_relat_1(k1_xboole_0)
% 0.95/1.00      | k2_xboole_0(k1_tarski(k4_tarski(sK0(k1_xboole_0,k1_xboole_0),sK1(k1_xboole_0,k1_xboole_0))),k1_xboole_0) = k1_xboole_0
% 0.95/1.00      | k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_850]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_671,plain,
% 0.95/1.00      ( k2_xboole_0(k1_tarski(sK2(k1_xboole_0)),k1_xboole_0) != k1_xboole_0 ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_646,plain,
% 0.95/1.00      ( ~ r2_hidden(sK2(X0),X0)
% 0.95/1.00      | k2_xboole_0(k1_tarski(sK2(X0)),X0) = X0 ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_648,plain,
% 0.95/1.00      ( ~ r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
% 0.95/1.00      | k2_xboole_0(k1_tarski(sK2(k1_xboole_0)),k1_xboole_0) = k1_xboole_0 ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_646]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_363,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_643,plain,
% 0.95/1.00      ( k6_relat_1(k1_xboole_0) != X0
% 0.95/1.00      | k1_xboole_0 != X0
% 0.95/1.00      | k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_363]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_644,plain,
% 0.95/1.00      ( k6_relat_1(k1_xboole_0) != k1_xboole_0
% 0.95/1.00      | k1_xboole_0 = k6_relat_1(k1_xboole_0)
% 0.95/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_643]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_362,plain,( X0 = X0 ),theory(equality) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_375,plain,
% 0.95/1.00      ( k1_xboole_0 = k1_xboole_0 ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_362]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_9,plain,
% 0.95/1.00      ( r2_hidden(sK2(X0),X0) | v1_relat_1(X0) ),
% 0.95/1.00      inference(cnf_transformation,[],[f27]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_12,plain,
% 0.95/1.00      ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
% 0.95/1.00      | v1_relat_1(k1_xboole_0) ),
% 0.95/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(c_10,negated_conjecture,
% 0.95/1.00      ( k1_xboole_0 != k6_relat_1(k1_xboole_0) ),
% 0.95/1.00      inference(cnf_transformation,[],[f29]) ).
% 0.95/1.00  
% 0.95/1.00  cnf(contradiction,plain,
% 0.95/1.00      ( $false ),
% 0.95/1.00      inference(minisat,
% 0.95/1.00                [status(thm)],
% 0.95/1.00                [c_2143,c_1224,c_1010,c_852,c_671,c_648,c_644,c_375,c_12,
% 0.95/1.00                 c_10]) ).
% 0.95/1.00  
% 0.95/1.00  
% 0.95/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 0.95/1.00  
% 0.95/1.00  ------                               Statistics
% 0.95/1.00  
% 0.95/1.00  ------ General
% 0.95/1.00  
% 0.95/1.00  abstr_ref_over_cycles:                  0
% 0.95/1.00  abstr_ref_under_cycles:                 0
% 0.95/1.00  gc_basic_clause_elim:                   0
% 0.95/1.00  forced_gc_time:                         0
% 0.95/1.00  parsing_time:                           0.009
% 0.95/1.00  unif_index_cands_time:                  0.
% 0.95/1.00  unif_index_add_time:                    0.
% 0.95/1.00  orderings_time:                         0.
% 0.95/1.00  out_proof_time:                         0.006
% 0.95/1.00  total_time:                             0.106
% 0.95/1.00  num_of_symbols:                         41
% 0.95/1.00  num_of_terms:                           1825
% 0.95/1.00  
% 0.95/1.00  ------ Preprocessing
% 0.95/1.00  
% 0.95/1.00  num_of_splits:                          0
% 0.95/1.00  num_of_split_atoms:                     0
% 0.95/1.00  num_of_reused_defs:                     0
% 0.95/1.00  num_eq_ax_congr_red:                    14
% 0.95/1.00  num_of_sem_filtered_clauses:            1
% 0.95/1.00  num_of_subtypes:                        0
% 0.95/1.00  monotx_restored_types:                  0
% 0.95/1.00  sat_num_of_epr_types:                   0
% 0.95/1.00  sat_num_of_non_cyclic_types:            0
% 0.95/1.00  sat_guarded_non_collapsed_types:        0
% 0.95/1.00  num_pure_diseq_elim:                    0
% 0.95/1.00  simp_replaced_by:                       0
% 0.95/1.00  res_preprocessed:                       48
% 0.95/1.00  prep_upred:                             0
% 0.95/1.00  prep_unflattend:                        12
% 0.95/1.00  smt_new_axioms:                         0
% 0.95/1.00  pred_elim_cands:                        2
% 0.95/1.00  pred_elim:                              0
% 0.95/1.00  pred_elim_cl:                           0
% 0.95/1.00  pred_elim_cycles:                       1
% 0.95/1.00  merged_defs:                            0
% 0.95/1.00  merged_defs_ncl:                        0
% 0.95/1.00  bin_hyper_res:                          0
% 0.95/1.00  prep_cycles:                            3
% 0.95/1.00  pred_elim_time:                         0.004
% 0.95/1.00  splitting_time:                         0.
% 0.95/1.00  sem_filter_time:                        0.
% 0.95/1.00  monotx_time:                            0.004
% 0.95/1.00  subtype_inf_time:                       0.
% 0.95/1.00  
% 0.95/1.00  ------ Problem properties
% 0.95/1.00  
% 0.95/1.00  clauses:                                11
% 0.95/1.00  conjectures:                            1
% 0.95/1.00  epr:                                    0
% 0.95/1.00  horn:                                   8
% 0.95/1.00  ground:                                 1
% 0.95/1.00  unary:                                  2
% 0.95/1.00  binary:                                 3
% 0.95/1.00  lits:                                   30
% 0.95/1.00  lits_eq:                                10
% 0.95/1.00  fd_pure:                                0
% 0.95/1.00  fd_pseudo:                              0
% 0.95/1.00  fd_cond:                                0
% 0.95/1.00  fd_pseudo_cond:                         4
% 0.95/1.00  ac_symbols:                             0
% 0.95/1.00  
% 0.95/1.00  ------ Propositional Solver
% 0.95/1.00  
% 0.95/1.00  prop_solver_calls:                      22
% 0.95/1.00  prop_fast_solver_calls:                 412
% 0.95/1.00  smt_solver_calls:                       0
% 0.95/1.00  smt_fast_solver_calls:                  0
% 0.95/1.00  prop_num_of_clauses:                    636
% 0.95/1.00  prop_preprocess_simplified:             2298
% 0.95/1.00  prop_fo_subsumed:                       5
% 0.95/1.00  prop_solver_time:                       0.
% 0.95/1.00  smt_solver_time:                        0.
% 0.95/1.00  smt_fast_solver_time:                   0.
% 0.95/1.00  prop_fast_solver_time:                  0.
% 0.95/1.00  prop_unsat_core_time:                   0.
% 0.95/1.00  
% 0.95/1.00  ------ QBF
% 0.95/1.00  
% 0.95/1.00  qbf_q_res:                              0
% 0.95/1.00  qbf_num_tautologies:                    0
% 0.95/1.00  qbf_prep_cycles:                        0
% 0.95/1.00  
% 0.95/1.00  ------ BMC1
% 0.95/1.00  
% 0.95/1.00  bmc1_current_bound:                     -1
% 0.95/1.00  bmc1_last_solved_bound:                 -1
% 0.95/1.00  bmc1_unsat_core_size:                   -1
% 0.95/1.00  bmc1_unsat_core_parents_size:           -1
% 0.95/1.00  bmc1_merge_next_fun:                    0
% 0.95/1.00  bmc1_unsat_core_clauses_time:           0.
% 0.95/1.00  
% 0.95/1.00  ------ Instantiation
% 0.95/1.00  
% 0.95/1.00  inst_num_of_clauses:                    222
% 0.95/1.00  inst_num_in_passive:                    33
% 0.95/1.00  inst_num_in_active:                     131
% 0.95/1.00  inst_num_in_unprocessed:                57
% 0.95/1.00  inst_num_of_loops:                      164
% 0.95/1.00  inst_num_of_learning_restarts:          0
% 0.95/1.00  inst_num_moves_active_passive:          29
% 0.95/1.00  inst_lit_activity:                      0
% 0.95/1.00  inst_lit_activity_moves:                0
% 0.95/1.00  inst_num_tautologies:                   0
% 0.95/1.00  inst_num_prop_implied:                  0
% 0.95/1.00  inst_num_existing_simplified:           0
% 0.95/1.00  inst_num_eq_res_simplified:             0
% 0.95/1.00  inst_num_child_elim:                    0
% 0.95/1.00  inst_num_of_dismatching_blockings:      100
% 0.95/1.00  inst_num_of_non_proper_insts:           325
% 0.95/1.00  inst_num_of_duplicates:                 0
% 0.95/1.00  inst_inst_num_from_inst_to_res:         0
% 0.95/1.00  inst_dismatching_checking_time:         0.
% 0.95/1.00  
% 0.95/1.00  ------ Resolution
% 0.95/1.00  
% 0.95/1.00  res_num_of_clauses:                     0
% 0.95/1.00  res_num_in_passive:                     0
% 0.95/1.00  res_num_in_active:                      0
% 0.95/1.00  res_num_of_loops:                       51
% 0.95/1.00  res_forward_subset_subsumed:            45
% 0.95/1.00  res_backward_subset_subsumed:           0
% 0.95/1.00  res_forward_subsumed:                   0
% 0.95/1.00  res_backward_subsumed:                  0
% 0.95/1.00  res_forward_subsumption_resolution:     0
% 0.95/1.00  res_backward_subsumption_resolution:    0
% 0.95/1.00  res_clause_to_clause_subsumption:       104
% 0.95/1.00  res_orphan_elimination:                 0
% 0.95/1.00  res_tautology_del:                      33
% 0.95/1.00  res_num_eq_res_simplified:              0
% 0.95/1.00  res_num_sel_changes:                    0
% 0.95/1.00  res_moves_from_active_to_pass:          0
% 0.95/1.00  
% 0.95/1.00  ------ Superposition
% 0.95/1.00  
% 0.95/1.00  sup_time_total:                         0.
% 0.95/1.00  sup_time_generating:                    0.
% 0.95/1.00  sup_time_sim_full:                      0.
% 0.95/1.00  sup_time_sim_immed:                     0.
% 0.95/1.00  
% 0.95/1.00  sup_num_of_clauses:                     54
% 0.95/1.00  sup_num_in_active:                      32
% 0.95/1.00  sup_num_in_passive:                     22
% 0.95/1.00  sup_num_of_loops:                       32
% 0.95/1.00  sup_fw_superposition:                   14
% 0.95/1.00  sup_bw_superposition:                   37
% 0.95/1.00  sup_immediate_simplified:               5
% 0.95/1.00  sup_given_eliminated:                   0
% 0.95/1.00  comparisons_done:                       0
% 0.95/1.00  comparisons_avoided:                    30
% 0.95/1.00  
% 0.95/1.00  ------ Simplifications
% 0.95/1.00  
% 0.95/1.00  
% 0.95/1.00  sim_fw_subset_subsumed:                 2
% 0.95/1.00  sim_bw_subset_subsumed:                 0
% 0.95/1.00  sim_fw_subsumed:                        2
% 0.95/1.00  sim_bw_subsumed:                        1
% 0.95/1.00  sim_fw_subsumption_res:                 0
% 0.95/1.00  sim_bw_subsumption_res:                 0
% 0.95/1.00  sim_tautology_del:                      1
% 0.95/1.00  sim_eq_tautology_del:                   2
% 0.95/1.00  sim_eq_res_simp:                        0
% 0.95/1.00  sim_fw_demodulated:                     0
% 0.95/1.00  sim_bw_demodulated:                     0
% 0.95/1.00  sim_light_normalised:                   0
% 0.95/1.00  sim_joinable_taut:                      0
% 0.95/1.00  sim_joinable_simp:                      0
% 0.95/1.00  sim_ac_normalised:                      0
% 0.95/1.00  sim_smt_subsumption:                    0
% 0.95/1.00  
%------------------------------------------------------------------------------
