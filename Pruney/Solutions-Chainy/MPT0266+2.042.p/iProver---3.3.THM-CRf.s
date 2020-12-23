%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:28 EST 2020

% Result     : Theorem 0.84s
% Output     : CNFRefutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   44 (  61 expanded)
%              Number of clauses        :   10 (  10 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :  196 ( 220 expanded)
%              Number of equality atoms :   90 ( 108 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal clause size      :   14 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f14])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f15])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK1(X0,X1,X2) != X1
            & sK1(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( sK1(X0,X1,X2) = X1
          | sK1(X0,X1,X2) = X0
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK1(X0,X1,X2) != X1
              & sK1(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK1(X0,X1,X2),X2) )
          & ( sK1(X0,X1,X2) = X1
            | sK1(X0,X1,X2) = X0
            | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f29,f38])).

fof(f57,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X4,X4,X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f49])).

fof(f58,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_enumset1(X4,X4,X4,X1)) ),
    inference(equality_resolution,[],[f57])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) )
   => ( ~ r2_hidden(sK2,sK4)
      & k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ~ r2_hidden(sK2,sK4)
    & k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f8,f19])).

fof(f36,plain,(
    k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f51,plain,(
    k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4)) = k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(definition_unfolding,[],[f36,f27,f38,f38])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f9])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f22,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f22,f27])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(equality_resolution,[],[f43])).

fof(f37,plain,(
    ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_10,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_354,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13,negated_conjecture,
    ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4)) = k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_360,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_706,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK3)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_360])).

cnf(c_726,plain,
    ( r2_hidden(sK2,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_354,c_706])).

cnf(c_12,negated_conjecture,
    ( ~ r2_hidden(sK2,sK4) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_14,plain,
    ( r2_hidden(sK2,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_726,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:31:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.84/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.84/0.99  
% 0.84/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.84/0.99  
% 0.84/0.99  ------  iProver source info
% 0.84/0.99  
% 0.84/0.99  git: date: 2020-06-30 10:37:57 +0100
% 0.84/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.84/0.99  git: non_committed_changes: false
% 0.84/0.99  git: last_make_outside_of_git: false
% 0.84/0.99  
% 0.84/0.99  ------ 
% 0.84/0.99  
% 0.84/0.99  ------ Input Options
% 0.84/0.99  
% 0.84/0.99  --out_options                           all
% 0.84/0.99  --tptp_safe_out                         true
% 0.84/0.99  --problem_path                          ""
% 0.84/0.99  --include_path                          ""
% 0.84/0.99  --clausifier                            res/vclausify_rel
% 0.84/0.99  --clausifier_options                    --mode clausify
% 0.84/0.99  --stdin                                 false
% 0.84/0.99  --stats_out                             all
% 0.84/0.99  
% 0.84/0.99  ------ General Options
% 0.84/0.99  
% 0.84/0.99  --fof                                   false
% 0.84/0.99  --time_out_real                         305.
% 0.84/0.99  --time_out_virtual                      -1.
% 0.84/0.99  --symbol_type_check                     false
% 0.84/0.99  --clausify_out                          false
% 0.84/0.99  --sig_cnt_out                           false
% 0.84/0.99  --trig_cnt_out                          false
% 0.84/0.99  --trig_cnt_out_tolerance                1.
% 0.84/0.99  --trig_cnt_out_sk_spl                   false
% 0.84/0.99  --abstr_cl_out                          false
% 0.84/0.99  
% 0.84/0.99  ------ Global Options
% 0.84/0.99  
% 0.84/0.99  --schedule                              default
% 0.84/0.99  --add_important_lit                     false
% 0.84/0.99  --prop_solver_per_cl                    1000
% 0.84/0.99  --min_unsat_core                        false
% 0.84/0.99  --soft_assumptions                      false
% 0.84/0.99  --soft_lemma_size                       3
% 0.84/0.99  --prop_impl_unit_size                   0
% 0.84/0.99  --prop_impl_unit                        []
% 0.84/0.99  --share_sel_clauses                     true
% 0.84/0.99  --reset_solvers                         false
% 0.84/0.99  --bc_imp_inh                            [conj_cone]
% 0.84/0.99  --conj_cone_tolerance                   3.
% 0.84/0.99  --extra_neg_conj                        none
% 0.84/0.99  --large_theory_mode                     true
% 0.84/0.99  --prolific_symb_bound                   200
% 0.84/0.99  --lt_threshold                          2000
% 0.84/0.99  --clause_weak_htbl                      true
% 0.84/0.99  --gc_record_bc_elim                     false
% 0.84/0.99  
% 0.84/0.99  ------ Preprocessing Options
% 0.84/0.99  
% 0.84/0.99  --preprocessing_flag                    true
% 0.84/0.99  --time_out_prep_mult                    0.1
% 0.84/0.99  --splitting_mode                        input
% 0.84/0.99  --splitting_grd                         true
% 0.84/0.99  --splitting_cvd                         false
% 0.84/0.99  --splitting_cvd_svl                     false
% 0.84/0.99  --splitting_nvd                         32
% 0.84/0.99  --sub_typing                            true
% 0.84/0.99  --prep_gs_sim                           true
% 0.84/0.99  --prep_unflatten                        true
% 0.84/0.99  --prep_res_sim                          true
% 0.84/0.99  --prep_upred                            true
% 0.84/0.99  --prep_sem_filter                       exhaustive
% 0.84/0.99  --prep_sem_filter_out                   false
% 0.84/0.99  --pred_elim                             true
% 0.84/0.99  --res_sim_input                         true
% 0.84/0.99  --eq_ax_congr_red                       true
% 0.84/0.99  --pure_diseq_elim                       true
% 0.84/0.99  --brand_transform                       false
% 0.84/0.99  --non_eq_to_eq                          false
% 0.84/0.99  --prep_def_merge                        true
% 0.84/0.99  --prep_def_merge_prop_impl              false
% 0.84/0.99  --prep_def_merge_mbd                    true
% 0.84/0.99  --prep_def_merge_tr_red                 false
% 0.84/0.99  --prep_def_merge_tr_cl                  false
% 0.84/0.99  --smt_preprocessing                     true
% 0.84/0.99  --smt_ac_axioms                         fast
% 0.84/0.99  --preprocessed_out                      false
% 0.84/0.99  --preprocessed_stats                    false
% 0.84/0.99  
% 0.84/0.99  ------ Abstraction refinement Options
% 0.84/0.99  
% 0.84/0.99  --abstr_ref                             []
% 0.84/0.99  --abstr_ref_prep                        false
% 0.84/0.99  --abstr_ref_until_sat                   false
% 0.84/0.99  --abstr_ref_sig_restrict                funpre
% 0.84/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.84/0.99  --abstr_ref_under                       []
% 0.84/0.99  
% 0.84/0.99  ------ SAT Options
% 0.84/0.99  
% 0.84/0.99  --sat_mode                              false
% 0.84/0.99  --sat_fm_restart_options                ""
% 0.84/0.99  --sat_gr_def                            false
% 0.84/0.99  --sat_epr_types                         true
% 0.84/0.99  --sat_non_cyclic_types                  false
% 0.84/0.99  --sat_finite_models                     false
% 0.84/0.99  --sat_fm_lemmas                         false
% 0.84/0.99  --sat_fm_prep                           false
% 0.84/0.99  --sat_fm_uc_incr                        true
% 0.84/0.99  --sat_out_model                         small
% 0.84/0.99  --sat_out_clauses                       false
% 0.84/0.99  
% 0.84/0.99  ------ QBF Options
% 0.84/0.99  
% 0.84/0.99  --qbf_mode                              false
% 0.84/0.99  --qbf_elim_univ                         false
% 0.84/0.99  --qbf_dom_inst                          none
% 0.84/0.99  --qbf_dom_pre_inst                      false
% 0.84/0.99  --qbf_sk_in                             false
% 0.84/0.99  --qbf_pred_elim                         true
% 0.84/0.99  --qbf_split                             512
% 0.84/0.99  
% 0.84/0.99  ------ BMC1 Options
% 0.84/0.99  
% 0.84/0.99  --bmc1_incremental                      false
% 0.84/0.99  --bmc1_axioms                           reachable_all
% 0.84/0.99  --bmc1_min_bound                        0
% 0.84/0.99  --bmc1_max_bound                        -1
% 0.84/0.99  --bmc1_max_bound_default                -1
% 0.84/0.99  --bmc1_symbol_reachability              true
% 0.84/0.99  --bmc1_property_lemmas                  false
% 0.84/0.99  --bmc1_k_induction                      false
% 0.84/0.99  --bmc1_non_equiv_states                 false
% 0.84/0.99  --bmc1_deadlock                         false
% 0.84/0.99  --bmc1_ucm                              false
% 0.84/0.99  --bmc1_add_unsat_core                   none
% 0.84/0.99  --bmc1_unsat_core_children              false
% 0.84/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.84/0.99  --bmc1_out_stat                         full
% 0.84/0.99  --bmc1_ground_init                      false
% 0.84/0.99  --bmc1_pre_inst_next_state              false
% 0.84/0.99  --bmc1_pre_inst_state                   false
% 0.84/0.99  --bmc1_pre_inst_reach_state             false
% 0.84/0.99  --bmc1_out_unsat_core                   false
% 0.84/0.99  --bmc1_aig_witness_out                  false
% 0.84/0.99  --bmc1_verbose                          false
% 0.84/0.99  --bmc1_dump_clauses_tptp                false
% 0.84/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.84/0.99  --bmc1_dump_file                        -
% 0.84/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.84/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.84/0.99  --bmc1_ucm_extend_mode                  1
% 0.84/0.99  --bmc1_ucm_init_mode                    2
% 0.84/0.99  --bmc1_ucm_cone_mode                    none
% 0.84/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.84/0.99  --bmc1_ucm_relax_model                  4
% 0.84/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.84/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.84/0.99  --bmc1_ucm_layered_model                none
% 0.84/0.99  --bmc1_ucm_max_lemma_size               10
% 0.84/0.99  
% 0.84/0.99  ------ AIG Options
% 0.84/0.99  
% 0.84/0.99  --aig_mode                              false
% 0.84/0.99  
% 0.84/0.99  ------ Instantiation Options
% 0.84/0.99  
% 0.84/0.99  --instantiation_flag                    true
% 0.84/0.99  --inst_sos_flag                         false
% 0.84/0.99  --inst_sos_phase                        true
% 0.84/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.84/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.84/0.99  --inst_lit_sel_side                     num_symb
% 0.84/0.99  --inst_solver_per_active                1400
% 0.84/0.99  --inst_solver_calls_frac                1.
% 0.84/0.99  --inst_passive_queue_type               priority_queues
% 0.84/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.84/0.99  --inst_passive_queues_freq              [25;2]
% 0.84/0.99  --inst_dismatching                      true
% 0.84/0.99  --inst_eager_unprocessed_to_passive     true
% 0.84/0.99  --inst_prop_sim_given                   true
% 0.84/0.99  --inst_prop_sim_new                     false
% 0.84/0.99  --inst_subs_new                         false
% 0.84/0.99  --inst_eq_res_simp                      false
% 0.84/0.99  --inst_subs_given                       false
% 0.84/0.99  --inst_orphan_elimination               true
% 0.84/0.99  --inst_learning_loop_flag               true
% 0.84/0.99  --inst_learning_start                   3000
% 0.84/0.99  --inst_learning_factor                  2
% 0.84/0.99  --inst_start_prop_sim_after_learn       3
% 0.84/0.99  --inst_sel_renew                        solver
% 0.84/0.99  --inst_lit_activity_flag                true
% 0.84/0.99  --inst_restr_to_given                   false
% 0.84/0.99  --inst_activity_threshold               500
% 0.84/0.99  --inst_out_proof                        true
% 0.84/0.99  
% 0.84/0.99  ------ Resolution Options
% 0.84/0.99  
% 0.84/0.99  --resolution_flag                       true
% 0.84/0.99  --res_lit_sel                           adaptive
% 0.84/0.99  --res_lit_sel_side                      none
% 0.84/0.99  --res_ordering                          kbo
% 0.84/0.99  --res_to_prop_solver                    active
% 0.84/0.99  --res_prop_simpl_new                    false
% 0.84/0.99  --res_prop_simpl_given                  true
% 0.84/0.99  --res_passive_queue_type                priority_queues
% 0.84/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.84/0.99  --res_passive_queues_freq               [15;5]
% 0.84/0.99  --res_forward_subs                      full
% 0.84/0.99  --res_backward_subs                     full
% 0.84/0.99  --res_forward_subs_resolution           true
% 0.84/0.99  --res_backward_subs_resolution          true
% 0.84/0.99  --res_orphan_elimination                true
% 0.84/0.99  --res_time_limit                        2.
% 0.84/0.99  --res_out_proof                         true
% 0.84/0.99  
% 0.84/0.99  ------ Superposition Options
% 0.84/0.99  
% 0.84/0.99  --superposition_flag                    true
% 0.84/0.99  --sup_passive_queue_type                priority_queues
% 0.84/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.84/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.84/0.99  --demod_completeness_check              fast
% 0.84/0.99  --demod_use_ground                      true
% 0.84/0.99  --sup_to_prop_solver                    passive
% 0.84/0.99  --sup_prop_simpl_new                    true
% 0.84/0.99  --sup_prop_simpl_given                  true
% 0.84/0.99  --sup_fun_splitting                     false
% 0.84/0.99  --sup_smt_interval                      50000
% 0.84/0.99  
% 0.84/0.99  ------ Superposition Simplification Setup
% 0.84/0.99  
% 0.84/0.99  --sup_indices_passive                   []
% 0.84/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.84/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.84/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.84/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.84/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.84/0.99  --sup_full_bw                           [BwDemod]
% 0.84/0.99  --sup_immed_triv                        [TrivRules]
% 0.84/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.84/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.84/0.99  --sup_immed_bw_main                     []
% 0.84/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.84/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.84/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.84/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.84/0.99  
% 0.84/0.99  ------ Combination Options
% 0.84/0.99  
% 0.84/0.99  --comb_res_mult                         3
% 0.84/0.99  --comb_sup_mult                         2
% 0.84/0.99  --comb_inst_mult                        10
% 0.84/0.99  
% 0.84/0.99  ------ Debug Options
% 0.84/0.99  
% 0.84/0.99  --dbg_backtrace                         false
% 0.84/0.99  --dbg_dump_prop_clauses                 false
% 0.84/0.99  --dbg_dump_prop_clauses_file            -
% 0.84/0.99  --dbg_out_stat                          false
% 0.84/0.99  ------ Parsing...
% 0.84/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.84/0.99  
% 0.84/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.84/0.99  
% 0.84/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.84/0.99  
% 0.84/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.84/0.99  ------ Proving...
% 0.84/0.99  ------ Problem Properties 
% 0.84/0.99  
% 0.84/0.99  
% 0.84/0.99  clauses                                 14
% 0.84/0.99  conjectures                             2
% 0.84/0.99  EPR                                     1
% 0.84/0.99  Horn                                    10
% 0.84/0.99  unary                                   4
% 0.84/0.99  binary                                  2
% 0.84/0.99  lits                                    34
% 0.84/0.99  lits eq                                 13
% 0.84/0.99  fd_pure                                 0
% 0.84/0.99  fd_pseudo                               0
% 0.84/0.99  fd_cond                                 0
% 0.84/0.99  fd_pseudo_cond                          6
% 0.84/0.99  AC symbols                              0
% 0.84/0.99  
% 0.84/0.99  ------ Schedule dynamic 5 is on 
% 0.84/0.99  
% 0.84/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.84/0.99  
% 0.84/0.99  
% 0.84/0.99  ------ 
% 0.84/0.99  Current options:
% 0.84/0.99  ------ 
% 0.84/0.99  
% 0.84/0.99  ------ Input Options
% 0.84/0.99  
% 0.84/0.99  --out_options                           all
% 0.84/0.99  --tptp_safe_out                         true
% 0.84/0.99  --problem_path                          ""
% 0.84/0.99  --include_path                          ""
% 0.84/0.99  --clausifier                            res/vclausify_rel
% 0.84/0.99  --clausifier_options                    --mode clausify
% 0.84/0.99  --stdin                                 false
% 0.84/0.99  --stats_out                             all
% 0.84/0.99  
% 0.84/0.99  ------ General Options
% 0.84/0.99  
% 0.84/0.99  --fof                                   false
% 0.84/0.99  --time_out_real                         305.
% 0.84/0.99  --time_out_virtual                      -1.
% 0.84/0.99  --symbol_type_check                     false
% 0.84/0.99  --clausify_out                          false
% 0.84/0.99  --sig_cnt_out                           false
% 0.84/0.99  --trig_cnt_out                          false
% 0.84/0.99  --trig_cnt_out_tolerance                1.
% 0.84/0.99  --trig_cnt_out_sk_spl                   false
% 0.84/0.99  --abstr_cl_out                          false
% 0.84/0.99  
% 0.84/0.99  ------ Global Options
% 0.84/0.99  
% 0.84/0.99  --schedule                              default
% 0.84/0.99  --add_important_lit                     false
% 0.84/0.99  --prop_solver_per_cl                    1000
% 0.84/0.99  --min_unsat_core                        false
% 0.84/0.99  --soft_assumptions                      false
% 0.84/0.99  --soft_lemma_size                       3
% 0.84/0.99  --prop_impl_unit_size                   0
% 0.84/0.99  --prop_impl_unit                        []
% 0.84/0.99  --share_sel_clauses                     true
% 0.84/0.99  --reset_solvers                         false
% 0.84/0.99  --bc_imp_inh                            [conj_cone]
% 0.84/0.99  --conj_cone_tolerance                   3.
% 0.84/0.99  --extra_neg_conj                        none
% 0.84/0.99  --large_theory_mode                     true
% 0.84/0.99  --prolific_symb_bound                   200
% 0.84/0.99  --lt_threshold                          2000
% 0.84/0.99  --clause_weak_htbl                      true
% 0.84/0.99  --gc_record_bc_elim                     false
% 0.84/0.99  
% 0.84/0.99  ------ Preprocessing Options
% 0.84/0.99  
% 0.84/0.99  --preprocessing_flag                    true
% 0.84/0.99  --time_out_prep_mult                    0.1
% 0.84/0.99  --splitting_mode                        input
% 0.84/0.99  --splitting_grd                         true
% 0.84/0.99  --splitting_cvd                         false
% 0.84/0.99  --splitting_cvd_svl                     false
% 0.84/0.99  --splitting_nvd                         32
% 0.84/0.99  --sub_typing                            true
% 0.84/0.99  --prep_gs_sim                           true
% 0.84/0.99  --prep_unflatten                        true
% 0.84/0.99  --prep_res_sim                          true
% 0.84/0.99  --prep_upred                            true
% 0.84/0.99  --prep_sem_filter                       exhaustive
% 0.84/0.99  --prep_sem_filter_out                   false
% 0.84/0.99  --pred_elim                             true
% 0.84/0.99  --res_sim_input                         true
% 0.84/0.99  --eq_ax_congr_red                       true
% 0.84/0.99  --pure_diseq_elim                       true
% 0.84/0.99  --brand_transform                       false
% 0.84/0.99  --non_eq_to_eq                          false
% 0.84/0.99  --prep_def_merge                        true
% 0.84/0.99  --prep_def_merge_prop_impl              false
% 0.84/0.99  --prep_def_merge_mbd                    true
% 0.84/0.99  --prep_def_merge_tr_red                 false
% 0.84/0.99  --prep_def_merge_tr_cl                  false
% 0.84/0.99  --smt_preprocessing                     true
% 0.84/0.99  --smt_ac_axioms                         fast
% 0.84/0.99  --preprocessed_out                      false
% 0.84/0.99  --preprocessed_stats                    false
% 0.84/0.99  
% 0.84/0.99  ------ Abstraction refinement Options
% 0.84/0.99  
% 0.84/0.99  --abstr_ref                             []
% 0.84/0.99  --abstr_ref_prep                        false
% 0.84/0.99  --abstr_ref_until_sat                   false
% 0.84/0.99  --abstr_ref_sig_restrict                funpre
% 0.84/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.84/0.99  --abstr_ref_under                       []
% 0.84/0.99  
% 0.84/0.99  ------ SAT Options
% 0.84/0.99  
% 0.84/0.99  --sat_mode                              false
% 0.84/0.99  --sat_fm_restart_options                ""
% 0.84/0.99  --sat_gr_def                            false
% 0.84/0.99  --sat_epr_types                         true
% 0.84/0.99  --sat_non_cyclic_types                  false
% 0.84/0.99  --sat_finite_models                     false
% 0.84/0.99  --sat_fm_lemmas                         false
% 0.84/0.99  --sat_fm_prep                           false
% 0.84/0.99  --sat_fm_uc_incr                        true
% 0.84/0.99  --sat_out_model                         small
% 0.84/0.99  --sat_out_clauses                       false
% 0.84/0.99  
% 0.84/0.99  ------ QBF Options
% 0.84/0.99  
% 0.84/0.99  --qbf_mode                              false
% 0.84/0.99  --qbf_elim_univ                         false
% 0.84/0.99  --qbf_dom_inst                          none
% 0.84/0.99  --qbf_dom_pre_inst                      false
% 0.84/0.99  --qbf_sk_in                             false
% 0.84/0.99  --qbf_pred_elim                         true
% 0.84/0.99  --qbf_split                             512
% 0.84/0.99  
% 0.84/0.99  ------ BMC1 Options
% 0.84/0.99  
% 0.84/0.99  --bmc1_incremental                      false
% 0.84/0.99  --bmc1_axioms                           reachable_all
% 0.84/0.99  --bmc1_min_bound                        0
% 0.84/0.99  --bmc1_max_bound                        -1
% 0.84/0.99  --bmc1_max_bound_default                -1
% 0.84/0.99  --bmc1_symbol_reachability              true
% 0.84/0.99  --bmc1_property_lemmas                  false
% 0.84/0.99  --bmc1_k_induction                      false
% 0.84/0.99  --bmc1_non_equiv_states                 false
% 0.84/0.99  --bmc1_deadlock                         false
% 0.84/0.99  --bmc1_ucm                              false
% 0.84/0.99  --bmc1_add_unsat_core                   none
% 0.84/0.99  --bmc1_unsat_core_children              false
% 0.84/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.84/0.99  --bmc1_out_stat                         full
% 0.84/0.99  --bmc1_ground_init                      false
% 0.84/0.99  --bmc1_pre_inst_next_state              false
% 0.84/0.99  --bmc1_pre_inst_state                   false
% 0.84/0.99  --bmc1_pre_inst_reach_state             false
% 0.84/0.99  --bmc1_out_unsat_core                   false
% 0.84/0.99  --bmc1_aig_witness_out                  false
% 0.84/0.99  --bmc1_verbose                          false
% 0.84/0.99  --bmc1_dump_clauses_tptp                false
% 0.84/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.84/0.99  --bmc1_dump_file                        -
% 0.84/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.84/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.84/0.99  --bmc1_ucm_extend_mode                  1
% 0.84/0.99  --bmc1_ucm_init_mode                    2
% 0.84/0.99  --bmc1_ucm_cone_mode                    none
% 0.84/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.84/0.99  --bmc1_ucm_relax_model                  4
% 0.84/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.84/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.84/0.99  --bmc1_ucm_layered_model                none
% 0.84/0.99  --bmc1_ucm_max_lemma_size               10
% 0.84/0.99  
% 0.84/0.99  ------ AIG Options
% 0.84/0.99  
% 0.84/0.99  --aig_mode                              false
% 0.84/0.99  
% 0.84/0.99  ------ Instantiation Options
% 0.84/0.99  
% 0.84/0.99  --instantiation_flag                    true
% 0.84/0.99  --inst_sos_flag                         false
% 0.84/0.99  --inst_sos_phase                        true
% 0.84/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.84/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.84/0.99  --inst_lit_sel_side                     none
% 0.84/0.99  --inst_solver_per_active                1400
% 0.84/0.99  --inst_solver_calls_frac                1.
% 0.84/0.99  --inst_passive_queue_type               priority_queues
% 0.84/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.84/0.99  --inst_passive_queues_freq              [25;2]
% 0.84/0.99  --inst_dismatching                      true
% 0.84/0.99  --inst_eager_unprocessed_to_passive     true
% 0.84/0.99  --inst_prop_sim_given                   true
% 0.84/0.99  --inst_prop_sim_new                     false
% 0.84/0.99  --inst_subs_new                         false
% 0.84/0.99  --inst_eq_res_simp                      false
% 0.84/0.99  --inst_subs_given                       false
% 0.84/0.99  --inst_orphan_elimination               true
% 0.84/0.99  --inst_learning_loop_flag               true
% 0.84/0.99  --inst_learning_start                   3000
% 0.84/0.99  --inst_learning_factor                  2
% 0.84/0.99  --inst_start_prop_sim_after_learn       3
% 0.84/0.99  --inst_sel_renew                        solver
% 0.84/0.99  --inst_lit_activity_flag                true
% 0.84/0.99  --inst_restr_to_given                   false
% 0.84/0.99  --inst_activity_threshold               500
% 0.84/0.99  --inst_out_proof                        true
% 0.84/0.99  
% 0.84/0.99  ------ Resolution Options
% 0.84/0.99  
% 0.84/0.99  --resolution_flag                       false
% 0.84/0.99  --res_lit_sel                           adaptive
% 0.84/0.99  --res_lit_sel_side                      none
% 0.84/0.99  --res_ordering                          kbo
% 0.84/0.99  --res_to_prop_solver                    active
% 0.84/0.99  --res_prop_simpl_new                    false
% 0.84/0.99  --res_prop_simpl_given                  true
% 0.84/0.99  --res_passive_queue_type                priority_queues
% 0.84/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.84/0.99  --res_passive_queues_freq               [15;5]
% 0.84/0.99  --res_forward_subs                      full
% 0.84/0.99  --res_backward_subs                     full
% 0.84/0.99  --res_forward_subs_resolution           true
% 0.84/0.99  --res_backward_subs_resolution          true
% 0.84/0.99  --res_orphan_elimination                true
% 0.84/0.99  --res_time_limit                        2.
% 0.84/0.99  --res_out_proof                         true
% 0.84/0.99  
% 0.84/0.99  ------ Superposition Options
% 0.84/0.99  
% 0.84/0.99  --superposition_flag                    true
% 0.84/0.99  --sup_passive_queue_type                priority_queues
% 0.84/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.84/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.84/0.99  --demod_completeness_check              fast
% 0.84/0.99  --demod_use_ground                      true
% 0.84/0.99  --sup_to_prop_solver                    passive
% 0.84/0.99  --sup_prop_simpl_new                    true
% 0.84/0.99  --sup_prop_simpl_given                  true
% 0.84/0.99  --sup_fun_splitting                     false
% 0.84/0.99  --sup_smt_interval                      50000
% 0.84/0.99  
% 0.84/0.99  ------ Superposition Simplification Setup
% 0.84/0.99  
% 0.84/0.99  --sup_indices_passive                   []
% 0.84/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.84/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.84/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.84/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.84/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.84/0.99  --sup_full_bw                           [BwDemod]
% 0.84/0.99  --sup_immed_triv                        [TrivRules]
% 0.84/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.84/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.84/0.99  --sup_immed_bw_main                     []
% 0.84/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.84/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.84/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.84/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.84/0.99  
% 0.84/0.99  ------ Combination Options
% 0.84/0.99  
% 0.84/0.99  --comb_res_mult                         3
% 0.84/0.99  --comb_sup_mult                         2
% 0.84/0.99  --comb_inst_mult                        10
% 0.84/0.99  
% 0.84/0.99  ------ Debug Options
% 0.84/0.99  
% 0.84/0.99  --dbg_backtrace                         false
% 0.84/0.99  --dbg_dump_prop_clauses                 false
% 0.84/0.99  --dbg_dump_prop_clauses_file            -
% 0.84/0.99  --dbg_out_stat                          false
% 0.84/0.99  
% 0.84/0.99  
% 0.84/0.99  
% 0.84/0.99  
% 0.84/0.99  ------ Proving...
% 0.84/0.99  
% 0.84/0.99  
% 0.84/0.99  % SZS status Theorem for theBenchmark.p
% 0.84/0.99  
% 0.84/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 0.84/0.99  
% 0.84/0.99  fof(f3,axiom,(
% 0.84/0.99    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.84/0.99  
% 0.84/0.99  fof(f14,plain,(
% 0.84/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.84/0.99    inference(nnf_transformation,[],[f3])).
% 0.84/0.99  
% 0.84/0.99  fof(f15,plain,(
% 0.84/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.84/0.99    inference(flattening,[],[f14])).
% 0.84/0.99  
% 0.84/0.99  fof(f16,plain,(
% 0.84/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.84/0.99    inference(rectify,[],[f15])).
% 0.84/0.99  
% 0.84/0.99  fof(f17,plain,(
% 0.84/0.99    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2))))),
% 0.84/0.99    introduced(choice_axiom,[])).
% 0.84/0.99  
% 0.84/0.99  fof(f18,plain,(
% 0.84/0.99    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK1(X0,X1,X2) != X1 & sK1(X0,X1,X2) != X0) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (sK1(X0,X1,X2) = X1 | sK1(X0,X1,X2) = X0 | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.84/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f16,f17])).
% 0.84/0.99  
% 0.84/0.99  fof(f29,plain,(
% 0.84/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.84/0.99    inference(cnf_transformation,[],[f18])).
% 0.84/0.99  
% 0.84/0.99  fof(f4,axiom,(
% 0.84/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.84/0.99  
% 0.84/0.99  fof(f34,plain,(
% 0.84/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.84/0.99    inference(cnf_transformation,[],[f4])).
% 0.84/0.99  
% 0.84/0.99  fof(f5,axiom,(
% 0.84/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.84/0.99  
% 0.84/0.99  fof(f35,plain,(
% 0.84/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.84/0.99    inference(cnf_transformation,[],[f5])).
% 0.84/0.99  
% 0.84/0.99  fof(f38,plain,(
% 0.84/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.84/0.99    inference(definition_unfolding,[],[f34,f35])).
% 0.84/0.99  
% 0.84/0.99  fof(f49,plain,(
% 0.84/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.84/0.99    inference(definition_unfolding,[],[f29,f38])).
% 0.84/0.99  
% 0.84/0.99  fof(f57,plain,(
% 0.84/0.99    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | k2_enumset1(X4,X4,X4,X1) != X2) )),
% 0.84/0.99    inference(equality_resolution,[],[f49])).
% 0.84/0.99  
% 0.84/0.99  fof(f58,plain,(
% 0.84/0.99    ( ! [X4,X1] : (r2_hidden(X4,k2_enumset1(X4,X4,X4,X1))) )),
% 0.84/0.99    inference(equality_resolution,[],[f57])).
% 0.84/0.99  
% 0.84/0.99  fof(f6,conjecture,(
% 0.84/0.99    ! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) => r2_hidden(X0,X2))),
% 0.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.84/0.99  
% 0.84/0.99  fof(f7,negated_conjecture,(
% 0.84/0.99    ~! [X0,X1,X2] : (k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) => r2_hidden(X0,X2))),
% 0.84/0.99    inference(negated_conjecture,[],[f6])).
% 0.84/0.99  
% 0.84/0.99  fof(f8,plain,(
% 0.84/0.99    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1))),
% 0.84/0.99    inference(ennf_transformation,[],[f7])).
% 0.84/0.99  
% 0.84/0.99  fof(f19,plain,(
% 0.84/0.99    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k3_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)) => (~r2_hidden(sK2,sK4) & k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3))),
% 0.84/0.99    introduced(choice_axiom,[])).
% 0.84/0.99  
% 0.84/0.99  fof(f20,plain,(
% 0.84/0.99    ~r2_hidden(sK2,sK4) & k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3)),
% 0.84/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f8,f19])).
% 0.84/0.99  
% 0.84/0.99  fof(f36,plain,(
% 0.84/0.99    k3_xboole_0(k2_tarski(sK2,sK3),sK4) = k2_tarski(sK2,sK3)),
% 0.84/0.99    inference(cnf_transformation,[],[f20])).
% 0.84/0.99  
% 0.84/0.99  fof(f2,axiom,(
% 0.84/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.84/0.99  
% 0.84/0.99  fof(f27,plain,(
% 0.84/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.84/0.99    inference(cnf_transformation,[],[f2])).
% 0.84/0.99  
% 0.84/0.99  fof(f51,plain,(
% 0.84/0.99    k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4)) = k2_enumset1(sK2,sK2,sK2,sK3)),
% 0.84/0.99    inference(definition_unfolding,[],[f36,f27,f38,f38])).
% 0.84/0.99  
% 0.84/0.99  fof(f1,axiom,(
% 0.84/0.99    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.84/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.84/0.99  
% 0.84/0.99  fof(f9,plain,(
% 0.84/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.84/0.99    inference(nnf_transformation,[],[f1])).
% 0.84/0.99  
% 0.84/0.99  fof(f10,plain,(
% 0.84/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.84/0.99    inference(flattening,[],[f9])).
% 0.84/0.99  
% 0.84/0.99  fof(f11,plain,(
% 0.84/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.84/0.99    inference(rectify,[],[f10])).
% 0.84/0.99  
% 0.84/0.99  fof(f12,plain,(
% 0.84/0.99    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 0.84/0.99    introduced(choice_axiom,[])).
% 0.84/0.99  
% 0.84/0.99  fof(f13,plain,(
% 0.84/0.99    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.84/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).
% 0.84/0.99  
% 0.84/0.99  fof(f22,plain,(
% 0.84/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.84/0.99    inference(cnf_transformation,[],[f13])).
% 0.84/0.99  
% 0.84/0.99  fof(f43,plain,(
% 0.84/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 0.84/0.99    inference(definition_unfolding,[],[f22,f27])).
% 0.84/0.99  
% 0.84/0.99  fof(f53,plain,(
% 0.84/0.99    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.84/0.99    inference(equality_resolution,[],[f43])).
% 0.84/0.99  
% 0.84/0.99  fof(f37,plain,(
% 0.84/0.99    ~r2_hidden(sK2,sK4)),
% 0.84/0.99    inference(cnf_transformation,[],[f20])).
% 0.84/0.99  
% 0.84/0.99  cnf(c_10,plain,
% 0.84/0.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) ),
% 0.84/0.99      inference(cnf_transformation,[],[f58]) ).
% 0.84/0.99  
% 0.84/0.99  cnf(c_354,plain,
% 0.84/0.99      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 0.84/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 0.84/0.99  
% 0.84/0.99  cnf(c_13,negated_conjecture,
% 0.84/0.99      ( k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),k4_xboole_0(k2_enumset1(sK2,sK2,sK2,sK3),sK4)) = k2_enumset1(sK2,sK2,sK2,sK3) ),
% 0.84/0.99      inference(cnf_transformation,[],[f51]) ).
% 0.84/0.99  
% 0.84/0.99  cnf(c_4,plain,
% 0.84/0.99      ( r2_hidden(X0,X1)
% 0.84/0.99      | ~ r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
% 0.84/0.99      inference(cnf_transformation,[],[f53]) ).
% 0.84/0.99  
% 0.84/0.99  cnf(c_360,plain,
% 0.84/0.99      ( r2_hidden(X0,X1) = iProver_top
% 0.84/0.99      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 0.84/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 0.84/0.99  
% 0.84/0.99  cnf(c_706,plain,
% 0.84/0.99      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK3)) != iProver_top
% 0.84/0.99      | r2_hidden(X0,sK4) = iProver_top ),
% 0.84/0.99      inference(superposition,[status(thm)],[c_13,c_360]) ).
% 0.84/0.99  
% 0.84/0.99  cnf(c_726,plain,
% 0.84/0.99      ( r2_hidden(sK2,sK4) = iProver_top ),
% 0.84/0.99      inference(superposition,[status(thm)],[c_354,c_706]) ).
% 0.84/0.99  
% 0.84/0.99  cnf(c_12,negated_conjecture,
% 0.84/0.99      ( ~ r2_hidden(sK2,sK4) ),
% 0.84/0.99      inference(cnf_transformation,[],[f37]) ).
% 0.84/0.99  
% 0.84/0.99  cnf(c_14,plain,
% 0.84/0.99      ( r2_hidden(sK2,sK4) != iProver_top ),
% 0.84/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 0.84/0.99  
% 0.84/0.99  cnf(contradiction,plain,
% 0.84/0.99      ( $false ),
% 0.84/0.99      inference(minisat,[status(thm)],[c_726,c_14]) ).
% 0.84/0.99  
% 0.84/0.99  
% 0.84/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 0.84/0.99  
% 0.84/0.99  ------                               Statistics
% 0.84/0.99  
% 0.84/0.99  ------ General
% 0.84/0.99  
% 0.84/0.99  abstr_ref_over_cycles:                  0
% 0.84/0.99  abstr_ref_under_cycles:                 0
% 0.84/0.99  gc_basic_clause_elim:                   0
% 0.84/0.99  forced_gc_time:                         0
% 0.84/0.99  parsing_time:                           0.009
% 0.84/0.99  unif_index_cands_time:                  0.
% 0.84/0.99  unif_index_add_time:                    0.
% 0.84/0.99  orderings_time:                         0.
% 0.84/0.99  out_proof_time:                         0.008
% 0.84/0.99  total_time:                             0.056
% 0.84/0.99  num_of_symbols:                         39
% 0.84/0.99  num_of_terms:                           839
% 0.84/0.99  
% 0.84/0.99  ------ Preprocessing
% 0.84/0.99  
% 0.84/0.99  num_of_splits:                          0
% 0.84/0.99  num_of_split_atoms:                     0
% 0.84/0.99  num_of_reused_defs:                     0
% 0.84/0.99  num_eq_ax_congr_red:                    12
% 0.84/0.99  num_of_sem_filtered_clauses:            1
% 0.84/0.99  num_of_subtypes:                        0
% 0.84/0.99  monotx_restored_types:                  0
% 0.84/0.99  sat_num_of_epr_types:                   0
% 0.84/0.99  sat_num_of_non_cyclic_types:            0
% 0.84/0.99  sat_guarded_non_collapsed_types:        0
% 0.84/0.99  num_pure_diseq_elim:                    0
% 0.84/0.99  simp_replaced_by:                       0
% 0.84/0.99  res_preprocessed:                       53
% 0.84/0.99  prep_upred:                             0
% 0.84/0.99  prep_unflattend:                        0
% 0.84/0.99  smt_new_axioms:                         0
% 0.84/0.99  pred_elim_cands:                        1
% 0.84/0.99  pred_elim:                              0
% 0.84/0.99  pred_elim_cl:                           0
% 0.84/0.99  pred_elim_cycles:                       1
% 0.84/0.99  merged_defs:                            0
% 0.84/0.99  merged_defs_ncl:                        0
% 0.84/0.99  bin_hyper_res:                          0
% 0.84/0.99  prep_cycles:                            3
% 0.84/0.99  pred_elim_time:                         0.
% 0.84/0.99  splitting_time:                         0.
% 0.84/0.99  sem_filter_time:                        0.
% 0.84/0.99  monotx_time:                            0.
% 0.84/0.99  subtype_inf_time:                       0.
% 0.84/0.99  
% 0.84/0.99  ------ Problem properties
% 0.84/0.99  
% 0.84/0.99  clauses:                                14
% 0.84/0.99  conjectures:                            2
% 0.84/0.99  epr:                                    1
% 0.84/0.99  horn:                                   10
% 0.84/0.99  ground:                                 2
% 0.84/0.99  unary:                                  4
% 0.84/0.99  binary:                                 2
% 0.84/0.99  lits:                                   34
% 0.84/0.99  lits_eq:                                13
% 0.84/0.99  fd_pure:                                0
% 0.84/0.99  fd_pseudo:                              0
% 0.84/0.99  fd_cond:                                0
% 0.84/0.99  fd_pseudo_cond:                         6
% 0.84/0.99  ac_symbols:                             0
% 0.84/0.99  
% 0.84/0.99  ------ Propositional Solver
% 0.84/0.99  
% 0.84/0.99  prop_solver_calls:                      20
% 0.84/0.99  prop_fast_solver_calls:                 282
% 0.84/0.99  smt_solver_calls:                       0
% 0.84/0.99  smt_fast_solver_calls:                  0
% 0.84/0.99  prop_num_of_clauses:                    214
% 0.84/0.99  prop_preprocess_simplified:             1689
% 0.84/0.99  prop_fo_subsumed:                       0
% 0.84/0.99  prop_solver_time:                       0.
% 0.84/0.99  smt_solver_time:                        0.
% 0.84/0.99  smt_fast_solver_time:                   0.
% 0.84/0.99  prop_fast_solver_time:                  0.
% 0.84/0.99  prop_unsat_core_time:                   0.
% 0.84/0.99  
% 0.84/0.99  ------ QBF
% 0.84/0.99  
% 0.84/0.99  qbf_q_res:                              0
% 0.84/0.99  qbf_num_tautologies:                    0
% 0.84/0.99  qbf_prep_cycles:                        0
% 0.84/0.99  
% 0.84/0.99  ------ BMC1
% 0.84/0.99  
% 0.84/0.99  bmc1_current_bound:                     -1
% 0.84/0.99  bmc1_last_solved_bound:                 -1
% 0.84/0.99  bmc1_unsat_core_size:                   -1
% 0.84/0.99  bmc1_unsat_core_parents_size:           -1
% 0.84/0.99  bmc1_merge_next_fun:                    0
% 0.84/0.99  bmc1_unsat_core_clauses_time:           0.
% 0.84/0.99  
% 0.84/0.99  ------ Instantiation
% 0.84/0.99  
% 0.84/0.99  inst_num_of_clauses:                    65
% 0.84/0.99  inst_num_in_passive:                    8
% 0.84/0.99  inst_num_in_active:                     32
% 0.84/0.99  inst_num_in_unprocessed:                25
% 0.84/0.99  inst_num_of_loops:                      40
% 0.84/0.99  inst_num_of_learning_restarts:          0
% 0.84/0.99  inst_num_moves_active_passive:          7
% 0.84/0.99  inst_lit_activity:                      0
% 0.84/0.99  inst_lit_activity_moves:                0
% 0.84/0.99  inst_num_tautologies:                   0
% 0.84/0.99  inst_num_prop_implied:                  0
% 0.84/0.99  inst_num_existing_simplified:           0
% 0.84/0.99  inst_num_eq_res_simplified:             0
% 0.84/0.99  inst_num_child_elim:                    0
% 0.84/0.99  inst_num_of_dismatching_blockings:      2
% 0.84/0.99  inst_num_of_non_proper_insts:           31
% 0.84/0.99  inst_num_of_duplicates:                 0
% 0.84/0.99  inst_inst_num_from_inst_to_res:         0
% 0.84/0.99  inst_dismatching_checking_time:         0.
% 0.84/0.99  
% 0.84/0.99  ------ Resolution
% 0.84/0.99  
% 0.84/0.99  res_num_of_clauses:                     0
% 0.84/0.99  res_num_in_passive:                     0
% 0.84/0.99  res_num_in_active:                      0
% 0.84/0.99  res_num_of_loops:                       56
% 0.84/0.99  res_forward_subset_subsumed:            2
% 0.84/0.99  res_backward_subset_subsumed:           0
% 0.84/0.99  res_forward_subsumed:                   0
% 0.84/0.99  res_backward_subsumed:                  0
% 0.84/0.99  res_forward_subsumption_resolution:     0
% 0.84/0.99  res_backward_subsumption_resolution:    0
% 0.84/0.99  res_clause_to_clause_subsumption:       39
% 0.84/0.99  res_orphan_elimination:                 0
% 0.84/0.99  res_tautology_del:                      1
% 0.84/0.99  res_num_eq_res_simplified:              0
% 0.84/0.99  res_num_sel_changes:                    0
% 0.84/0.99  res_moves_from_active_to_pass:          0
% 0.84/0.99  
% 0.84/0.99  ------ Superposition
% 0.84/0.99  
% 0.84/0.99  sup_time_total:                         0.
% 0.84/0.99  sup_time_generating:                    0.
% 0.84/0.99  sup_time_sim_full:                      0.
% 0.84/0.99  sup_time_sim_immed:                     0.
% 0.84/0.99  
% 0.84/0.99  sup_num_of_clauses:                     19
% 0.84/0.99  sup_num_in_active:                      8
% 0.84/0.99  sup_num_in_passive:                     11
% 0.84/0.99  sup_num_of_loops:                       7
% 0.84/0.99  sup_fw_superposition:                   6
% 0.84/0.99  sup_bw_superposition:                   0
% 0.84/0.99  sup_immediate_simplified:               0
% 0.84/0.99  sup_given_eliminated:                   0
% 0.84/0.99  comparisons_done:                       0
% 0.84/0.99  comparisons_avoided:                    0
% 0.84/0.99  
% 0.84/0.99  ------ Simplifications
% 0.84/0.99  
% 0.84/0.99  
% 0.84/0.99  sim_fw_subset_subsumed:                 0
% 0.84/0.99  sim_bw_subset_subsumed:                 0
% 0.84/0.99  sim_fw_subsumed:                        0
% 0.84/0.99  sim_bw_subsumed:                        0
% 0.84/0.99  sim_fw_subsumption_res:                 0
% 0.84/0.99  sim_bw_subsumption_res:                 0
% 0.84/0.99  sim_tautology_del:                      1
% 0.84/0.99  sim_eq_tautology_del:                   0
% 0.84/0.99  sim_eq_res_simp:                        0
% 0.84/0.99  sim_fw_demodulated:                     0
% 0.84/0.99  sim_bw_demodulated:                     0
% 0.84/0.99  sim_light_normalised:                   0
% 0.84/0.99  sim_joinable_taut:                      0
% 0.84/0.99  sim_joinable_simp:                      0
% 0.84/0.99  sim_ac_normalised:                      0
% 0.84/0.99  sim_smt_subsumption:                    0
% 0.84/0.99  
%------------------------------------------------------------------------------
