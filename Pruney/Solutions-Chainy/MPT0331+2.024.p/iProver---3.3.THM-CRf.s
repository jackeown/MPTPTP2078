%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:38:17 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   46 (  68 expanded)
%              Number of clauses        :   24 (  24 expanded)
%              Number of leaves         :    7 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :  178 ( 358 expanded)
%              Number of equality atoms :   51 (  81 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f8,plain,(
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
    inference(rectify,[],[f7])).

fof(f9,plain,(
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

fof(f10,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).

fof(f16,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1) ) ) ),
    inference(flattening,[],[f11])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( k4_xboole_0(sK3,k2_tarski(sK1,sK2)) != sK3
      & ~ r2_hidden(sK2,sK3)
      & ~ r2_hidden(sK1,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( k4_xboole_0(sK3,k2_tarski(sK1,sK2)) != sK3
    & ~ r2_hidden(sK2,sK3)
    & ~ r2_hidden(sK1,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f5,f13])).

fof(f25,plain,(
    ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f24,plain,(
    ~ r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ r2_hidden(sK0(X0,X1,X2),X0)
      | ~ r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK0(X0,X1,X2),X0)
      | r2_hidden(sK0(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    k4_xboole_0(sK3,k2_tarski(sK1,sK2)) != sK3 ),
    inference(cnf_transformation,[],[f14])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_411,plain,
    ( ~ r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),k4_xboole_0(X0,sK3))
    | ~ r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_8905,plain,
    ( ~ r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),k4_xboole_0(k2_tarski(sK1,sK2),sK3))
    | ~ r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),sK3) ),
    inference(instantiation,[status(thm)],[c_411])).

cnf(c_124,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_440,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),k2_tarski(sK1,sK2))
    | X0 != sK0(sK3,k2_tarski(sK1,sK2),sK3)
    | X1 != k2_tarski(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_124])).

cnf(c_704,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X2))
    | ~ r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),k2_tarski(sK1,sK2))
    | X0 != sK0(sK3,k2_tarski(sK1,sK2),sK3)
    | k4_xboole_0(X1,X2) != k2_tarski(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_1695,plain,
    ( ~ r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),k2_tarski(sK1,sK2))
    | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),k4_xboole_0(X0,X1))
    | sK0(sK3,k2_tarski(sK1,sK2),sK3) != sK0(sK3,k2_tarski(sK1,sK2),sK3)
    | k4_xboole_0(X0,X1) != k2_tarski(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_704])).

cnf(c_6164,plain,
    ( ~ r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),k2_tarski(sK1,sK2))
    | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),k4_xboole_0(k2_tarski(sK1,sK2),sK3))
    | sK0(sK3,k2_tarski(sK1,sK2),sK3) != sK0(sK3,k2_tarski(sK1,sK2),sK3)
    | k4_xboole_0(k2_tarski(sK1,sK2),sK3) != k2_tarski(sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_1695])).

cnf(c_6,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X2,X1)
    | k4_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_310,plain,
    ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_10,negated_conjecture,
    ( ~ r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_307,plain,
    ( r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_877,plain,
    ( k4_xboole_0(k2_tarski(X0,sK2),sK3) = k2_tarski(X0,sK2)
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_310,c_307])).

cnf(c_11,negated_conjecture,
    ( ~ r2_hidden(sK1,sK3) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_306,plain,
    ( r2_hidden(sK1,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1411,plain,
    ( k4_xboole_0(k2_tarski(sK1,sK2),sK3) = k2_tarski(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_877,c_306])).

cnf(c_121,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_669,plain,
    ( sK0(sK3,k2_tarski(sK1,sK2),sK3) = sK0(sK3,k2_tarski(sK1,sK2),sK3) ),
    inference(instantiation,[status(thm)],[c_121])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1,X2),X0)
    | ~ r2_hidden(sK0(X0,X1,X2),X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f20])).

cnf(c_404,plain,
    ( r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),k2_tarski(sK1,sK2))
    | ~ r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),sK3)
    | k4_xboole_0(sK3,k2_tarski(sK1,sK2)) = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1,X2),X0)
    | r2_hidden(sK0(X0,X1,X2),X2)
    | k4_xboole_0(X0,X1) = X2 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_401,plain,
    ( r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),sK3)
    | k4_xboole_0(sK3,k2_tarski(sK1,sK2)) = sK3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_9,negated_conjecture,
    ( k4_xboole_0(sK3,k2_tarski(sK1,sK2)) != sK3 ),
    inference(cnf_transformation,[],[f26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8905,c_6164,c_1411,c_669,c_404,c_401,c_9])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:15:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.89/1.07  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.07  
% 2.89/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.89/1.07  
% 2.89/1.07  ------  iProver source info
% 2.89/1.07  
% 2.89/1.07  git: date: 2020-06-30 10:37:57 +0100
% 2.89/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.89/1.07  git: non_committed_changes: false
% 2.89/1.07  git: last_make_outside_of_git: false
% 2.89/1.07  
% 2.89/1.07  ------ 
% 2.89/1.07  
% 2.89/1.07  ------ Input Options
% 2.89/1.07  
% 2.89/1.07  --out_options                           all
% 2.89/1.07  --tptp_safe_out                         true
% 2.89/1.07  --problem_path                          ""
% 2.89/1.07  --include_path                          ""
% 2.89/1.07  --clausifier                            res/vclausify_rel
% 2.89/1.07  --clausifier_options                    --mode clausify
% 2.89/1.07  --stdin                                 false
% 2.89/1.07  --stats_out                             all
% 2.89/1.07  
% 2.89/1.07  ------ General Options
% 2.89/1.07  
% 2.89/1.07  --fof                                   false
% 2.89/1.07  --time_out_real                         305.
% 2.89/1.07  --time_out_virtual                      -1.
% 2.89/1.07  --symbol_type_check                     false
% 2.89/1.07  --clausify_out                          false
% 2.89/1.07  --sig_cnt_out                           false
% 2.89/1.07  --trig_cnt_out                          false
% 2.89/1.07  --trig_cnt_out_tolerance                1.
% 2.89/1.07  --trig_cnt_out_sk_spl                   false
% 2.89/1.07  --abstr_cl_out                          false
% 2.89/1.07  
% 2.89/1.07  ------ Global Options
% 2.89/1.07  
% 2.89/1.07  --schedule                              default
% 2.89/1.07  --add_important_lit                     false
% 2.89/1.07  --prop_solver_per_cl                    1000
% 2.89/1.07  --min_unsat_core                        false
% 2.89/1.07  --soft_assumptions                      false
% 2.89/1.07  --soft_lemma_size                       3
% 2.89/1.07  --prop_impl_unit_size                   0
% 2.89/1.07  --prop_impl_unit                        []
% 2.89/1.07  --share_sel_clauses                     true
% 2.89/1.07  --reset_solvers                         false
% 2.89/1.07  --bc_imp_inh                            [conj_cone]
% 2.89/1.07  --conj_cone_tolerance                   3.
% 2.89/1.07  --extra_neg_conj                        none
% 2.89/1.07  --large_theory_mode                     true
% 2.89/1.07  --prolific_symb_bound                   200
% 2.89/1.07  --lt_threshold                          2000
% 2.89/1.07  --clause_weak_htbl                      true
% 2.89/1.07  --gc_record_bc_elim                     false
% 2.89/1.07  
% 2.89/1.07  ------ Preprocessing Options
% 2.89/1.07  
% 2.89/1.07  --preprocessing_flag                    true
% 2.89/1.07  --time_out_prep_mult                    0.1
% 2.89/1.07  --splitting_mode                        input
% 2.89/1.07  --splitting_grd                         true
% 2.89/1.07  --splitting_cvd                         false
% 2.89/1.07  --splitting_cvd_svl                     false
% 2.89/1.07  --splitting_nvd                         32
% 2.89/1.07  --sub_typing                            true
% 2.89/1.07  --prep_gs_sim                           true
% 2.89/1.07  --prep_unflatten                        true
% 2.89/1.07  --prep_res_sim                          true
% 2.89/1.07  --prep_upred                            true
% 2.89/1.07  --prep_sem_filter                       exhaustive
% 2.89/1.07  --prep_sem_filter_out                   false
% 2.89/1.07  --pred_elim                             true
% 2.89/1.07  --res_sim_input                         true
% 2.89/1.07  --eq_ax_congr_red                       true
% 2.89/1.07  --pure_diseq_elim                       true
% 2.89/1.07  --brand_transform                       false
% 2.89/1.07  --non_eq_to_eq                          false
% 2.89/1.07  --prep_def_merge                        true
% 2.89/1.07  --prep_def_merge_prop_impl              false
% 2.89/1.07  --prep_def_merge_mbd                    true
% 2.89/1.07  --prep_def_merge_tr_red                 false
% 2.89/1.07  --prep_def_merge_tr_cl                  false
% 2.89/1.07  --smt_preprocessing                     true
% 2.89/1.07  --smt_ac_axioms                         fast
% 2.89/1.07  --preprocessed_out                      false
% 2.89/1.07  --preprocessed_stats                    false
% 2.89/1.07  
% 2.89/1.07  ------ Abstraction refinement Options
% 2.89/1.07  
% 2.89/1.07  --abstr_ref                             []
% 2.89/1.07  --abstr_ref_prep                        false
% 2.89/1.07  --abstr_ref_until_sat                   false
% 2.89/1.07  --abstr_ref_sig_restrict                funpre
% 2.89/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/1.07  --abstr_ref_under                       []
% 2.89/1.07  
% 2.89/1.07  ------ SAT Options
% 2.89/1.07  
% 2.89/1.07  --sat_mode                              false
% 2.89/1.07  --sat_fm_restart_options                ""
% 2.89/1.07  --sat_gr_def                            false
% 2.89/1.07  --sat_epr_types                         true
% 2.89/1.07  --sat_non_cyclic_types                  false
% 2.89/1.07  --sat_finite_models                     false
% 2.89/1.07  --sat_fm_lemmas                         false
% 2.89/1.07  --sat_fm_prep                           false
% 2.89/1.07  --sat_fm_uc_incr                        true
% 2.89/1.07  --sat_out_model                         small
% 2.89/1.07  --sat_out_clauses                       false
% 2.89/1.07  
% 2.89/1.07  ------ QBF Options
% 2.89/1.07  
% 2.89/1.07  --qbf_mode                              false
% 2.89/1.07  --qbf_elim_univ                         false
% 2.89/1.07  --qbf_dom_inst                          none
% 2.89/1.07  --qbf_dom_pre_inst                      false
% 2.89/1.07  --qbf_sk_in                             false
% 2.89/1.07  --qbf_pred_elim                         true
% 2.89/1.07  --qbf_split                             512
% 2.89/1.07  
% 2.89/1.07  ------ BMC1 Options
% 2.89/1.07  
% 2.89/1.07  --bmc1_incremental                      false
% 2.89/1.07  --bmc1_axioms                           reachable_all
% 2.89/1.07  --bmc1_min_bound                        0
% 2.89/1.07  --bmc1_max_bound                        -1
% 2.89/1.07  --bmc1_max_bound_default                -1
% 2.89/1.07  --bmc1_symbol_reachability              true
% 2.89/1.07  --bmc1_property_lemmas                  false
% 2.89/1.07  --bmc1_k_induction                      false
% 2.89/1.07  --bmc1_non_equiv_states                 false
% 2.89/1.07  --bmc1_deadlock                         false
% 2.89/1.07  --bmc1_ucm                              false
% 2.89/1.07  --bmc1_add_unsat_core                   none
% 2.89/1.07  --bmc1_unsat_core_children              false
% 2.89/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/1.07  --bmc1_out_stat                         full
% 2.89/1.07  --bmc1_ground_init                      false
% 2.89/1.07  --bmc1_pre_inst_next_state              false
% 2.89/1.07  --bmc1_pre_inst_state                   false
% 2.89/1.07  --bmc1_pre_inst_reach_state             false
% 2.89/1.07  --bmc1_out_unsat_core                   false
% 2.89/1.07  --bmc1_aig_witness_out                  false
% 2.89/1.07  --bmc1_verbose                          false
% 2.89/1.07  --bmc1_dump_clauses_tptp                false
% 2.89/1.07  --bmc1_dump_unsat_core_tptp             false
% 2.89/1.07  --bmc1_dump_file                        -
% 2.89/1.07  --bmc1_ucm_expand_uc_limit              128
% 2.89/1.07  --bmc1_ucm_n_expand_iterations          6
% 2.89/1.07  --bmc1_ucm_extend_mode                  1
% 2.89/1.07  --bmc1_ucm_init_mode                    2
% 2.89/1.07  --bmc1_ucm_cone_mode                    none
% 2.89/1.07  --bmc1_ucm_reduced_relation_type        0
% 2.89/1.07  --bmc1_ucm_relax_model                  4
% 2.89/1.07  --bmc1_ucm_full_tr_after_sat            true
% 2.89/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/1.07  --bmc1_ucm_layered_model                none
% 2.89/1.07  --bmc1_ucm_max_lemma_size               10
% 2.89/1.07  
% 2.89/1.07  ------ AIG Options
% 2.89/1.07  
% 2.89/1.07  --aig_mode                              false
% 2.89/1.07  
% 2.89/1.07  ------ Instantiation Options
% 2.89/1.07  
% 2.89/1.07  --instantiation_flag                    true
% 2.89/1.07  --inst_sos_flag                         false
% 2.89/1.07  --inst_sos_phase                        true
% 2.89/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/1.07  --inst_lit_sel_side                     num_symb
% 2.89/1.07  --inst_solver_per_active                1400
% 2.89/1.07  --inst_solver_calls_frac                1.
% 2.89/1.07  --inst_passive_queue_type               priority_queues
% 2.89/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/1.07  --inst_passive_queues_freq              [25;2]
% 2.89/1.07  --inst_dismatching                      true
% 2.89/1.07  --inst_eager_unprocessed_to_passive     true
% 2.89/1.07  --inst_prop_sim_given                   true
% 2.89/1.07  --inst_prop_sim_new                     false
% 2.89/1.07  --inst_subs_new                         false
% 2.89/1.07  --inst_eq_res_simp                      false
% 2.89/1.07  --inst_subs_given                       false
% 2.89/1.07  --inst_orphan_elimination               true
% 2.89/1.07  --inst_learning_loop_flag               true
% 2.89/1.07  --inst_learning_start                   3000
% 2.89/1.07  --inst_learning_factor                  2
% 2.89/1.07  --inst_start_prop_sim_after_learn       3
% 2.89/1.07  --inst_sel_renew                        solver
% 2.89/1.07  --inst_lit_activity_flag                true
% 2.89/1.07  --inst_restr_to_given                   false
% 2.89/1.07  --inst_activity_threshold               500
% 2.89/1.07  --inst_out_proof                        true
% 2.89/1.07  
% 2.89/1.07  ------ Resolution Options
% 2.89/1.07  
% 2.89/1.07  --resolution_flag                       true
% 2.89/1.07  --res_lit_sel                           adaptive
% 2.89/1.07  --res_lit_sel_side                      none
% 2.89/1.07  --res_ordering                          kbo
% 2.89/1.07  --res_to_prop_solver                    active
% 2.89/1.07  --res_prop_simpl_new                    false
% 2.89/1.07  --res_prop_simpl_given                  true
% 2.89/1.07  --res_passive_queue_type                priority_queues
% 2.89/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/1.07  --res_passive_queues_freq               [15;5]
% 2.89/1.07  --res_forward_subs                      full
% 2.89/1.07  --res_backward_subs                     full
% 2.89/1.07  --res_forward_subs_resolution           true
% 2.89/1.07  --res_backward_subs_resolution          true
% 2.89/1.07  --res_orphan_elimination                true
% 2.89/1.07  --res_time_limit                        2.
% 2.89/1.07  --res_out_proof                         true
% 2.89/1.07  
% 2.89/1.07  ------ Superposition Options
% 2.89/1.07  
% 2.89/1.07  --superposition_flag                    true
% 2.89/1.07  --sup_passive_queue_type                priority_queues
% 2.89/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/1.07  --sup_passive_queues_freq               [8;1;4]
% 2.89/1.07  --demod_completeness_check              fast
% 2.89/1.07  --demod_use_ground                      true
% 2.89/1.07  --sup_to_prop_solver                    passive
% 2.89/1.07  --sup_prop_simpl_new                    true
% 2.89/1.07  --sup_prop_simpl_given                  true
% 2.89/1.07  --sup_fun_splitting                     false
% 2.89/1.07  --sup_smt_interval                      50000
% 2.89/1.07  
% 2.89/1.07  ------ Superposition Simplification Setup
% 2.89/1.07  
% 2.89/1.07  --sup_indices_passive                   []
% 2.89/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.07  --sup_full_bw                           [BwDemod]
% 2.89/1.07  --sup_immed_triv                        [TrivRules]
% 2.89/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.07  --sup_immed_bw_main                     []
% 2.89/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/1.07  
% 2.89/1.07  ------ Combination Options
% 2.89/1.07  
% 2.89/1.07  --comb_res_mult                         3
% 2.89/1.07  --comb_sup_mult                         2
% 2.89/1.07  --comb_inst_mult                        10
% 2.89/1.07  
% 2.89/1.07  ------ Debug Options
% 2.89/1.07  
% 2.89/1.07  --dbg_backtrace                         false
% 2.89/1.07  --dbg_dump_prop_clauses                 false
% 2.89/1.07  --dbg_dump_prop_clauses_file            -
% 2.89/1.07  --dbg_out_stat                          false
% 2.89/1.07  ------ Parsing...
% 2.89/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.89/1.07  
% 2.89/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.89/1.07  
% 2.89/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.89/1.07  
% 2.89/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.89/1.07  ------ Proving...
% 2.89/1.07  ------ Problem Properties 
% 2.89/1.07  
% 2.89/1.07  
% 2.89/1.07  clauses                                 12
% 2.89/1.07  conjectures                             3
% 2.89/1.07  EPR                                     2
% 2.89/1.07  Horn                                    7
% 2.89/1.07  unary                                   3
% 2.89/1.07  binary                                  4
% 2.89/1.07  lits                                    27
% 2.89/1.07  lits eq                                 7
% 2.89/1.07  fd_pure                                 0
% 2.89/1.07  fd_pseudo                               0
% 2.89/1.07  fd_cond                                 0
% 2.89/1.07  fd_pseudo_cond                          3
% 2.89/1.07  AC symbols                              0
% 2.89/1.07  
% 2.89/1.07  ------ Schedule dynamic 5 is on 
% 2.89/1.07  
% 2.89/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.89/1.07  
% 2.89/1.07  
% 2.89/1.07  ------ 
% 2.89/1.07  Current options:
% 2.89/1.07  ------ 
% 2.89/1.07  
% 2.89/1.07  ------ Input Options
% 2.89/1.07  
% 2.89/1.07  --out_options                           all
% 2.89/1.07  --tptp_safe_out                         true
% 2.89/1.07  --problem_path                          ""
% 2.89/1.07  --include_path                          ""
% 2.89/1.07  --clausifier                            res/vclausify_rel
% 2.89/1.07  --clausifier_options                    --mode clausify
% 2.89/1.07  --stdin                                 false
% 2.89/1.07  --stats_out                             all
% 2.89/1.07  
% 2.89/1.07  ------ General Options
% 2.89/1.07  
% 2.89/1.07  --fof                                   false
% 2.89/1.07  --time_out_real                         305.
% 2.89/1.07  --time_out_virtual                      -1.
% 2.89/1.07  --symbol_type_check                     false
% 2.89/1.07  --clausify_out                          false
% 2.89/1.07  --sig_cnt_out                           false
% 2.89/1.07  --trig_cnt_out                          false
% 2.89/1.07  --trig_cnt_out_tolerance                1.
% 2.89/1.07  --trig_cnt_out_sk_spl                   false
% 2.89/1.07  --abstr_cl_out                          false
% 2.89/1.07  
% 2.89/1.07  ------ Global Options
% 2.89/1.07  
% 2.89/1.07  --schedule                              default
% 2.89/1.07  --add_important_lit                     false
% 2.89/1.07  --prop_solver_per_cl                    1000
% 2.89/1.07  --min_unsat_core                        false
% 2.89/1.07  --soft_assumptions                      false
% 2.89/1.07  --soft_lemma_size                       3
% 2.89/1.07  --prop_impl_unit_size                   0
% 2.89/1.07  --prop_impl_unit                        []
% 2.89/1.07  --share_sel_clauses                     true
% 2.89/1.07  --reset_solvers                         false
% 2.89/1.07  --bc_imp_inh                            [conj_cone]
% 2.89/1.07  --conj_cone_tolerance                   3.
% 2.89/1.07  --extra_neg_conj                        none
% 2.89/1.08  --large_theory_mode                     true
% 2.89/1.08  --prolific_symb_bound                   200
% 2.89/1.08  --lt_threshold                          2000
% 2.89/1.08  --clause_weak_htbl                      true
% 2.89/1.08  --gc_record_bc_elim                     false
% 2.89/1.08  
% 2.89/1.08  ------ Preprocessing Options
% 2.89/1.08  
% 2.89/1.08  --preprocessing_flag                    true
% 2.89/1.08  --time_out_prep_mult                    0.1
% 2.89/1.08  --splitting_mode                        input
% 2.89/1.08  --splitting_grd                         true
% 2.89/1.08  --splitting_cvd                         false
% 2.89/1.08  --splitting_cvd_svl                     false
% 2.89/1.08  --splitting_nvd                         32
% 2.89/1.08  --sub_typing                            true
% 2.89/1.08  --prep_gs_sim                           true
% 2.89/1.08  --prep_unflatten                        true
% 2.89/1.08  --prep_res_sim                          true
% 2.89/1.08  --prep_upred                            true
% 2.89/1.08  --prep_sem_filter                       exhaustive
% 2.89/1.08  --prep_sem_filter_out                   false
% 2.89/1.08  --pred_elim                             true
% 2.89/1.08  --res_sim_input                         true
% 2.89/1.08  --eq_ax_congr_red                       true
% 2.89/1.08  --pure_diseq_elim                       true
% 2.89/1.08  --brand_transform                       false
% 2.89/1.08  --non_eq_to_eq                          false
% 2.89/1.08  --prep_def_merge                        true
% 2.89/1.08  --prep_def_merge_prop_impl              false
% 2.89/1.08  --prep_def_merge_mbd                    true
% 2.89/1.08  --prep_def_merge_tr_red                 false
% 2.89/1.08  --prep_def_merge_tr_cl                  false
% 2.89/1.08  --smt_preprocessing                     true
% 2.89/1.08  --smt_ac_axioms                         fast
% 2.89/1.08  --preprocessed_out                      false
% 2.89/1.08  --preprocessed_stats                    false
% 2.89/1.08  
% 2.89/1.08  ------ Abstraction refinement Options
% 2.89/1.08  
% 2.89/1.08  --abstr_ref                             []
% 2.89/1.08  --abstr_ref_prep                        false
% 2.89/1.08  --abstr_ref_until_sat                   false
% 2.89/1.08  --abstr_ref_sig_restrict                funpre
% 2.89/1.08  --abstr_ref_af_restrict_to_split_sk     false
% 2.89/1.08  --abstr_ref_under                       []
% 2.89/1.08  
% 2.89/1.08  ------ SAT Options
% 2.89/1.08  
% 2.89/1.08  --sat_mode                              false
% 2.89/1.08  --sat_fm_restart_options                ""
% 2.89/1.08  --sat_gr_def                            false
% 2.89/1.08  --sat_epr_types                         true
% 2.89/1.08  --sat_non_cyclic_types                  false
% 2.89/1.08  --sat_finite_models                     false
% 2.89/1.08  --sat_fm_lemmas                         false
% 2.89/1.08  --sat_fm_prep                           false
% 2.89/1.08  --sat_fm_uc_incr                        true
% 2.89/1.08  --sat_out_model                         small
% 2.89/1.08  --sat_out_clauses                       false
% 2.89/1.08  
% 2.89/1.08  ------ QBF Options
% 2.89/1.08  
% 2.89/1.08  --qbf_mode                              false
% 2.89/1.08  --qbf_elim_univ                         false
% 2.89/1.08  --qbf_dom_inst                          none
% 2.89/1.08  --qbf_dom_pre_inst                      false
% 2.89/1.08  --qbf_sk_in                             false
% 2.89/1.08  --qbf_pred_elim                         true
% 2.89/1.08  --qbf_split                             512
% 2.89/1.08  
% 2.89/1.08  ------ BMC1 Options
% 2.89/1.08  
% 2.89/1.08  --bmc1_incremental                      false
% 2.89/1.08  --bmc1_axioms                           reachable_all
% 2.89/1.08  --bmc1_min_bound                        0
% 2.89/1.08  --bmc1_max_bound                        -1
% 2.89/1.08  --bmc1_max_bound_default                -1
% 2.89/1.08  --bmc1_symbol_reachability              true
% 2.89/1.08  --bmc1_property_lemmas                  false
% 2.89/1.08  --bmc1_k_induction                      false
% 2.89/1.08  --bmc1_non_equiv_states                 false
% 2.89/1.08  --bmc1_deadlock                         false
% 2.89/1.08  --bmc1_ucm                              false
% 2.89/1.08  --bmc1_add_unsat_core                   none
% 2.89/1.08  --bmc1_unsat_core_children              false
% 2.89/1.08  --bmc1_unsat_core_extrapolate_axioms    false
% 2.89/1.08  --bmc1_out_stat                         full
% 2.89/1.08  --bmc1_ground_init                      false
% 2.89/1.08  --bmc1_pre_inst_next_state              false
% 2.89/1.08  --bmc1_pre_inst_state                   false
% 2.89/1.08  --bmc1_pre_inst_reach_state             false
% 2.89/1.08  --bmc1_out_unsat_core                   false
% 2.89/1.08  --bmc1_aig_witness_out                  false
% 2.89/1.08  --bmc1_verbose                          false
% 2.89/1.08  --bmc1_dump_clauses_tptp                false
% 2.89/1.08  --bmc1_dump_unsat_core_tptp             false
% 2.89/1.08  --bmc1_dump_file                        -
% 2.89/1.08  --bmc1_ucm_expand_uc_limit              128
% 2.89/1.08  --bmc1_ucm_n_expand_iterations          6
% 2.89/1.08  --bmc1_ucm_extend_mode                  1
% 2.89/1.08  --bmc1_ucm_init_mode                    2
% 2.89/1.08  --bmc1_ucm_cone_mode                    none
% 2.89/1.08  --bmc1_ucm_reduced_relation_type        0
% 2.89/1.08  --bmc1_ucm_relax_model                  4
% 2.89/1.08  --bmc1_ucm_full_tr_after_sat            true
% 2.89/1.08  --bmc1_ucm_expand_neg_assumptions       false
% 2.89/1.08  --bmc1_ucm_layered_model                none
% 2.89/1.08  --bmc1_ucm_max_lemma_size               10
% 2.89/1.08  
% 2.89/1.08  ------ AIG Options
% 2.89/1.08  
% 2.89/1.08  --aig_mode                              false
% 2.89/1.08  
% 2.89/1.08  ------ Instantiation Options
% 2.89/1.08  
% 2.89/1.08  --instantiation_flag                    true
% 2.89/1.08  --inst_sos_flag                         false
% 2.89/1.08  --inst_sos_phase                        true
% 2.89/1.08  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.89/1.08  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.89/1.08  --inst_lit_sel_side                     none
% 2.89/1.08  --inst_solver_per_active                1400
% 2.89/1.08  --inst_solver_calls_frac                1.
% 2.89/1.08  --inst_passive_queue_type               priority_queues
% 2.89/1.08  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.89/1.08  --inst_passive_queues_freq              [25;2]
% 2.89/1.08  --inst_dismatching                      true
% 2.89/1.08  --inst_eager_unprocessed_to_passive     true
% 2.89/1.08  --inst_prop_sim_given                   true
% 2.89/1.08  --inst_prop_sim_new                     false
% 2.89/1.08  --inst_subs_new                         false
% 2.89/1.08  --inst_eq_res_simp                      false
% 2.89/1.08  --inst_subs_given                       false
% 2.89/1.08  --inst_orphan_elimination               true
% 2.89/1.08  --inst_learning_loop_flag               true
% 2.89/1.08  --inst_learning_start                   3000
% 2.89/1.08  --inst_learning_factor                  2
% 2.89/1.08  --inst_start_prop_sim_after_learn       3
% 2.89/1.08  --inst_sel_renew                        solver
% 2.89/1.08  --inst_lit_activity_flag                true
% 2.89/1.08  --inst_restr_to_given                   false
% 2.89/1.08  --inst_activity_threshold               500
% 2.89/1.08  --inst_out_proof                        true
% 2.89/1.08  
% 2.89/1.08  ------ Resolution Options
% 2.89/1.08  
% 2.89/1.08  --resolution_flag                       false
% 2.89/1.08  --res_lit_sel                           adaptive
% 2.89/1.08  --res_lit_sel_side                      none
% 2.89/1.08  --res_ordering                          kbo
% 2.89/1.08  --res_to_prop_solver                    active
% 2.89/1.08  --res_prop_simpl_new                    false
% 2.89/1.08  --res_prop_simpl_given                  true
% 2.89/1.08  --res_passive_queue_type                priority_queues
% 2.89/1.08  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.89/1.08  --res_passive_queues_freq               [15;5]
% 2.89/1.08  --res_forward_subs                      full
% 2.89/1.08  --res_backward_subs                     full
% 2.89/1.08  --res_forward_subs_resolution           true
% 2.89/1.08  --res_backward_subs_resolution          true
% 2.89/1.08  --res_orphan_elimination                true
% 2.89/1.08  --res_time_limit                        2.
% 2.89/1.08  --res_out_proof                         true
% 2.89/1.08  
% 2.89/1.08  ------ Superposition Options
% 2.89/1.08  
% 2.89/1.08  --superposition_flag                    true
% 2.89/1.08  --sup_passive_queue_type                priority_queues
% 2.89/1.08  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.89/1.08  --sup_passive_queues_freq               [8;1;4]
% 2.89/1.08  --demod_completeness_check              fast
% 2.89/1.08  --demod_use_ground                      true
% 2.89/1.08  --sup_to_prop_solver                    passive
% 2.89/1.08  --sup_prop_simpl_new                    true
% 2.89/1.08  --sup_prop_simpl_given                  true
% 2.89/1.08  --sup_fun_splitting                     false
% 2.89/1.08  --sup_smt_interval                      50000
% 2.89/1.08  
% 2.89/1.08  ------ Superposition Simplification Setup
% 2.89/1.08  
% 2.89/1.08  --sup_indices_passive                   []
% 2.89/1.08  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.08  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.08  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.89/1.08  --sup_full_triv                         [TrivRules;PropSubs]
% 2.89/1.08  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.08  --sup_full_bw                           [BwDemod]
% 2.89/1.08  --sup_immed_triv                        [TrivRules]
% 2.89/1.08  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.89/1.08  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.08  --sup_immed_bw_main                     []
% 2.89/1.08  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/1.08  --sup_input_triv                        [Unflattening;TrivRules]
% 2.89/1.08  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.89/1.08  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.89/1.08  
% 2.89/1.08  ------ Combination Options
% 2.89/1.08  
% 2.89/1.08  --comb_res_mult                         3
% 2.89/1.08  --comb_sup_mult                         2
% 2.89/1.08  --comb_inst_mult                        10
% 2.89/1.08  
% 2.89/1.08  ------ Debug Options
% 2.89/1.08  
% 2.89/1.08  --dbg_backtrace                         false
% 2.89/1.08  --dbg_dump_prop_clauses                 false
% 2.89/1.08  --dbg_dump_prop_clauses_file            -
% 2.89/1.08  --dbg_out_stat                          false
% 2.89/1.08  
% 2.89/1.08  
% 2.89/1.08  
% 2.89/1.08  
% 2.89/1.08  ------ Proving...
% 2.89/1.08  
% 2.89/1.08  
% 2.89/1.08  % SZS status Theorem for theBenchmark.p
% 2.89/1.08  
% 2.89/1.08  % SZS output start CNFRefutation for theBenchmark.p
% 2.89/1.08  
% 2.89/1.08  fof(f1,axiom,(
% 2.89/1.08    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.89/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.08  
% 2.89/1.08  fof(f6,plain,(
% 2.89/1.08    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.89/1.08    inference(nnf_transformation,[],[f1])).
% 2.89/1.08  
% 2.89/1.08  fof(f7,plain,(
% 2.89/1.08    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.89/1.08    inference(flattening,[],[f6])).
% 2.89/1.08  
% 2.89/1.08  fof(f8,plain,(
% 2.89/1.08    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.89/1.08    inference(rectify,[],[f7])).
% 2.89/1.08  
% 2.89/1.08  fof(f9,plain,(
% 2.89/1.08    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.89/1.08    introduced(choice_axiom,[])).
% 2.89/1.08  
% 2.89/1.08  fof(f10,plain,(
% 2.89/1.08    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((~r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(sK0(X0,X1,X2),X0)) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.89/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f9])).
% 2.89/1.08  
% 2.89/1.08  fof(f16,plain,(
% 2.89/1.08    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.89/1.08    inference(cnf_transformation,[],[f10])).
% 2.89/1.08  
% 2.89/1.08  fof(f28,plain,(
% 2.89/1.08    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 2.89/1.08    inference(equality_resolution,[],[f16])).
% 2.89/1.08  
% 2.89/1.08  fof(f2,axiom,(
% 2.89/1.08    ! [X0,X1,X2] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.89/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.08  
% 2.89/1.08  fof(f11,plain,(
% 2.89/1.08    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 2.89/1.08    inference(nnf_transformation,[],[f2])).
% 2.89/1.08  
% 2.89/1.08  fof(f12,plain,(
% 2.89/1.08    ! [X0,X1,X2] : ((k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k4_xboole_0(k2_tarski(X0,X1),X2) != k2_tarski(X0,X1)))),
% 2.89/1.08    inference(flattening,[],[f11])).
% 2.89/1.08  
% 2.89/1.08  fof(f23,plain,(
% 2.89/1.08    ( ! [X2,X0,X1] : (k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 2.89/1.08    inference(cnf_transformation,[],[f12])).
% 2.89/1.08  
% 2.89/1.08  fof(f3,conjecture,(
% 2.89/1.08    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.89/1.08    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.89/1.08  
% 2.89/1.08  fof(f4,negated_conjecture,(
% 2.89/1.08    ~! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.89/1.08    inference(negated_conjecture,[],[f3])).
% 2.89/1.08  
% 2.89/1.08  fof(f5,plain,(
% 2.89/1.08    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.89/1.08    inference(ennf_transformation,[],[f4])).
% 2.89/1.08  
% 2.89/1.08  fof(f13,plain,(
% 2.89/1.08    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (k4_xboole_0(sK3,k2_tarski(sK1,sK2)) != sK3 & ~r2_hidden(sK2,sK3) & ~r2_hidden(sK1,sK3))),
% 2.89/1.08    introduced(choice_axiom,[])).
% 2.89/1.08  
% 2.89/1.08  fof(f14,plain,(
% 2.89/1.08    k4_xboole_0(sK3,k2_tarski(sK1,sK2)) != sK3 & ~r2_hidden(sK2,sK3) & ~r2_hidden(sK1,sK3)),
% 2.89/1.08    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f5,f13])).
% 2.89/1.08  
% 2.89/1.08  fof(f25,plain,(
% 2.89/1.08    ~r2_hidden(sK2,sK3)),
% 2.89/1.08    inference(cnf_transformation,[],[f14])).
% 2.89/1.08  
% 2.89/1.08  fof(f24,plain,(
% 2.89/1.08    ~r2_hidden(sK1,sK3)),
% 2.89/1.08    inference(cnf_transformation,[],[f14])).
% 2.89/1.08  
% 2.89/1.08  fof(f20,plain,(
% 2.89/1.08    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X1) | ~r2_hidden(sK0(X0,X1,X2),X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.89/1.08    inference(cnf_transformation,[],[f10])).
% 2.89/1.08  
% 2.89/1.08  fof(f18,plain,(
% 2.89/1.08    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)) )),
% 2.89/1.08    inference(cnf_transformation,[],[f10])).
% 2.89/1.08  
% 2.89/1.08  fof(f26,plain,(
% 2.89/1.08    k4_xboole_0(sK3,k2_tarski(sK1,sK2)) != sK3),
% 2.89/1.08    inference(cnf_transformation,[],[f14])).
% 2.89/1.08  
% 2.89/1.08  cnf(c_4,plain,
% 2.89/1.08      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X0,k4_xboole_0(X2,X1)) ),
% 2.89/1.08      inference(cnf_transformation,[],[f28]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_411,plain,
% 2.89/1.08      ( ~ r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),k4_xboole_0(X0,sK3))
% 2.89/1.08      | ~ r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),sK3) ),
% 2.89/1.08      inference(instantiation,[status(thm)],[c_4]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_8905,plain,
% 2.89/1.08      ( ~ r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),k4_xboole_0(k2_tarski(sK1,sK2),sK3))
% 2.89/1.08      | ~ r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),sK3) ),
% 2.89/1.08      inference(instantiation,[status(thm)],[c_411]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_124,plain,
% 2.89/1.08      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.89/1.08      theory(equality) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_440,plain,
% 2.89/1.08      ( r2_hidden(X0,X1)
% 2.89/1.08      | ~ r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),k2_tarski(sK1,sK2))
% 2.89/1.08      | X0 != sK0(sK3,k2_tarski(sK1,sK2),sK3)
% 2.89/1.08      | X1 != k2_tarski(sK1,sK2) ),
% 2.89/1.08      inference(instantiation,[status(thm)],[c_124]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_704,plain,
% 2.89/1.08      ( r2_hidden(X0,k4_xboole_0(X1,X2))
% 2.89/1.08      | ~ r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),k2_tarski(sK1,sK2))
% 2.89/1.08      | X0 != sK0(sK3,k2_tarski(sK1,sK2),sK3)
% 2.89/1.08      | k4_xboole_0(X1,X2) != k2_tarski(sK1,sK2) ),
% 2.89/1.08      inference(instantiation,[status(thm)],[c_440]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_1695,plain,
% 2.89/1.08      ( ~ r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),k2_tarski(sK1,sK2))
% 2.89/1.08      | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),k4_xboole_0(X0,X1))
% 2.89/1.08      | sK0(sK3,k2_tarski(sK1,sK2),sK3) != sK0(sK3,k2_tarski(sK1,sK2),sK3)
% 2.89/1.08      | k4_xboole_0(X0,X1) != k2_tarski(sK1,sK2) ),
% 2.89/1.08      inference(instantiation,[status(thm)],[c_704]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_6164,plain,
% 2.89/1.08      ( ~ r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),k2_tarski(sK1,sK2))
% 2.89/1.08      | r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),k4_xboole_0(k2_tarski(sK1,sK2),sK3))
% 2.89/1.08      | sK0(sK3,k2_tarski(sK1,sK2),sK3) != sK0(sK3,k2_tarski(sK1,sK2),sK3)
% 2.89/1.08      | k4_xboole_0(k2_tarski(sK1,sK2),sK3) != k2_tarski(sK1,sK2) ),
% 2.89/1.08      inference(instantiation,[status(thm)],[c_1695]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_6,plain,
% 2.89/1.08      ( r2_hidden(X0,X1)
% 2.89/1.08      | r2_hidden(X2,X1)
% 2.89/1.08      | k4_xboole_0(k2_tarski(X0,X2),X1) = k2_tarski(X0,X2) ),
% 2.89/1.08      inference(cnf_transformation,[],[f23]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_310,plain,
% 2.89/1.08      ( k4_xboole_0(k2_tarski(X0,X1),X2) = k2_tarski(X0,X1)
% 2.89/1.08      | r2_hidden(X0,X2) = iProver_top
% 2.89/1.08      | r2_hidden(X1,X2) = iProver_top ),
% 2.89/1.08      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_10,negated_conjecture,
% 2.89/1.08      ( ~ r2_hidden(sK2,sK3) ),
% 2.89/1.08      inference(cnf_transformation,[],[f25]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_307,plain,
% 2.89/1.08      ( r2_hidden(sK2,sK3) != iProver_top ),
% 2.89/1.08      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_877,plain,
% 2.89/1.08      ( k4_xboole_0(k2_tarski(X0,sK2),sK3) = k2_tarski(X0,sK2)
% 2.89/1.08      | r2_hidden(X0,sK3) = iProver_top ),
% 2.89/1.08      inference(superposition,[status(thm)],[c_310,c_307]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_11,negated_conjecture,
% 2.89/1.08      ( ~ r2_hidden(sK1,sK3) ),
% 2.89/1.08      inference(cnf_transformation,[],[f24]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_306,plain,
% 2.89/1.08      ( r2_hidden(sK1,sK3) != iProver_top ),
% 2.89/1.08      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_1411,plain,
% 2.89/1.08      ( k4_xboole_0(k2_tarski(sK1,sK2),sK3) = k2_tarski(sK1,sK2) ),
% 2.89/1.08      inference(superposition,[status(thm)],[c_877,c_306]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_121,plain,( X0 = X0 ),theory(equality) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_669,plain,
% 2.89/1.08      ( sK0(sK3,k2_tarski(sK1,sK2),sK3) = sK0(sK3,k2_tarski(sK1,sK2),sK3) ),
% 2.89/1.08      inference(instantiation,[status(thm)],[c_121]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_0,plain,
% 2.89/1.08      ( ~ r2_hidden(sK0(X0,X1,X2),X0)
% 2.89/1.08      | ~ r2_hidden(sK0(X0,X1,X2),X2)
% 2.89/1.08      | r2_hidden(sK0(X0,X1,X2),X1)
% 2.89/1.08      | k4_xboole_0(X0,X1) = X2 ),
% 2.89/1.08      inference(cnf_transformation,[],[f20]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_404,plain,
% 2.89/1.08      ( r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),k2_tarski(sK1,sK2))
% 2.89/1.08      | ~ r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),sK3)
% 2.89/1.08      | k4_xboole_0(sK3,k2_tarski(sK1,sK2)) = sK3 ),
% 2.89/1.08      inference(instantiation,[status(thm)],[c_0]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_2,plain,
% 2.89/1.08      ( r2_hidden(sK0(X0,X1,X2),X0)
% 2.89/1.08      | r2_hidden(sK0(X0,X1,X2),X2)
% 2.89/1.08      | k4_xboole_0(X0,X1) = X2 ),
% 2.89/1.08      inference(cnf_transformation,[],[f18]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_401,plain,
% 2.89/1.08      ( r2_hidden(sK0(sK3,k2_tarski(sK1,sK2),sK3),sK3)
% 2.89/1.08      | k4_xboole_0(sK3,k2_tarski(sK1,sK2)) = sK3 ),
% 2.89/1.08      inference(instantiation,[status(thm)],[c_2]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(c_9,negated_conjecture,
% 2.89/1.08      ( k4_xboole_0(sK3,k2_tarski(sK1,sK2)) != sK3 ),
% 2.89/1.08      inference(cnf_transformation,[],[f26]) ).
% 2.89/1.08  
% 2.89/1.08  cnf(contradiction,plain,
% 2.89/1.08      ( $false ),
% 2.89/1.08      inference(minisat,
% 2.89/1.08                [status(thm)],
% 2.89/1.08                [c_8905,c_6164,c_1411,c_669,c_404,c_401,c_9]) ).
% 2.89/1.08  
% 2.89/1.08  
% 2.89/1.08  % SZS output end CNFRefutation for theBenchmark.p
% 2.89/1.08  
% 2.89/1.08  ------                               Statistics
% 2.89/1.08  
% 2.89/1.08  ------ General
% 2.89/1.08  
% 2.89/1.08  abstr_ref_over_cycles:                  0
% 2.89/1.08  abstr_ref_under_cycles:                 0
% 2.89/1.08  gc_basic_clause_elim:                   0
% 2.89/1.08  forced_gc_time:                         0
% 2.89/1.08  parsing_time:                           0.007
% 2.89/1.08  unif_index_cands_time:                  0.
% 2.89/1.08  unif_index_add_time:                    0.
% 2.89/1.08  orderings_time:                         0.
% 2.89/1.08  out_proof_time:                         0.008
% 2.89/1.08  total_time:                             0.349
% 2.89/1.08  num_of_symbols:                         38
% 2.89/1.08  num_of_terms:                           8957
% 2.89/1.08  
% 2.89/1.08  ------ Preprocessing
% 2.89/1.08  
% 2.89/1.08  num_of_splits:                          0
% 2.89/1.08  num_of_split_atoms:                     0
% 2.89/1.08  num_of_reused_defs:                     0
% 2.89/1.08  num_eq_ax_congr_red:                    6
% 2.89/1.08  num_of_sem_filtered_clauses:            1
% 2.89/1.08  num_of_subtypes:                        0
% 2.89/1.08  monotx_restored_types:                  0
% 2.89/1.08  sat_num_of_epr_types:                   0
% 2.89/1.08  sat_num_of_non_cyclic_types:            0
% 2.89/1.08  sat_guarded_non_collapsed_types:        0
% 2.89/1.08  num_pure_diseq_elim:                    0
% 2.89/1.08  simp_replaced_by:                       0
% 2.89/1.08  res_preprocessed:                       47
% 2.89/1.08  prep_upred:                             0
% 2.89/1.08  prep_unflattend:                        0
% 2.89/1.08  smt_new_axioms:                         0
% 2.89/1.08  pred_elim_cands:                        1
% 2.89/1.08  pred_elim:                              0
% 2.89/1.08  pred_elim_cl:                           0
% 2.89/1.08  pred_elim_cycles:                       1
% 2.89/1.08  merged_defs:                            0
% 2.89/1.08  merged_defs_ncl:                        0
% 2.89/1.08  bin_hyper_res:                          0
% 2.89/1.08  prep_cycles:                            3
% 2.89/1.08  pred_elim_time:                         0.
% 2.89/1.08  splitting_time:                         0.
% 2.89/1.08  sem_filter_time:                        0.
% 2.89/1.08  monotx_time:                            0.
% 2.89/1.08  subtype_inf_time:                       0.
% 2.89/1.08  
% 2.89/1.08  ------ Problem properties
% 2.89/1.08  
% 2.89/1.08  clauses:                                12
% 2.89/1.08  conjectures:                            3
% 2.89/1.08  epr:                                    2
% 2.89/1.08  horn:                                   7
% 2.89/1.08  ground:                                 3
% 2.89/1.08  unary:                                  3
% 2.89/1.08  binary:                                 4
% 2.89/1.08  lits:                                   27
% 2.89/1.08  lits_eq:                                7
% 2.89/1.08  fd_pure:                                0
% 2.89/1.08  fd_pseudo:                              0
% 2.89/1.08  fd_cond:                                0
% 2.89/1.08  fd_pseudo_cond:                         3
% 2.89/1.08  ac_symbols:                             0
% 2.89/1.08  
% 2.89/1.08  ------ Propositional Solver
% 2.89/1.08  
% 2.89/1.08  prop_solver_calls:                      24
% 2.89/1.08  prop_fast_solver_calls:                 351
% 2.89/1.08  smt_solver_calls:                       0
% 2.89/1.08  smt_fast_solver_calls:                  0
% 2.89/1.08  prop_num_of_clauses:                    2935
% 2.89/1.08  prop_preprocess_simplified:             6459
% 2.89/1.08  prop_fo_subsumed:                       0
% 2.89/1.08  prop_solver_time:                       0.
% 2.89/1.08  smt_solver_time:                        0.
% 2.89/1.08  smt_fast_solver_time:                   0.
% 2.89/1.08  prop_fast_solver_time:                  0.
% 2.89/1.08  prop_unsat_core_time:                   0.
% 2.89/1.08  
% 2.89/1.08  ------ QBF
% 2.89/1.08  
% 2.89/1.08  qbf_q_res:                              0
% 2.89/1.08  qbf_num_tautologies:                    0
% 2.89/1.08  qbf_prep_cycles:                        0
% 2.89/1.08  
% 2.89/1.08  ------ BMC1
% 2.89/1.08  
% 2.89/1.08  bmc1_current_bound:                     -1
% 2.89/1.08  bmc1_last_solved_bound:                 -1
% 2.89/1.08  bmc1_unsat_core_size:                   -1
% 2.89/1.08  bmc1_unsat_core_parents_size:           -1
% 2.89/1.08  bmc1_merge_next_fun:                    0
% 2.89/1.08  bmc1_unsat_core_clauses_time:           0.
% 2.89/1.08  
% 2.89/1.08  ------ Instantiation
% 2.89/1.08  
% 2.89/1.08  inst_num_of_clauses:                    699
% 2.89/1.08  inst_num_in_passive:                    378
% 2.89/1.08  inst_num_in_active:                     309
% 2.89/1.08  inst_num_in_unprocessed:                11
% 2.89/1.08  inst_num_of_loops:                      333
% 2.89/1.08  inst_num_of_learning_restarts:          0
% 2.89/1.08  inst_num_moves_active_passive:          21
% 2.89/1.08  inst_lit_activity:                      0
% 2.89/1.08  inst_lit_activity_moves:                0
% 2.89/1.08  inst_num_tautologies:                   0
% 2.89/1.08  inst_num_prop_implied:                  0
% 2.89/1.08  inst_num_existing_simplified:           0
% 2.89/1.08  inst_num_eq_res_simplified:             0
% 2.89/1.08  inst_num_child_elim:                    0
% 2.89/1.08  inst_num_of_dismatching_blockings:      982
% 2.89/1.08  inst_num_of_non_proper_insts:           830
% 2.89/1.08  inst_num_of_duplicates:                 0
% 2.89/1.08  inst_inst_num_from_inst_to_res:         0
% 2.89/1.08  inst_dismatching_checking_time:         0.
% 2.89/1.08  
% 2.89/1.08  ------ Resolution
% 2.89/1.08  
% 2.89/1.08  res_num_of_clauses:                     0
% 2.89/1.08  res_num_in_passive:                     0
% 2.89/1.08  res_num_in_active:                      0
% 2.89/1.08  res_num_of_loops:                       50
% 2.89/1.08  res_forward_subset_subsumed:            63
% 2.89/1.08  res_backward_subset_subsumed:           0
% 2.89/1.08  res_forward_subsumed:                   0
% 2.89/1.08  res_backward_subsumed:                  0
% 2.89/1.08  res_forward_subsumption_resolution:     0
% 2.89/1.08  res_backward_subsumption_resolution:    0
% 2.89/1.08  res_clause_to_clause_subsumption:       1894
% 2.89/1.08  res_orphan_elimination:                 0
% 2.89/1.08  res_tautology_del:                      58
% 2.89/1.08  res_num_eq_res_simplified:              0
% 2.89/1.08  res_num_sel_changes:                    0
% 2.89/1.08  res_moves_from_active_to_pass:          0
% 2.89/1.08  
% 2.89/1.08  ------ Superposition
% 2.89/1.08  
% 2.89/1.08  sup_time_total:                         0.
% 2.89/1.08  sup_time_generating:                    0.
% 2.89/1.08  sup_time_sim_full:                      0.
% 2.89/1.08  sup_time_sim_immed:                     0.
% 2.89/1.08  
% 2.89/1.08  sup_num_of_clauses:                     396
% 2.89/1.08  sup_num_in_active:                      66
% 2.89/1.08  sup_num_in_passive:                     330
% 2.89/1.08  sup_num_of_loops:                       66
% 2.89/1.08  sup_fw_superposition:                   280
% 2.89/1.08  sup_bw_superposition:                   266
% 2.89/1.08  sup_immediate_simplified:               77
% 2.89/1.08  sup_given_eliminated:                   0
% 2.89/1.08  comparisons_done:                       0
% 2.89/1.08  comparisons_avoided:                    32
% 2.89/1.08  
% 2.89/1.08  ------ Simplifications
% 2.89/1.08  
% 2.89/1.08  
% 2.89/1.08  sim_fw_subset_subsumed:                 3
% 2.89/1.08  sim_bw_subset_subsumed:                 0
% 2.89/1.08  sim_fw_subsumed:                        50
% 2.89/1.08  sim_bw_subsumed:                        0
% 2.89/1.08  sim_fw_subsumption_res:                 0
% 2.89/1.08  sim_bw_subsumption_res:                 0
% 2.89/1.08  sim_tautology_del:                      51
% 2.89/1.08  sim_eq_tautology_del:                   0
% 2.89/1.08  sim_eq_res_simp:                        2
% 2.89/1.08  sim_fw_demodulated:                     28
% 2.89/1.08  sim_bw_demodulated:                     0
% 2.89/1.08  sim_light_normalised:                   8
% 2.89/1.08  sim_joinable_taut:                      0
% 2.89/1.08  sim_joinable_simp:                      0
% 2.89/1.08  sim_ac_normalised:                      0
% 2.89/1.08  sim_smt_subsumption:                    0
% 2.89/1.08  
%------------------------------------------------------------------------------
