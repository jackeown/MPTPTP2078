%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:50 EST 2020

% Result     : Theorem 1.31s
% Output     : CNFRefutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 157 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :   13 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  149 ( 258 expanded)
%              Number of equality atoms :  116 ( 225 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f14,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f20,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK1 != sK2
      & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( sK1 != sK2
    & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f20])).

fof(f37,plain,(
    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f34,f35])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f32,f40])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f31,f41])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f43])).

fof(f52,plain,(
    k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f37,f44,f44,f44])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1)
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ) ),
    inference(definition_unfolding,[],[f36,f44,f44])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(nnf_transformation,[],[f2])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f23,f43])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f38,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f21])).

cnf(c_9,negated_conjecture,
    ( k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_0,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_7,plain,
    ( r2_hidden(X0,X1)
    | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_362,plain,
    ( k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
    | r2_hidden(X1,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_570,plain,
    ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
    | r2_hidden(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_362])).

cnf(c_699,plain,
    ( r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9,c_570])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
    | X0 = X1
    | X0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_434,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0))
    | sK1 = X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_453,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_454,plain,
    ( sK1 = sK2
    | r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_8,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_699,c_454,c_8])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.31/1.06  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.31/1.06  
% 1.31/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.31/1.06  
% 1.31/1.06  ------  iProver source info
% 1.31/1.06  
% 1.31/1.06  git: date: 2020-06-30 10:37:57 +0100
% 1.31/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.31/1.06  git: non_committed_changes: false
% 1.31/1.06  git: last_make_outside_of_git: false
% 1.31/1.06  
% 1.31/1.06  ------ 
% 1.31/1.06  
% 1.31/1.06  ------ Input Options
% 1.31/1.06  
% 1.31/1.06  --out_options                           all
% 1.31/1.06  --tptp_safe_out                         true
% 1.31/1.06  --problem_path                          ""
% 1.31/1.06  --include_path                          ""
% 1.31/1.06  --clausifier                            res/vclausify_rel
% 1.31/1.06  --clausifier_options                    --mode clausify
% 1.31/1.06  --stdin                                 false
% 1.31/1.06  --stats_out                             all
% 1.31/1.06  
% 1.31/1.06  ------ General Options
% 1.31/1.06  
% 1.31/1.06  --fof                                   false
% 1.31/1.06  --time_out_real                         305.
% 1.31/1.06  --time_out_virtual                      -1.
% 1.31/1.06  --symbol_type_check                     false
% 1.31/1.06  --clausify_out                          false
% 1.31/1.06  --sig_cnt_out                           false
% 1.31/1.06  --trig_cnt_out                          false
% 1.31/1.06  --trig_cnt_out_tolerance                1.
% 1.31/1.06  --trig_cnt_out_sk_spl                   false
% 1.31/1.06  --abstr_cl_out                          false
% 1.31/1.06  
% 1.31/1.06  ------ Global Options
% 1.31/1.06  
% 1.31/1.06  --schedule                              default
% 1.31/1.06  --add_important_lit                     false
% 1.31/1.06  --prop_solver_per_cl                    1000
% 1.31/1.06  --min_unsat_core                        false
% 1.31/1.06  --soft_assumptions                      false
% 1.31/1.06  --soft_lemma_size                       3
% 1.31/1.06  --prop_impl_unit_size                   0
% 1.31/1.06  --prop_impl_unit                        []
% 1.31/1.06  --share_sel_clauses                     true
% 1.31/1.06  --reset_solvers                         false
% 1.31/1.06  --bc_imp_inh                            [conj_cone]
% 1.31/1.06  --conj_cone_tolerance                   3.
% 1.31/1.06  --extra_neg_conj                        none
% 1.31/1.06  --large_theory_mode                     true
% 1.31/1.06  --prolific_symb_bound                   200
% 1.31/1.06  --lt_threshold                          2000
% 1.31/1.06  --clause_weak_htbl                      true
% 1.31/1.06  --gc_record_bc_elim                     false
% 1.31/1.06  
% 1.31/1.06  ------ Preprocessing Options
% 1.31/1.06  
% 1.31/1.06  --preprocessing_flag                    true
% 1.31/1.06  --time_out_prep_mult                    0.1
% 1.31/1.06  --splitting_mode                        input
% 1.31/1.06  --splitting_grd                         true
% 1.31/1.06  --splitting_cvd                         false
% 1.31/1.06  --splitting_cvd_svl                     false
% 1.31/1.06  --splitting_nvd                         32
% 1.31/1.06  --sub_typing                            true
% 1.31/1.06  --prep_gs_sim                           true
% 1.31/1.06  --prep_unflatten                        true
% 1.31/1.06  --prep_res_sim                          true
% 1.31/1.06  --prep_upred                            true
% 1.31/1.06  --prep_sem_filter                       exhaustive
% 1.31/1.06  --prep_sem_filter_out                   false
% 1.31/1.06  --pred_elim                             true
% 1.31/1.06  --res_sim_input                         true
% 1.31/1.06  --eq_ax_congr_red                       true
% 1.31/1.06  --pure_diseq_elim                       true
% 1.31/1.06  --brand_transform                       false
% 1.31/1.06  --non_eq_to_eq                          false
% 1.31/1.06  --prep_def_merge                        true
% 1.31/1.06  --prep_def_merge_prop_impl              false
% 1.31/1.06  --prep_def_merge_mbd                    true
% 1.31/1.06  --prep_def_merge_tr_red                 false
% 1.31/1.06  --prep_def_merge_tr_cl                  false
% 1.31/1.06  --smt_preprocessing                     true
% 1.31/1.06  --smt_ac_axioms                         fast
% 1.31/1.06  --preprocessed_out                      false
% 1.31/1.06  --preprocessed_stats                    false
% 1.31/1.06  
% 1.31/1.06  ------ Abstraction refinement Options
% 1.31/1.06  
% 1.31/1.06  --abstr_ref                             []
% 1.31/1.06  --abstr_ref_prep                        false
% 1.31/1.06  --abstr_ref_until_sat                   false
% 1.31/1.06  --abstr_ref_sig_restrict                funpre
% 1.31/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 1.31/1.06  --abstr_ref_under                       []
% 1.31/1.06  
% 1.31/1.06  ------ SAT Options
% 1.31/1.06  
% 1.31/1.06  --sat_mode                              false
% 1.31/1.06  --sat_fm_restart_options                ""
% 1.31/1.06  --sat_gr_def                            false
% 1.31/1.06  --sat_epr_types                         true
% 1.31/1.06  --sat_non_cyclic_types                  false
% 1.31/1.06  --sat_finite_models                     false
% 1.31/1.06  --sat_fm_lemmas                         false
% 1.31/1.06  --sat_fm_prep                           false
% 1.31/1.06  --sat_fm_uc_incr                        true
% 1.31/1.06  --sat_out_model                         small
% 1.31/1.06  --sat_out_clauses                       false
% 1.31/1.06  
% 1.31/1.06  ------ QBF Options
% 1.31/1.06  
% 1.31/1.06  --qbf_mode                              false
% 1.31/1.06  --qbf_elim_univ                         false
% 1.31/1.06  --qbf_dom_inst                          none
% 1.31/1.06  --qbf_dom_pre_inst                      false
% 1.31/1.06  --qbf_sk_in                             false
% 1.31/1.06  --qbf_pred_elim                         true
% 1.31/1.06  --qbf_split                             512
% 1.31/1.06  
% 1.31/1.06  ------ BMC1 Options
% 1.31/1.06  
% 1.31/1.06  --bmc1_incremental                      false
% 1.31/1.06  --bmc1_axioms                           reachable_all
% 1.31/1.06  --bmc1_min_bound                        0
% 1.31/1.06  --bmc1_max_bound                        -1
% 1.31/1.06  --bmc1_max_bound_default                -1
% 1.31/1.06  --bmc1_symbol_reachability              true
% 1.31/1.06  --bmc1_property_lemmas                  false
% 1.31/1.06  --bmc1_k_induction                      false
% 1.31/1.06  --bmc1_non_equiv_states                 false
% 1.31/1.06  --bmc1_deadlock                         false
% 1.31/1.06  --bmc1_ucm                              false
% 1.31/1.06  --bmc1_add_unsat_core                   none
% 1.31/1.06  --bmc1_unsat_core_children              false
% 1.31/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 1.31/1.06  --bmc1_out_stat                         full
% 1.31/1.06  --bmc1_ground_init                      false
% 1.31/1.06  --bmc1_pre_inst_next_state              false
% 1.31/1.06  --bmc1_pre_inst_state                   false
% 1.31/1.06  --bmc1_pre_inst_reach_state             false
% 1.31/1.06  --bmc1_out_unsat_core                   false
% 1.31/1.06  --bmc1_aig_witness_out                  false
% 1.31/1.06  --bmc1_verbose                          false
% 1.31/1.06  --bmc1_dump_clauses_tptp                false
% 1.31/1.06  --bmc1_dump_unsat_core_tptp             false
% 1.31/1.06  --bmc1_dump_file                        -
% 1.31/1.06  --bmc1_ucm_expand_uc_limit              128
% 1.31/1.06  --bmc1_ucm_n_expand_iterations          6
% 1.31/1.06  --bmc1_ucm_extend_mode                  1
% 1.31/1.06  --bmc1_ucm_init_mode                    2
% 1.31/1.06  --bmc1_ucm_cone_mode                    none
% 1.31/1.06  --bmc1_ucm_reduced_relation_type        0
% 1.31/1.06  --bmc1_ucm_relax_model                  4
% 1.31/1.06  --bmc1_ucm_full_tr_after_sat            true
% 1.31/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 1.31/1.06  --bmc1_ucm_layered_model                none
% 1.31/1.06  --bmc1_ucm_max_lemma_size               10
% 1.31/1.06  
% 1.31/1.06  ------ AIG Options
% 1.31/1.06  
% 1.31/1.06  --aig_mode                              false
% 1.31/1.06  
% 1.31/1.06  ------ Instantiation Options
% 1.31/1.06  
% 1.31/1.06  --instantiation_flag                    true
% 1.31/1.06  --inst_sos_flag                         false
% 1.31/1.06  --inst_sos_phase                        true
% 1.31/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.31/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.31/1.06  --inst_lit_sel_side                     num_symb
% 1.31/1.06  --inst_solver_per_active                1400
% 1.31/1.06  --inst_solver_calls_frac                1.
% 1.31/1.06  --inst_passive_queue_type               priority_queues
% 1.31/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.31/1.06  --inst_passive_queues_freq              [25;2]
% 1.31/1.06  --inst_dismatching                      true
% 1.31/1.06  --inst_eager_unprocessed_to_passive     true
% 1.31/1.06  --inst_prop_sim_given                   true
% 1.31/1.06  --inst_prop_sim_new                     false
% 1.31/1.06  --inst_subs_new                         false
% 1.31/1.06  --inst_eq_res_simp                      false
% 1.31/1.06  --inst_subs_given                       false
% 1.31/1.06  --inst_orphan_elimination               true
% 1.31/1.06  --inst_learning_loop_flag               true
% 1.31/1.06  --inst_learning_start                   3000
% 1.31/1.06  --inst_learning_factor                  2
% 1.31/1.06  --inst_start_prop_sim_after_learn       3
% 1.31/1.06  --inst_sel_renew                        solver
% 1.31/1.06  --inst_lit_activity_flag                true
% 1.31/1.06  --inst_restr_to_given                   false
% 1.31/1.06  --inst_activity_threshold               500
% 1.31/1.06  --inst_out_proof                        true
% 1.31/1.06  
% 1.31/1.06  ------ Resolution Options
% 1.31/1.06  
% 1.31/1.06  --resolution_flag                       true
% 1.31/1.06  --res_lit_sel                           adaptive
% 1.31/1.06  --res_lit_sel_side                      none
% 1.31/1.06  --res_ordering                          kbo
% 1.31/1.06  --res_to_prop_solver                    active
% 1.31/1.06  --res_prop_simpl_new                    false
% 1.31/1.06  --res_prop_simpl_given                  true
% 1.31/1.06  --res_passive_queue_type                priority_queues
% 1.31/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.31/1.06  --res_passive_queues_freq               [15;5]
% 1.31/1.06  --res_forward_subs                      full
% 1.31/1.06  --res_backward_subs                     full
% 1.31/1.06  --res_forward_subs_resolution           true
% 1.31/1.06  --res_backward_subs_resolution          true
% 1.31/1.06  --res_orphan_elimination                true
% 1.31/1.06  --res_time_limit                        2.
% 1.31/1.06  --res_out_proof                         true
% 1.31/1.06  
% 1.31/1.06  ------ Superposition Options
% 1.31/1.06  
% 1.31/1.06  --superposition_flag                    true
% 1.31/1.06  --sup_passive_queue_type                priority_queues
% 1.31/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.31/1.06  --sup_passive_queues_freq               [8;1;4]
% 1.31/1.06  --demod_completeness_check              fast
% 1.31/1.06  --demod_use_ground                      true
% 1.31/1.06  --sup_to_prop_solver                    passive
% 1.31/1.06  --sup_prop_simpl_new                    true
% 1.31/1.06  --sup_prop_simpl_given                  true
% 1.31/1.06  --sup_fun_splitting                     false
% 1.31/1.06  --sup_smt_interval                      50000
% 1.31/1.06  
% 1.31/1.06  ------ Superposition Simplification Setup
% 1.31/1.06  
% 1.31/1.06  --sup_indices_passive                   []
% 1.31/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.31/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.31/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.31/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 1.31/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.31/1.06  --sup_full_bw                           [BwDemod]
% 1.31/1.06  --sup_immed_triv                        [TrivRules]
% 1.31/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.31/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.31/1.06  --sup_immed_bw_main                     []
% 1.31/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.31/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 1.31/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.31/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.31/1.06  
% 1.31/1.06  ------ Combination Options
% 1.31/1.06  
% 1.31/1.06  --comb_res_mult                         3
% 1.31/1.06  --comb_sup_mult                         2
% 1.31/1.06  --comb_inst_mult                        10
% 1.31/1.06  
% 1.31/1.06  ------ Debug Options
% 1.31/1.06  
% 1.31/1.06  --dbg_backtrace                         false
% 1.31/1.06  --dbg_dump_prop_clauses                 false
% 1.31/1.06  --dbg_dump_prop_clauses_file            -
% 1.31/1.06  --dbg_out_stat                          false
% 1.31/1.06  ------ Parsing...
% 1.31/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.31/1.06  
% 1.31/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.31/1.06  
% 1.31/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.31/1.06  
% 1.31/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.31/1.06  ------ Proving...
% 1.31/1.06  ------ Problem Properties 
% 1.31/1.06  
% 1.31/1.06  
% 1.31/1.06  clauses                                 10
% 1.31/1.06  conjectures                             2
% 1.31/1.06  EPR                                     1
% 1.31/1.06  Horn                                    8
% 1.31/1.07  unary                                   5
% 1.31/1.07  binary                                  1
% 1.31/1.07  lits                                    20
% 1.31/1.07  lits eq                                 13
% 1.31/1.07  fd_pure                                 0
% 1.31/1.07  fd_pseudo                               0
% 1.31/1.07  fd_cond                                 0
% 1.31/1.07  fd_pseudo_cond                          3
% 1.31/1.07  AC symbols                              0
% 1.31/1.07  
% 1.31/1.07  ------ Schedule dynamic 5 is on 
% 1.31/1.07  
% 1.31/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.31/1.07  
% 1.31/1.07  
% 1.31/1.07  ------ 
% 1.31/1.07  Current options:
% 1.31/1.07  ------ 
% 1.31/1.07  
% 1.31/1.07  ------ Input Options
% 1.31/1.07  
% 1.31/1.07  --out_options                           all
% 1.31/1.07  --tptp_safe_out                         true
% 1.31/1.07  --problem_path                          ""
% 1.31/1.07  --include_path                          ""
% 1.31/1.07  --clausifier                            res/vclausify_rel
% 1.31/1.07  --clausifier_options                    --mode clausify
% 1.31/1.07  --stdin                                 false
% 1.31/1.07  --stats_out                             all
% 1.31/1.07  
% 1.31/1.07  ------ General Options
% 1.31/1.07  
% 1.31/1.07  --fof                                   false
% 1.31/1.07  --time_out_real                         305.
% 1.31/1.07  --time_out_virtual                      -1.
% 1.31/1.07  --symbol_type_check                     false
% 1.31/1.07  --clausify_out                          false
% 1.31/1.07  --sig_cnt_out                           false
% 1.31/1.07  --trig_cnt_out                          false
% 1.31/1.07  --trig_cnt_out_tolerance                1.
% 1.31/1.07  --trig_cnt_out_sk_spl                   false
% 1.31/1.07  --abstr_cl_out                          false
% 1.31/1.07  
% 1.31/1.07  ------ Global Options
% 1.31/1.07  
% 1.31/1.07  --schedule                              default
% 1.31/1.07  --add_important_lit                     false
% 1.31/1.07  --prop_solver_per_cl                    1000
% 1.31/1.07  --min_unsat_core                        false
% 1.31/1.07  --soft_assumptions                      false
% 1.31/1.07  --soft_lemma_size                       3
% 1.31/1.07  --prop_impl_unit_size                   0
% 1.31/1.07  --prop_impl_unit                        []
% 1.31/1.07  --share_sel_clauses                     true
% 1.31/1.07  --reset_solvers                         false
% 1.31/1.07  --bc_imp_inh                            [conj_cone]
% 1.31/1.07  --conj_cone_tolerance                   3.
% 1.31/1.07  --extra_neg_conj                        none
% 1.31/1.07  --large_theory_mode                     true
% 1.31/1.07  --prolific_symb_bound                   200
% 1.31/1.07  --lt_threshold                          2000
% 1.31/1.07  --clause_weak_htbl                      true
% 1.31/1.07  --gc_record_bc_elim                     false
% 1.31/1.07  
% 1.31/1.07  ------ Preprocessing Options
% 1.31/1.07  
% 1.31/1.07  --preprocessing_flag                    true
% 1.31/1.07  --time_out_prep_mult                    0.1
% 1.31/1.07  --splitting_mode                        input
% 1.31/1.07  --splitting_grd                         true
% 1.31/1.07  --splitting_cvd                         false
% 1.31/1.07  --splitting_cvd_svl                     false
% 1.31/1.07  --splitting_nvd                         32
% 1.31/1.07  --sub_typing                            true
% 1.31/1.07  --prep_gs_sim                           true
% 1.31/1.07  --prep_unflatten                        true
% 1.31/1.07  --prep_res_sim                          true
% 1.31/1.07  --prep_upred                            true
% 1.31/1.07  --prep_sem_filter                       exhaustive
% 1.31/1.07  --prep_sem_filter_out                   false
% 1.31/1.07  --pred_elim                             true
% 1.31/1.07  --res_sim_input                         true
% 1.31/1.07  --eq_ax_congr_red                       true
% 1.31/1.07  --pure_diseq_elim                       true
% 1.31/1.07  --brand_transform                       false
% 1.31/1.07  --non_eq_to_eq                          false
% 1.31/1.07  --prep_def_merge                        true
% 1.31/1.07  --prep_def_merge_prop_impl              false
% 1.31/1.07  --prep_def_merge_mbd                    true
% 1.31/1.07  --prep_def_merge_tr_red                 false
% 1.31/1.07  --prep_def_merge_tr_cl                  false
% 1.31/1.07  --smt_preprocessing                     true
% 1.31/1.07  --smt_ac_axioms                         fast
% 1.31/1.07  --preprocessed_out                      false
% 1.31/1.07  --preprocessed_stats                    false
% 1.31/1.07  
% 1.31/1.07  ------ Abstraction refinement Options
% 1.31/1.07  
% 1.31/1.07  --abstr_ref                             []
% 1.31/1.07  --abstr_ref_prep                        false
% 1.31/1.07  --abstr_ref_until_sat                   false
% 1.31/1.07  --abstr_ref_sig_restrict                funpre
% 1.31/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 1.31/1.07  --abstr_ref_under                       []
% 1.31/1.07  
% 1.31/1.07  ------ SAT Options
% 1.31/1.07  
% 1.31/1.07  --sat_mode                              false
% 1.31/1.07  --sat_fm_restart_options                ""
% 1.31/1.07  --sat_gr_def                            false
% 1.31/1.07  --sat_epr_types                         true
% 1.31/1.07  --sat_non_cyclic_types                  false
% 1.31/1.07  --sat_finite_models                     false
% 1.31/1.07  --sat_fm_lemmas                         false
% 1.31/1.07  --sat_fm_prep                           false
% 1.31/1.07  --sat_fm_uc_incr                        true
% 1.31/1.07  --sat_out_model                         small
% 1.31/1.07  --sat_out_clauses                       false
% 1.31/1.07  
% 1.31/1.07  ------ QBF Options
% 1.31/1.07  
% 1.31/1.07  --qbf_mode                              false
% 1.31/1.07  --qbf_elim_univ                         false
% 1.31/1.07  --qbf_dom_inst                          none
% 1.31/1.07  --qbf_dom_pre_inst                      false
% 1.31/1.07  --qbf_sk_in                             false
% 1.31/1.07  --qbf_pred_elim                         true
% 1.31/1.07  --qbf_split                             512
% 1.31/1.07  
% 1.31/1.07  ------ BMC1 Options
% 1.31/1.07  
% 1.31/1.07  --bmc1_incremental                      false
% 1.31/1.07  --bmc1_axioms                           reachable_all
% 1.31/1.07  --bmc1_min_bound                        0
% 1.31/1.07  --bmc1_max_bound                        -1
% 1.31/1.07  --bmc1_max_bound_default                -1
% 1.31/1.07  --bmc1_symbol_reachability              true
% 1.31/1.07  --bmc1_property_lemmas                  false
% 1.31/1.07  --bmc1_k_induction                      false
% 1.31/1.07  --bmc1_non_equiv_states                 false
% 1.31/1.07  --bmc1_deadlock                         false
% 1.31/1.07  --bmc1_ucm                              false
% 1.31/1.07  --bmc1_add_unsat_core                   none
% 1.31/1.07  --bmc1_unsat_core_children              false
% 1.31/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 1.31/1.07  --bmc1_out_stat                         full
% 1.31/1.07  --bmc1_ground_init                      false
% 1.31/1.07  --bmc1_pre_inst_next_state              false
% 1.31/1.07  --bmc1_pre_inst_state                   false
% 1.31/1.07  --bmc1_pre_inst_reach_state             false
% 1.31/1.07  --bmc1_out_unsat_core                   false
% 1.31/1.07  --bmc1_aig_witness_out                  false
% 1.31/1.07  --bmc1_verbose                          false
% 1.31/1.07  --bmc1_dump_clauses_tptp                false
% 1.31/1.07  --bmc1_dump_unsat_core_tptp             false
% 1.31/1.07  --bmc1_dump_file                        -
% 1.31/1.07  --bmc1_ucm_expand_uc_limit              128
% 1.31/1.07  --bmc1_ucm_n_expand_iterations          6
% 1.31/1.07  --bmc1_ucm_extend_mode                  1
% 1.31/1.07  --bmc1_ucm_init_mode                    2
% 1.31/1.07  --bmc1_ucm_cone_mode                    none
% 1.31/1.07  --bmc1_ucm_reduced_relation_type        0
% 1.31/1.07  --bmc1_ucm_relax_model                  4
% 1.31/1.07  --bmc1_ucm_full_tr_after_sat            true
% 1.31/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 1.31/1.07  --bmc1_ucm_layered_model                none
% 1.31/1.07  --bmc1_ucm_max_lemma_size               10
% 1.31/1.07  
% 1.31/1.07  ------ AIG Options
% 1.31/1.07  
% 1.31/1.07  --aig_mode                              false
% 1.31/1.07  
% 1.31/1.07  ------ Instantiation Options
% 1.31/1.07  
% 1.31/1.07  --instantiation_flag                    true
% 1.31/1.07  --inst_sos_flag                         false
% 1.31/1.07  --inst_sos_phase                        true
% 1.31/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.31/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.31/1.07  --inst_lit_sel_side                     none
% 1.31/1.07  --inst_solver_per_active                1400
% 1.31/1.07  --inst_solver_calls_frac                1.
% 1.31/1.07  --inst_passive_queue_type               priority_queues
% 1.31/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.31/1.07  --inst_passive_queues_freq              [25;2]
% 1.31/1.07  --inst_dismatching                      true
% 1.31/1.07  --inst_eager_unprocessed_to_passive     true
% 1.31/1.07  --inst_prop_sim_given                   true
% 1.31/1.07  --inst_prop_sim_new                     false
% 1.31/1.07  --inst_subs_new                         false
% 1.31/1.07  --inst_eq_res_simp                      false
% 1.31/1.07  --inst_subs_given                       false
% 1.31/1.07  --inst_orphan_elimination               true
% 1.31/1.07  --inst_learning_loop_flag               true
% 1.31/1.07  --inst_learning_start                   3000
% 1.31/1.07  --inst_learning_factor                  2
% 1.31/1.07  --inst_start_prop_sim_after_learn       3
% 1.31/1.07  --inst_sel_renew                        solver
% 1.31/1.07  --inst_lit_activity_flag                true
% 1.31/1.07  --inst_restr_to_given                   false
% 1.31/1.07  --inst_activity_threshold               500
% 1.31/1.07  --inst_out_proof                        true
% 1.31/1.07  
% 1.31/1.07  ------ Resolution Options
% 1.31/1.07  
% 1.31/1.07  --resolution_flag                       false
% 1.31/1.07  --res_lit_sel                           adaptive
% 1.31/1.07  --res_lit_sel_side                      none
% 1.31/1.07  --res_ordering                          kbo
% 1.31/1.07  --res_to_prop_solver                    active
% 1.31/1.07  --res_prop_simpl_new                    false
% 1.31/1.07  --res_prop_simpl_given                  true
% 1.31/1.07  --res_passive_queue_type                priority_queues
% 1.31/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.31/1.07  --res_passive_queues_freq               [15;5]
% 1.31/1.07  --res_forward_subs                      full
% 1.31/1.07  --res_backward_subs                     full
% 1.31/1.07  --res_forward_subs_resolution           true
% 1.31/1.07  --res_backward_subs_resolution          true
% 1.31/1.07  --res_orphan_elimination                true
% 1.31/1.07  --res_time_limit                        2.
% 1.31/1.07  --res_out_proof                         true
% 1.31/1.07  
% 1.31/1.07  ------ Superposition Options
% 1.31/1.07  
% 1.31/1.07  --superposition_flag                    true
% 1.31/1.07  --sup_passive_queue_type                priority_queues
% 1.31/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.31/1.07  --sup_passive_queues_freq               [8;1;4]
% 1.31/1.07  --demod_completeness_check              fast
% 1.31/1.07  --demod_use_ground                      true
% 1.31/1.07  --sup_to_prop_solver                    passive
% 1.31/1.07  --sup_prop_simpl_new                    true
% 1.31/1.07  --sup_prop_simpl_given                  true
% 1.31/1.07  --sup_fun_splitting                     false
% 1.31/1.07  --sup_smt_interval                      50000
% 1.31/1.07  
% 1.31/1.07  ------ Superposition Simplification Setup
% 1.31/1.07  
% 1.31/1.07  --sup_indices_passive                   []
% 1.31/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.31/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.31/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.31/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 1.31/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.31/1.07  --sup_full_bw                           [BwDemod]
% 1.31/1.07  --sup_immed_triv                        [TrivRules]
% 1.31/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.31/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.31/1.07  --sup_immed_bw_main                     []
% 1.31/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.31/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 1.31/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.31/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.31/1.07  
% 1.31/1.07  ------ Combination Options
% 1.31/1.07  
% 1.31/1.07  --comb_res_mult                         3
% 1.31/1.07  --comb_sup_mult                         2
% 1.31/1.07  --comb_inst_mult                        10
% 1.31/1.07  
% 1.31/1.07  ------ Debug Options
% 1.31/1.07  
% 1.31/1.07  --dbg_backtrace                         false
% 1.31/1.07  --dbg_dump_prop_clauses                 false
% 1.31/1.07  --dbg_dump_prop_clauses_file            -
% 1.31/1.07  --dbg_out_stat                          false
% 1.31/1.07  
% 1.31/1.07  
% 1.31/1.07  
% 1.31/1.07  
% 1.31/1.07  ------ Proving...
% 1.31/1.07  
% 1.31/1.07  
% 1.31/1.07  % SZS status Theorem for theBenchmark.p
% 1.31/1.07  
% 1.31/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 1.31/1.07  
% 1.31/1.07  fof(f11,conjecture,(
% 1.31/1.07    ! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 1.31/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/1.07  
% 1.31/1.07  fof(f12,negated_conjecture,(
% 1.31/1.07    ~! [X0,X1] : (k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 1.31/1.07    inference(negated_conjecture,[],[f11])).
% 1.31/1.07  
% 1.31/1.07  fof(f14,plain,(
% 1.31/1.07    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 1.31/1.07    inference(ennf_transformation,[],[f12])).
% 1.31/1.07  
% 1.31/1.07  fof(f20,plain,(
% 1.31/1.07    ? [X0,X1] : (X0 != X1 & k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1))),
% 1.31/1.07    introduced(choice_axiom,[])).
% 1.31/1.07  
% 1.31/1.07  fof(f21,plain,(
% 1.31/1.07    sK1 != sK2 & k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 1.31/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f20])).
% 1.31/1.07  
% 1.31/1.07  fof(f37,plain,(
% 1.31/1.07    k3_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 1.31/1.07    inference(cnf_transformation,[],[f21])).
% 1.31/1.07  
% 1.31/1.07  fof(f3,axiom,(
% 1.31/1.07    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.31/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/1.07  
% 1.31/1.07  fof(f29,plain,(
% 1.31/1.07    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.31/1.07    inference(cnf_transformation,[],[f3])).
% 1.31/1.07  
% 1.31/1.07  fof(f4,axiom,(
% 1.31/1.07    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.31/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/1.07  
% 1.31/1.07  fof(f30,plain,(
% 1.31/1.07    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.31/1.07    inference(cnf_transformation,[],[f4])).
% 1.31/1.07  
% 1.31/1.07  fof(f5,axiom,(
% 1.31/1.07    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.31/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/1.07  
% 1.31/1.07  fof(f31,plain,(
% 1.31/1.07    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.31/1.07    inference(cnf_transformation,[],[f5])).
% 1.31/1.07  
% 1.31/1.07  fof(f6,axiom,(
% 1.31/1.07    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.31/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/1.07  
% 1.31/1.07  fof(f32,plain,(
% 1.31/1.07    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.31/1.07    inference(cnf_transformation,[],[f6])).
% 1.31/1.07  
% 1.31/1.07  fof(f7,axiom,(
% 1.31/1.07    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 1.31/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/1.07  
% 1.31/1.07  fof(f33,plain,(
% 1.31/1.07    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 1.31/1.07    inference(cnf_transformation,[],[f7])).
% 1.31/1.07  
% 1.31/1.07  fof(f8,axiom,(
% 1.31/1.07    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.31/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/1.07  
% 1.31/1.07  fof(f34,plain,(
% 1.31/1.07    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.31/1.07    inference(cnf_transformation,[],[f8])).
% 1.31/1.07  
% 1.31/1.07  fof(f9,axiom,(
% 1.31/1.07    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.31/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/1.07  
% 1.31/1.07  fof(f35,plain,(
% 1.31/1.07    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.31/1.07    inference(cnf_transformation,[],[f9])).
% 1.31/1.07  
% 1.31/1.07  fof(f39,plain,(
% 1.31/1.07    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.31/1.07    inference(definition_unfolding,[],[f34,f35])).
% 1.31/1.07  
% 1.31/1.07  fof(f40,plain,(
% 1.31/1.07    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.31/1.07    inference(definition_unfolding,[],[f33,f39])).
% 1.31/1.07  
% 1.31/1.07  fof(f41,plain,(
% 1.31/1.07    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.31/1.07    inference(definition_unfolding,[],[f32,f40])).
% 1.31/1.07  
% 1.31/1.07  fof(f42,plain,(
% 1.31/1.07    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.31/1.07    inference(definition_unfolding,[],[f31,f41])).
% 1.31/1.07  
% 1.31/1.07  fof(f43,plain,(
% 1.31/1.07    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.31/1.07    inference(definition_unfolding,[],[f30,f42])).
% 1.31/1.07  
% 1.31/1.07  fof(f44,plain,(
% 1.31/1.07    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.31/1.07    inference(definition_unfolding,[],[f29,f43])).
% 1.31/1.07  
% 1.31/1.07  fof(f52,plain,(
% 1.31/1.07    k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 1.31/1.07    inference(definition_unfolding,[],[f37,f44,f44,f44])).
% 1.31/1.07  
% 1.31/1.07  fof(f1,axiom,(
% 1.31/1.07    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.31/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/1.07  
% 1.31/1.07  fof(f22,plain,(
% 1.31/1.07    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.31/1.07    inference(cnf_transformation,[],[f1])).
% 1.31/1.07  
% 1.31/1.07  fof(f10,axiom,(
% 1.31/1.07    ! [X0,X1] : (k3_xboole_0(X0,k1_tarski(X1)) = k1_tarski(X1) => r2_hidden(X1,X0))),
% 1.31/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/1.07  
% 1.31/1.07  fof(f13,plain,(
% 1.31/1.07    ! [X0,X1] : (r2_hidden(X1,X0) | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1))),
% 1.31/1.07    inference(ennf_transformation,[],[f10])).
% 1.31/1.07  
% 1.31/1.07  fof(f36,plain,(
% 1.31/1.07    ( ! [X0,X1] : (r2_hidden(X1,X0) | k3_xboole_0(X0,k1_tarski(X1)) != k1_tarski(X1)) )),
% 1.31/1.07    inference(cnf_transformation,[],[f13])).
% 1.31/1.07  
% 1.31/1.07  fof(f51,plain,(
% 1.31/1.07    ( ! [X0,X1] : (r2_hidden(X1,X0) | k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 1.31/1.07    inference(definition_unfolding,[],[f36,f44,f44])).
% 1.31/1.07  
% 1.31/1.07  fof(f2,axiom,(
% 1.31/1.07    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.31/1.07    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.31/1.07  
% 1.31/1.07  fof(f15,plain,(
% 1.31/1.07    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.31/1.07    inference(nnf_transformation,[],[f2])).
% 1.31/1.07  
% 1.31/1.07  fof(f16,plain,(
% 1.31/1.07    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.31/1.07    inference(flattening,[],[f15])).
% 1.31/1.07  
% 1.31/1.07  fof(f17,plain,(
% 1.31/1.07    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.31/1.07    inference(rectify,[],[f16])).
% 1.31/1.07  
% 1.31/1.07  fof(f18,plain,(
% 1.31/1.07    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.31/1.07    introduced(choice_axiom,[])).
% 1.31/1.07  
% 1.31/1.07  fof(f19,plain,(
% 1.31/1.07    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.31/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).
% 1.31/1.07  
% 1.31/1.07  fof(f23,plain,(
% 1.31/1.07    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.31/1.07    inference(cnf_transformation,[],[f19])).
% 1.31/1.07  
% 1.31/1.07  fof(f50,plain,(
% 1.31/1.07    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 1.31/1.07    inference(definition_unfolding,[],[f23,f43])).
% 1.31/1.07  
% 1.31/1.07  fof(f57,plain,(
% 1.31/1.07    ( ! [X4,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.31/1.07    inference(equality_resolution,[],[f50])).
% 1.31/1.07  
% 1.31/1.07  fof(f38,plain,(
% 1.31/1.07    sK1 != sK2),
% 1.31/1.07    inference(cnf_transformation,[],[f21])).
% 1.31/1.07  
% 1.31/1.07  cnf(c_9,negated_conjecture,
% 1.31/1.07      ( k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
% 1.31/1.07      inference(cnf_transformation,[],[f52]) ).
% 1.31/1.07  
% 1.31/1.07  cnf(c_0,plain,
% 1.31/1.07      ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
% 1.31/1.07      inference(cnf_transformation,[],[f22]) ).
% 1.31/1.07  
% 1.31/1.07  cnf(c_7,plain,
% 1.31/1.07      ( r2_hidden(X0,X1)
% 1.31/1.07      | k3_xboole_0(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 1.31/1.07      inference(cnf_transformation,[],[f51]) ).
% 1.31/1.07  
% 1.31/1.07  cnf(c_362,plain,
% 1.31/1.07      ( k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)
% 1.31/1.07      | r2_hidden(X1,X0) = iProver_top ),
% 1.31/1.07      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.31/1.07  
% 1.31/1.07  cnf(c_570,plain,
% 1.31/1.07      ( k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)
% 1.31/1.07      | r2_hidden(X0,X1) = iProver_top ),
% 1.31/1.07      inference(superposition,[status(thm)],[c_0,c_362]) ).
% 1.31/1.07  
% 1.31/1.07  cnf(c_699,plain,
% 1.31/1.07      ( r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) = iProver_top ),
% 1.31/1.07      inference(superposition,[status(thm)],[c_9,c_570]) ).
% 1.31/1.07  
% 1.31/1.07  cnf(c_6,plain,
% 1.31/1.07      ( ~ r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
% 1.31/1.07      | X0 = X1
% 1.31/1.07      | X0 = X2 ),
% 1.31/1.07      inference(cnf_transformation,[],[f57]) ).
% 1.31/1.07  
% 1.31/1.07  cnf(c_434,plain,
% 1.31/1.07      ( ~ r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,X0))
% 1.31/1.07      | sK1 = X0
% 1.31/1.07      | sK1 = sK2 ),
% 1.31/1.07      inference(instantiation,[status(thm)],[c_6]) ).
% 1.31/1.07  
% 1.31/1.07  cnf(c_453,plain,
% 1.31/1.07      ( ~ r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
% 1.31/1.07      | sK1 = sK2 ),
% 1.31/1.07      inference(instantiation,[status(thm)],[c_434]) ).
% 1.31/1.07  
% 1.31/1.07  cnf(c_454,plain,
% 1.31/1.07      ( sK1 = sK2
% 1.31/1.07      | r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) != iProver_top ),
% 1.31/1.07      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 1.31/1.07  
% 1.31/1.07  cnf(c_8,negated_conjecture,
% 1.31/1.07      ( sK1 != sK2 ),
% 1.31/1.07      inference(cnf_transformation,[],[f38]) ).
% 1.31/1.07  
% 1.31/1.07  cnf(contradiction,plain,
% 1.31/1.07      ( $false ),
% 1.31/1.07      inference(minisat,[status(thm)],[c_699,c_454,c_8]) ).
% 1.31/1.07  
% 1.31/1.07  
% 1.31/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 1.31/1.07  
% 1.31/1.07  ------                               Statistics
% 1.31/1.07  
% 1.31/1.07  ------ General
% 1.31/1.07  
% 1.31/1.07  abstr_ref_over_cycles:                  0
% 1.31/1.07  abstr_ref_under_cycles:                 0
% 1.31/1.07  gc_basic_clause_elim:                   0
% 1.31/1.07  forced_gc_time:                         0
% 1.31/1.07  parsing_time:                           0.008
% 1.31/1.07  unif_index_cands_time:                  0.
% 1.31/1.07  unif_index_add_time:                    0.
% 1.31/1.07  orderings_time:                         0.
% 1.31/1.07  out_proof_time:                         0.012
% 1.31/1.07  total_time:                             0.061
% 1.31/1.07  num_of_symbols:                         37
% 1.31/1.07  num_of_terms:                           935
% 1.31/1.07  
% 1.31/1.07  ------ Preprocessing
% 1.31/1.07  
% 1.31/1.07  num_of_splits:                          0
% 1.31/1.07  num_of_split_atoms:                     0
% 1.31/1.07  num_of_reused_defs:                     0
% 1.31/1.07  num_eq_ax_congr_red:                    6
% 1.31/1.07  num_of_sem_filtered_clauses:            1
% 1.31/1.07  num_of_subtypes:                        0
% 1.31/1.07  monotx_restored_types:                  0
% 1.31/1.07  sat_num_of_epr_types:                   0
% 1.31/1.07  sat_num_of_non_cyclic_types:            0
% 1.31/1.07  sat_guarded_non_collapsed_types:        0
% 1.31/1.07  num_pure_diseq_elim:                    0
% 1.31/1.07  simp_replaced_by:                       0
% 1.31/1.07  res_preprocessed:                       41
% 1.31/1.07  prep_upred:                             0
% 1.31/1.07  prep_unflattend:                        14
% 1.31/1.07  smt_new_axioms:                         0
% 1.31/1.07  pred_elim_cands:                        1
% 1.31/1.07  pred_elim:                              0
% 1.31/1.07  pred_elim_cl:                           0
% 1.31/1.07  pred_elim_cycles:                       1
% 1.31/1.07  merged_defs:                            0
% 1.31/1.07  merged_defs_ncl:                        0
% 1.31/1.07  bin_hyper_res:                          0
% 1.31/1.07  prep_cycles:                            3
% 1.31/1.07  pred_elim_time:                         0.002
% 1.31/1.07  splitting_time:                         0.
% 1.31/1.07  sem_filter_time:                        0.
% 1.31/1.07  monotx_time:                            0.
% 1.31/1.07  subtype_inf_time:                       0.
% 1.31/1.07  
% 1.31/1.07  ------ Problem properties
% 1.31/1.07  
% 1.31/1.07  clauses:                                10
% 1.31/1.07  conjectures:                            2
% 1.31/1.07  epr:                                    1
% 1.31/1.07  horn:                                   8
% 1.31/1.07  ground:                                 2
% 1.31/1.07  unary:                                  5
% 1.31/1.07  binary:                                 1
% 1.31/1.07  lits:                                   20
% 1.31/1.07  lits_eq:                                13
% 1.31/1.07  fd_pure:                                0
% 1.31/1.07  fd_pseudo:                              0
% 1.31/1.07  fd_cond:                                0
% 1.31/1.07  fd_pseudo_cond:                         3
% 1.31/1.07  ac_symbols:                             0
% 1.31/1.07  
% 1.31/1.07  ------ Propositional Solver
% 1.31/1.07  
% 1.31/1.07  prop_solver_calls:                      21
% 1.31/1.07  prop_fast_solver_calls:                 246
% 1.31/1.07  smt_solver_calls:                       0
% 1.31/1.07  smt_fast_solver_calls:                  0
% 1.31/1.07  prop_num_of_clauses:                    204
% 1.31/1.07  prop_preprocess_simplified:             1246
% 1.31/1.07  prop_fo_subsumed:                       1
% 1.31/1.07  prop_solver_time:                       0.
% 1.31/1.07  smt_solver_time:                        0.
% 1.31/1.07  smt_fast_solver_time:                   0.
% 1.31/1.07  prop_fast_solver_time:                  0.
% 1.31/1.07  prop_unsat_core_time:                   0.
% 1.31/1.07  
% 1.31/1.07  ------ QBF
% 1.31/1.07  
% 1.31/1.07  qbf_q_res:                              0
% 1.31/1.07  qbf_num_tautologies:                    0
% 1.31/1.07  qbf_prep_cycles:                        0
% 1.31/1.07  
% 1.31/1.07  ------ BMC1
% 1.31/1.07  
% 1.31/1.07  bmc1_current_bound:                     -1
% 1.31/1.07  bmc1_last_solved_bound:                 -1
% 1.31/1.07  bmc1_unsat_core_size:                   -1
% 1.31/1.07  bmc1_unsat_core_parents_size:           -1
% 1.31/1.07  bmc1_merge_next_fun:                    0
% 1.31/1.07  bmc1_unsat_core_clauses_time:           0.
% 1.31/1.07  
% 1.31/1.07  ------ Instantiation
% 1.31/1.07  
% 1.31/1.07  inst_num_of_clauses:                    66
% 1.31/1.07  inst_num_in_passive:                    30
% 1.31/1.07  inst_num_in_active:                     35
% 1.31/1.07  inst_num_in_unprocessed:                1
% 1.31/1.07  inst_num_of_loops:                      40
% 1.31/1.07  inst_num_of_learning_restarts:          0
% 1.31/1.07  inst_num_moves_active_passive:          3
% 1.31/1.07  inst_lit_activity:                      0
% 1.31/1.07  inst_lit_activity_moves:                0
% 1.31/1.07  inst_num_tautologies:                   0
% 1.31/1.07  inst_num_prop_implied:                  0
% 1.31/1.07  inst_num_existing_simplified:           0
% 1.31/1.07  inst_num_eq_res_simplified:             0
% 1.31/1.07  inst_num_child_elim:                    0
% 1.31/1.07  inst_num_of_dismatching_blockings:      15
% 1.31/1.07  inst_num_of_non_proper_insts:           55
% 1.31/1.07  inst_num_of_duplicates:                 0
% 1.31/1.07  inst_inst_num_from_inst_to_res:         0
% 1.31/1.07  inst_dismatching_checking_time:         0.
% 1.31/1.07  
% 1.31/1.07  ------ Resolution
% 1.31/1.07  
% 1.31/1.07  res_num_of_clauses:                     0
% 1.31/1.07  res_num_in_passive:                     0
% 1.31/1.07  res_num_in_active:                      0
% 1.31/1.07  res_num_of_loops:                       44
% 1.31/1.07  res_forward_subset_subsumed:            3
% 1.31/1.07  res_backward_subset_subsumed:           0
% 1.31/1.07  res_forward_subsumed:                   0
% 1.31/1.07  res_backward_subsumed:                  0
% 1.31/1.07  res_forward_subsumption_resolution:     0
% 1.31/1.07  res_backward_subsumption_resolution:    0
% 1.31/1.07  res_clause_to_clause_subsumption:       36
% 1.31/1.07  res_orphan_elimination:                 0
% 1.31/1.07  res_tautology_del:                      4
% 1.31/1.07  res_num_eq_res_simplified:              0
% 1.31/1.07  res_num_sel_changes:                    0
% 1.31/1.07  res_moves_from_active_to_pass:          0
% 1.31/1.07  
% 1.31/1.07  ------ Superposition
% 1.31/1.07  
% 1.31/1.07  sup_time_total:                         0.
% 1.31/1.07  sup_time_generating:                    0.
% 1.31/1.07  sup_time_sim_full:                      0.
% 1.31/1.07  sup_time_sim_immed:                     0.
% 1.31/1.07  
% 1.31/1.07  sup_num_of_clauses:                     13
% 1.31/1.07  sup_num_in_active:                      8
% 1.31/1.07  sup_num_in_passive:                     5
% 1.31/1.07  sup_num_of_loops:                       7
% 1.31/1.07  sup_fw_superposition:                   6
% 1.31/1.07  sup_bw_superposition:                   0
% 1.31/1.07  sup_immediate_simplified:               0
% 1.31/1.07  sup_given_eliminated:                   0
% 1.31/1.07  comparisons_done:                       0
% 1.31/1.07  comparisons_avoided:                    0
% 1.31/1.07  
% 1.31/1.07  ------ Simplifications
% 1.31/1.07  
% 1.31/1.07  
% 1.31/1.07  sim_fw_subset_subsumed:                 0
% 1.31/1.07  sim_bw_subset_subsumed:                 0
% 1.31/1.07  sim_fw_subsumed:                        0
% 1.31/1.07  sim_bw_subsumed:                        0
% 1.31/1.07  sim_fw_subsumption_res:                 0
% 1.31/1.07  sim_bw_subsumption_res:                 0
% 1.31/1.07  sim_tautology_del:                      0
% 1.31/1.07  sim_eq_tautology_del:                   0
% 1.31/1.07  sim_eq_res_simp:                        0
% 1.31/1.07  sim_fw_demodulated:                     0
% 1.31/1.07  sim_bw_demodulated:                     0
% 1.31/1.07  sim_light_normalised:                   0
% 1.31/1.07  sim_joinable_taut:                      0
% 1.31/1.07  sim_joinable_simp:                      0
% 1.31/1.07  sim_ac_normalised:                      0
% 1.31/1.07  sim_smt_subsumption:                    0
% 1.31/1.07  
%------------------------------------------------------------------------------
