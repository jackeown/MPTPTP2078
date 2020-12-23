%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:26 EST 2020

% Result     : Theorem 0.96s
% Output     : CNFRefutation 0.96s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 119 expanded)
%              Number of clauses        :   17 (  18 expanded)
%              Number of leaves         :    9 (  33 expanded)
%              Depth                    :   14
%              Number of atoms          :  187 ( 547 expanded)
%              Number of equality atoms :  148 ( 438 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f11,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK1 != sK2
      & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( sK1 != sK2
    & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f11,f17])).

fof(f33,plain,(
    k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f47,plain,(
    k5_xboole_0(k2_tarski(sK1,sK1),k4_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK1,sK1))) = k2_tarski(sK1,sK1) ),
    inference(definition_unfolding,[],[f33,f19,f30,f30,f30])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f12])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f13])).

fof(f15,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK0(X0,X1,X2,X3) != X2
            & sK0(X0,X1,X2,X3) != X1
            & sK0(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
        & ( sK0(X0,X1,X2,X3) = X2
          | sK0(X0,X1,X2,X3) = X1
          | sK0(X0,X1,X2,X3) = X0
          | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK0(X0,X1,X2,X3) != X2
              & sK0(X0,X1,X2,X3) != X1
              & sK0(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2,X3),X3) )
          & ( sK0(X0,X1,X2,X3) = X2
            | sK0(X0,X1,X2,X3) = X1
            | sK0(X0,X1,X2,X3) = X0
            | r2_hidden(sK0(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).

fof(f22,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f28,f19,f30])).

fof(f43,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) != X3 ) ),
    inference(definition_unfolding,[],[f22,f35])).

fof(f50,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0))) != X3 ) ),
    inference(equality_resolution,[],[f43])).

fof(f51,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0)))) ),
    inference(equality_resolution,[],[f50])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))) = k2_tarski(X0,X1) ),
    inference(definition_unfolding,[],[f31,f35])).

fof(f20,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) != X3 ) ),
    inference(definition_unfolding,[],[f20,f35])).

fof(f54,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) ) ),
    inference(equality_resolution,[],[f45])).

fof(f21,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) != X3 ) ),
    inference(definition_unfolding,[],[f21,f35])).

fof(f52,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X5,X5),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5))) != X3 ) ),
    inference(equality_resolution,[],[f44])).

fof(f53,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k5_xboole_0(k2_tarski(X5,X5),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5)))) ),
    inference(equality_resolution,[],[f52])).

fof(f34,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_11,negated_conjecture,
    ( k5_xboole_0(k2_tarski(sK1,sK1),k4_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK1,sK1))) = k2_tarski(sK1,sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_6,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X1)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_451,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_694,plain,
    ( r2_hidden(sK2,k2_tarski(sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_451])).

cnf(c_0,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))
    | X0 = X1
    | X0 = X2
    | X0 = X3 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_449,plain,
    ( X0 = X1
    | X0 = X2
    | X0 = X3
    | r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_975,plain,
    ( X0 = X1
    | X2 = X1
    | r2_hidden(X1,k2_tarski(X2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_449])).

cnf(c_1227,plain,
    ( sK2 = sK1 ),
    inference(superposition,[status(thm)],[c_694,c_975])).

cnf(c_313,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_524,plain,
    ( sK2 != X0
    | sK1 != X0
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_313])).

cnf(c_525,plain,
    ( sK2 != sK1
    | sK1 = sK2
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_524])).

cnf(c_7,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_17,plain,
    ( r2_hidden(sK1,k5_xboole_0(k2_tarski(sK1,sK1),k4_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_14,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k2_tarski(sK1,sK1),k4_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1))))
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_10,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f34])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1227,c_525,c_17,c_14,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:54:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 0.96/0.94  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.96/0.94  
% 0.96/0.94  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.96/0.94  
% 0.96/0.94  ------  iProver source info
% 0.96/0.94  
% 0.96/0.94  git: date: 2020-06-30 10:37:57 +0100
% 0.96/0.94  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.96/0.94  git: non_committed_changes: false
% 0.96/0.94  git: last_make_outside_of_git: false
% 0.96/0.94  
% 0.96/0.94  ------ 
% 0.96/0.94  
% 0.96/0.94  ------ Input Options
% 0.96/0.94  
% 0.96/0.94  --out_options                           all
% 0.96/0.94  --tptp_safe_out                         true
% 0.96/0.94  --problem_path                          ""
% 0.96/0.94  --include_path                          ""
% 0.96/0.94  --clausifier                            res/vclausify_rel
% 0.96/0.94  --clausifier_options                    --mode clausify
% 0.96/0.94  --stdin                                 false
% 0.96/0.94  --stats_out                             all
% 0.96/0.94  
% 0.96/0.94  ------ General Options
% 0.96/0.94  
% 0.96/0.94  --fof                                   false
% 0.96/0.94  --time_out_real                         305.
% 0.96/0.94  --time_out_virtual                      -1.
% 0.96/0.94  --symbol_type_check                     false
% 0.96/0.94  --clausify_out                          false
% 0.96/0.94  --sig_cnt_out                           false
% 0.96/0.94  --trig_cnt_out                          false
% 0.96/0.94  --trig_cnt_out_tolerance                1.
% 0.96/0.94  --trig_cnt_out_sk_spl                   false
% 0.96/0.94  --abstr_cl_out                          false
% 0.96/0.94  
% 0.96/0.94  ------ Global Options
% 0.96/0.94  
% 0.96/0.94  --schedule                              default
% 0.96/0.94  --add_important_lit                     false
% 0.96/0.94  --prop_solver_per_cl                    1000
% 0.96/0.94  --min_unsat_core                        false
% 0.96/0.94  --soft_assumptions                      false
% 0.96/0.94  --soft_lemma_size                       3
% 0.96/0.94  --prop_impl_unit_size                   0
% 0.96/0.94  --prop_impl_unit                        []
% 0.96/0.94  --share_sel_clauses                     true
% 0.96/0.94  --reset_solvers                         false
% 0.96/0.94  --bc_imp_inh                            [conj_cone]
% 0.96/0.94  --conj_cone_tolerance                   3.
% 0.96/0.94  --extra_neg_conj                        none
% 0.96/0.94  --large_theory_mode                     true
% 0.96/0.94  --prolific_symb_bound                   200
% 0.96/0.94  --lt_threshold                          2000
% 0.96/0.94  --clause_weak_htbl                      true
% 0.96/0.94  --gc_record_bc_elim                     false
% 0.96/0.94  
% 0.96/0.94  ------ Preprocessing Options
% 0.96/0.94  
% 0.96/0.94  --preprocessing_flag                    true
% 0.96/0.94  --time_out_prep_mult                    0.1
% 0.96/0.94  --splitting_mode                        input
% 0.96/0.94  --splitting_grd                         true
% 0.96/0.94  --splitting_cvd                         false
% 0.96/0.94  --splitting_cvd_svl                     false
% 0.96/0.94  --splitting_nvd                         32
% 0.96/0.94  --sub_typing                            true
% 0.96/0.94  --prep_gs_sim                           true
% 0.96/0.94  --prep_unflatten                        true
% 0.96/0.94  --prep_res_sim                          true
% 0.96/0.94  --prep_upred                            true
% 0.96/0.94  --prep_sem_filter                       exhaustive
% 0.96/0.94  --prep_sem_filter_out                   false
% 0.96/0.94  --pred_elim                             true
% 0.96/0.94  --res_sim_input                         true
% 0.96/0.94  --eq_ax_congr_red                       true
% 0.96/0.94  --pure_diseq_elim                       true
% 0.96/0.94  --brand_transform                       false
% 0.96/0.94  --non_eq_to_eq                          false
% 0.96/0.94  --prep_def_merge                        true
% 0.96/0.94  --prep_def_merge_prop_impl              false
% 0.96/0.94  --prep_def_merge_mbd                    true
% 0.96/0.94  --prep_def_merge_tr_red                 false
% 0.96/0.94  --prep_def_merge_tr_cl                  false
% 0.96/0.94  --smt_preprocessing                     true
% 0.96/0.94  --smt_ac_axioms                         fast
% 0.96/0.94  --preprocessed_out                      false
% 0.96/0.94  --preprocessed_stats                    false
% 0.96/0.94  
% 0.96/0.94  ------ Abstraction refinement Options
% 0.96/0.94  
% 0.96/0.94  --abstr_ref                             []
% 0.96/0.94  --abstr_ref_prep                        false
% 0.96/0.94  --abstr_ref_until_sat                   false
% 0.96/0.94  --abstr_ref_sig_restrict                funpre
% 0.96/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 0.96/0.94  --abstr_ref_under                       []
% 0.96/0.94  
% 0.96/0.94  ------ SAT Options
% 0.96/0.94  
% 0.96/0.94  --sat_mode                              false
% 0.96/0.94  --sat_fm_restart_options                ""
% 0.96/0.94  --sat_gr_def                            false
% 0.96/0.94  --sat_epr_types                         true
% 0.96/0.94  --sat_non_cyclic_types                  false
% 0.96/0.94  --sat_finite_models                     false
% 0.96/0.94  --sat_fm_lemmas                         false
% 0.96/0.94  --sat_fm_prep                           false
% 0.96/0.94  --sat_fm_uc_incr                        true
% 0.96/0.94  --sat_out_model                         small
% 0.96/0.94  --sat_out_clauses                       false
% 0.96/0.94  
% 0.96/0.94  ------ QBF Options
% 0.96/0.94  
% 0.96/0.94  --qbf_mode                              false
% 0.96/0.94  --qbf_elim_univ                         false
% 0.96/0.94  --qbf_dom_inst                          none
% 0.96/0.94  --qbf_dom_pre_inst                      false
% 0.96/0.94  --qbf_sk_in                             false
% 0.96/0.94  --qbf_pred_elim                         true
% 0.96/0.94  --qbf_split                             512
% 0.96/0.94  
% 0.96/0.94  ------ BMC1 Options
% 0.96/0.94  
% 0.96/0.94  --bmc1_incremental                      false
% 0.96/0.94  --bmc1_axioms                           reachable_all
% 0.96/0.94  --bmc1_min_bound                        0
% 0.96/0.94  --bmc1_max_bound                        -1
% 0.96/0.94  --bmc1_max_bound_default                -1
% 0.96/0.94  --bmc1_symbol_reachability              true
% 0.96/0.94  --bmc1_property_lemmas                  false
% 0.96/0.94  --bmc1_k_induction                      false
% 0.96/0.94  --bmc1_non_equiv_states                 false
% 0.96/0.94  --bmc1_deadlock                         false
% 0.96/0.94  --bmc1_ucm                              false
% 0.96/0.94  --bmc1_add_unsat_core                   none
% 0.96/0.94  --bmc1_unsat_core_children              false
% 0.96/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 0.96/0.94  --bmc1_out_stat                         full
% 0.96/0.94  --bmc1_ground_init                      false
% 0.96/0.94  --bmc1_pre_inst_next_state              false
% 0.96/0.94  --bmc1_pre_inst_state                   false
% 0.96/0.94  --bmc1_pre_inst_reach_state             false
% 0.96/0.94  --bmc1_out_unsat_core                   false
% 0.96/0.94  --bmc1_aig_witness_out                  false
% 0.96/0.94  --bmc1_verbose                          false
% 0.96/0.94  --bmc1_dump_clauses_tptp                false
% 0.96/0.94  --bmc1_dump_unsat_core_tptp             false
% 0.96/0.94  --bmc1_dump_file                        -
% 0.96/0.94  --bmc1_ucm_expand_uc_limit              128
% 0.96/0.94  --bmc1_ucm_n_expand_iterations          6
% 0.96/0.94  --bmc1_ucm_extend_mode                  1
% 0.96/0.94  --bmc1_ucm_init_mode                    2
% 0.96/0.94  --bmc1_ucm_cone_mode                    none
% 0.96/0.94  --bmc1_ucm_reduced_relation_type        0
% 0.96/0.94  --bmc1_ucm_relax_model                  4
% 0.96/0.94  --bmc1_ucm_full_tr_after_sat            true
% 0.96/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 0.96/0.94  --bmc1_ucm_layered_model                none
% 0.96/0.94  --bmc1_ucm_max_lemma_size               10
% 0.96/0.94  
% 0.96/0.94  ------ AIG Options
% 0.96/0.94  
% 0.96/0.94  --aig_mode                              false
% 0.96/0.94  
% 0.96/0.94  ------ Instantiation Options
% 0.96/0.94  
% 0.96/0.94  --instantiation_flag                    true
% 0.96/0.94  --inst_sos_flag                         false
% 0.96/0.94  --inst_sos_phase                        true
% 0.96/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.96/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.96/0.94  --inst_lit_sel_side                     num_symb
% 0.96/0.94  --inst_solver_per_active                1400
% 0.96/0.94  --inst_solver_calls_frac                1.
% 0.96/0.94  --inst_passive_queue_type               priority_queues
% 0.96/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.96/0.94  --inst_passive_queues_freq              [25;2]
% 0.96/0.94  --inst_dismatching                      true
% 0.96/0.94  --inst_eager_unprocessed_to_passive     true
% 0.96/0.94  --inst_prop_sim_given                   true
% 0.96/0.94  --inst_prop_sim_new                     false
% 0.96/0.94  --inst_subs_new                         false
% 0.96/0.94  --inst_eq_res_simp                      false
% 0.96/0.94  --inst_subs_given                       false
% 0.96/0.94  --inst_orphan_elimination               true
% 0.96/0.94  --inst_learning_loop_flag               true
% 0.96/0.94  --inst_learning_start                   3000
% 0.96/0.94  --inst_learning_factor                  2
% 0.96/0.94  --inst_start_prop_sim_after_learn       3
% 0.96/0.94  --inst_sel_renew                        solver
% 0.96/0.94  --inst_lit_activity_flag                true
% 0.96/0.94  --inst_restr_to_given                   false
% 0.96/0.94  --inst_activity_threshold               500
% 0.96/0.94  --inst_out_proof                        true
% 0.96/0.94  
% 0.96/0.94  ------ Resolution Options
% 0.96/0.94  
% 0.96/0.94  --resolution_flag                       true
% 0.96/0.94  --res_lit_sel                           adaptive
% 0.96/0.94  --res_lit_sel_side                      none
% 0.96/0.94  --res_ordering                          kbo
% 0.96/0.94  --res_to_prop_solver                    active
% 0.96/0.94  --res_prop_simpl_new                    false
% 0.96/0.94  --res_prop_simpl_given                  true
% 0.96/0.94  --res_passive_queue_type                priority_queues
% 0.96/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.96/0.94  --res_passive_queues_freq               [15;5]
% 0.96/0.94  --res_forward_subs                      full
% 0.96/0.94  --res_backward_subs                     full
% 0.96/0.94  --res_forward_subs_resolution           true
% 0.96/0.94  --res_backward_subs_resolution          true
% 0.96/0.94  --res_orphan_elimination                true
% 0.96/0.94  --res_time_limit                        2.
% 0.96/0.94  --res_out_proof                         true
% 0.96/0.94  
% 0.96/0.94  ------ Superposition Options
% 0.96/0.94  
% 0.96/0.94  --superposition_flag                    true
% 0.96/0.94  --sup_passive_queue_type                priority_queues
% 0.96/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.96/0.94  --sup_passive_queues_freq               [8;1;4]
% 0.96/0.94  --demod_completeness_check              fast
% 0.96/0.94  --demod_use_ground                      true
% 0.96/0.94  --sup_to_prop_solver                    passive
% 0.96/0.94  --sup_prop_simpl_new                    true
% 0.96/0.94  --sup_prop_simpl_given                  true
% 0.96/0.94  --sup_fun_splitting                     false
% 0.96/0.94  --sup_smt_interval                      50000
% 0.96/0.94  
% 0.96/0.94  ------ Superposition Simplification Setup
% 0.96/0.94  
% 0.96/0.94  --sup_indices_passive                   []
% 0.96/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 0.96/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.94  --sup_full_bw                           [BwDemod]
% 0.96/0.94  --sup_immed_triv                        [TrivRules]
% 0.96/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.96/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.94  --sup_immed_bw_main                     []
% 0.96/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 0.96/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/0.94  
% 0.96/0.94  ------ Combination Options
% 0.96/0.94  
% 0.96/0.94  --comb_res_mult                         3
% 0.96/0.94  --comb_sup_mult                         2
% 0.96/0.94  --comb_inst_mult                        10
% 0.96/0.94  
% 0.96/0.94  ------ Debug Options
% 0.96/0.94  
% 0.96/0.94  --dbg_backtrace                         false
% 0.96/0.94  --dbg_dump_prop_clauses                 false
% 0.96/0.94  --dbg_dump_prop_clauses_file            -
% 0.96/0.94  --dbg_out_stat                          false
% 0.96/0.94  ------ Parsing...
% 0.96/0.94  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.96/0.94  
% 0.96/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.96/0.94  
% 0.96/0.94  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.96/0.94  
% 0.96/0.94  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.96/0.94  ------ Proving...
% 0.96/0.94  ------ Problem Properties 
% 0.96/0.94  
% 0.96/0.94  
% 0.96/0.94  clauses                                 12
% 0.96/0.94  conjectures                             2
% 0.96/0.94  EPR                                     1
% 0.96/0.94  Horn                                    10
% 0.96/0.94  unary                                   7
% 0.96/0.94  binary                                  0
% 0.96/0.94  lits                                    25
% 0.96/0.94  lits eq                                 17
% 0.96/0.94  fd_pure                                 0
% 0.96/0.94  fd_pseudo                               0
% 0.96/0.94  fd_cond                                 0
% 0.96/0.94  fd_pseudo_cond                          4
% 0.96/0.94  AC symbols                              0
% 0.96/0.94  
% 0.96/0.94  ------ Schedule dynamic 5 is on 
% 0.96/0.94  
% 0.96/0.94  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.96/0.94  
% 0.96/0.94  
% 0.96/0.94  ------ 
% 0.96/0.94  Current options:
% 0.96/0.94  ------ 
% 0.96/0.94  
% 0.96/0.94  ------ Input Options
% 0.96/0.94  
% 0.96/0.94  --out_options                           all
% 0.96/0.94  --tptp_safe_out                         true
% 0.96/0.94  --problem_path                          ""
% 0.96/0.94  --include_path                          ""
% 0.96/0.94  --clausifier                            res/vclausify_rel
% 0.96/0.94  --clausifier_options                    --mode clausify
% 0.96/0.94  --stdin                                 false
% 0.96/0.94  --stats_out                             all
% 0.96/0.94  
% 0.96/0.94  ------ General Options
% 0.96/0.94  
% 0.96/0.94  --fof                                   false
% 0.96/0.94  --time_out_real                         305.
% 0.96/0.94  --time_out_virtual                      -1.
% 0.96/0.94  --symbol_type_check                     false
% 0.96/0.94  --clausify_out                          false
% 0.96/0.94  --sig_cnt_out                           false
% 0.96/0.94  --trig_cnt_out                          false
% 0.96/0.94  --trig_cnt_out_tolerance                1.
% 0.96/0.94  --trig_cnt_out_sk_spl                   false
% 0.96/0.94  --abstr_cl_out                          false
% 0.96/0.94  
% 0.96/0.94  ------ Global Options
% 0.96/0.94  
% 0.96/0.94  --schedule                              default
% 0.96/0.94  --add_important_lit                     false
% 0.96/0.94  --prop_solver_per_cl                    1000
% 0.96/0.94  --min_unsat_core                        false
% 0.96/0.94  --soft_assumptions                      false
% 0.96/0.94  --soft_lemma_size                       3
% 0.96/0.94  --prop_impl_unit_size                   0
% 0.96/0.94  --prop_impl_unit                        []
% 0.96/0.94  --share_sel_clauses                     true
% 0.96/0.94  --reset_solvers                         false
% 0.96/0.94  --bc_imp_inh                            [conj_cone]
% 0.96/0.94  --conj_cone_tolerance                   3.
% 0.96/0.94  --extra_neg_conj                        none
% 0.96/0.94  --large_theory_mode                     true
% 0.96/0.94  --prolific_symb_bound                   200
% 0.96/0.94  --lt_threshold                          2000
% 0.96/0.94  --clause_weak_htbl                      true
% 0.96/0.94  --gc_record_bc_elim                     false
% 0.96/0.94  
% 0.96/0.94  ------ Preprocessing Options
% 0.96/0.94  
% 0.96/0.94  --preprocessing_flag                    true
% 0.96/0.94  --time_out_prep_mult                    0.1
% 0.96/0.94  --splitting_mode                        input
% 0.96/0.94  --splitting_grd                         true
% 0.96/0.94  --splitting_cvd                         false
% 0.96/0.94  --splitting_cvd_svl                     false
% 0.96/0.94  --splitting_nvd                         32
% 0.96/0.94  --sub_typing                            true
% 0.96/0.94  --prep_gs_sim                           true
% 0.96/0.94  --prep_unflatten                        true
% 0.96/0.94  --prep_res_sim                          true
% 0.96/0.94  --prep_upred                            true
% 0.96/0.94  --prep_sem_filter                       exhaustive
% 0.96/0.94  --prep_sem_filter_out                   false
% 0.96/0.94  --pred_elim                             true
% 0.96/0.94  --res_sim_input                         true
% 0.96/0.94  --eq_ax_congr_red                       true
% 0.96/0.94  --pure_diseq_elim                       true
% 0.96/0.94  --brand_transform                       false
% 0.96/0.94  --non_eq_to_eq                          false
% 0.96/0.94  --prep_def_merge                        true
% 0.96/0.94  --prep_def_merge_prop_impl              false
% 0.96/0.94  --prep_def_merge_mbd                    true
% 0.96/0.94  --prep_def_merge_tr_red                 false
% 0.96/0.94  --prep_def_merge_tr_cl                  false
% 0.96/0.94  --smt_preprocessing                     true
% 0.96/0.94  --smt_ac_axioms                         fast
% 0.96/0.94  --preprocessed_out                      false
% 0.96/0.94  --preprocessed_stats                    false
% 0.96/0.94  
% 0.96/0.94  ------ Abstraction refinement Options
% 0.96/0.94  
% 0.96/0.94  --abstr_ref                             []
% 0.96/0.94  --abstr_ref_prep                        false
% 0.96/0.94  --abstr_ref_until_sat                   false
% 0.96/0.94  --abstr_ref_sig_restrict                funpre
% 0.96/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 0.96/0.94  --abstr_ref_under                       []
% 0.96/0.94  
% 0.96/0.94  ------ SAT Options
% 0.96/0.94  
% 0.96/0.94  --sat_mode                              false
% 0.96/0.94  --sat_fm_restart_options                ""
% 0.96/0.94  --sat_gr_def                            false
% 0.96/0.94  --sat_epr_types                         true
% 0.96/0.94  --sat_non_cyclic_types                  false
% 0.96/0.94  --sat_finite_models                     false
% 0.96/0.94  --sat_fm_lemmas                         false
% 0.96/0.94  --sat_fm_prep                           false
% 0.96/0.94  --sat_fm_uc_incr                        true
% 0.96/0.94  --sat_out_model                         small
% 0.96/0.94  --sat_out_clauses                       false
% 0.96/0.94  
% 0.96/0.94  ------ QBF Options
% 0.96/0.94  
% 0.96/0.94  --qbf_mode                              false
% 0.96/0.94  --qbf_elim_univ                         false
% 0.96/0.94  --qbf_dom_inst                          none
% 0.96/0.94  --qbf_dom_pre_inst                      false
% 0.96/0.94  --qbf_sk_in                             false
% 0.96/0.94  --qbf_pred_elim                         true
% 0.96/0.94  --qbf_split                             512
% 0.96/0.94  
% 0.96/0.94  ------ BMC1 Options
% 0.96/0.94  
% 0.96/0.94  --bmc1_incremental                      false
% 0.96/0.94  --bmc1_axioms                           reachable_all
% 0.96/0.94  --bmc1_min_bound                        0
% 0.96/0.94  --bmc1_max_bound                        -1
% 0.96/0.94  --bmc1_max_bound_default                -1
% 0.96/0.94  --bmc1_symbol_reachability              true
% 0.96/0.94  --bmc1_property_lemmas                  false
% 0.96/0.94  --bmc1_k_induction                      false
% 0.96/0.94  --bmc1_non_equiv_states                 false
% 0.96/0.94  --bmc1_deadlock                         false
% 0.96/0.94  --bmc1_ucm                              false
% 0.96/0.94  --bmc1_add_unsat_core                   none
% 0.96/0.94  --bmc1_unsat_core_children              false
% 0.96/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 0.96/0.94  --bmc1_out_stat                         full
% 0.96/0.94  --bmc1_ground_init                      false
% 0.96/0.94  --bmc1_pre_inst_next_state              false
% 0.96/0.94  --bmc1_pre_inst_state                   false
% 0.96/0.94  --bmc1_pre_inst_reach_state             false
% 0.96/0.94  --bmc1_out_unsat_core                   false
% 0.96/0.94  --bmc1_aig_witness_out                  false
% 0.96/0.94  --bmc1_verbose                          false
% 0.96/0.94  --bmc1_dump_clauses_tptp                false
% 0.96/0.94  --bmc1_dump_unsat_core_tptp             false
% 0.96/0.94  --bmc1_dump_file                        -
% 0.96/0.94  --bmc1_ucm_expand_uc_limit              128
% 0.96/0.94  --bmc1_ucm_n_expand_iterations          6
% 0.96/0.94  --bmc1_ucm_extend_mode                  1
% 0.96/0.94  --bmc1_ucm_init_mode                    2
% 0.96/0.94  --bmc1_ucm_cone_mode                    none
% 0.96/0.94  --bmc1_ucm_reduced_relation_type        0
% 0.96/0.94  --bmc1_ucm_relax_model                  4
% 0.96/0.94  --bmc1_ucm_full_tr_after_sat            true
% 0.96/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 0.96/0.94  --bmc1_ucm_layered_model                none
% 0.96/0.94  --bmc1_ucm_max_lemma_size               10
% 0.96/0.94  
% 0.96/0.94  ------ AIG Options
% 0.96/0.94  
% 0.96/0.94  --aig_mode                              false
% 0.96/0.94  
% 0.96/0.94  ------ Instantiation Options
% 0.96/0.94  
% 0.96/0.94  --instantiation_flag                    true
% 0.96/0.94  --inst_sos_flag                         false
% 0.96/0.94  --inst_sos_phase                        true
% 0.96/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.96/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.96/0.94  --inst_lit_sel_side                     none
% 0.96/0.94  --inst_solver_per_active                1400
% 0.96/0.94  --inst_solver_calls_frac                1.
% 0.96/0.94  --inst_passive_queue_type               priority_queues
% 0.96/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.96/0.94  --inst_passive_queues_freq              [25;2]
% 0.96/0.94  --inst_dismatching                      true
% 0.96/0.94  --inst_eager_unprocessed_to_passive     true
% 0.96/0.94  --inst_prop_sim_given                   true
% 0.96/0.94  --inst_prop_sim_new                     false
% 0.96/0.94  --inst_subs_new                         false
% 0.96/0.94  --inst_eq_res_simp                      false
% 0.96/0.94  --inst_subs_given                       false
% 0.96/0.94  --inst_orphan_elimination               true
% 0.96/0.94  --inst_learning_loop_flag               true
% 0.96/0.94  --inst_learning_start                   3000
% 0.96/0.94  --inst_learning_factor                  2
% 0.96/0.94  --inst_start_prop_sim_after_learn       3
% 0.96/0.94  --inst_sel_renew                        solver
% 0.96/0.94  --inst_lit_activity_flag                true
% 0.96/0.94  --inst_restr_to_given                   false
% 0.96/0.94  --inst_activity_threshold               500
% 0.96/0.94  --inst_out_proof                        true
% 0.96/0.94  
% 0.96/0.94  ------ Resolution Options
% 0.96/0.94  
% 0.96/0.94  --resolution_flag                       false
% 0.96/0.94  --res_lit_sel                           adaptive
% 0.96/0.94  --res_lit_sel_side                      none
% 0.96/0.94  --res_ordering                          kbo
% 0.96/0.94  --res_to_prop_solver                    active
% 0.96/0.94  --res_prop_simpl_new                    false
% 0.96/0.94  --res_prop_simpl_given                  true
% 0.96/0.94  --res_passive_queue_type                priority_queues
% 0.96/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.96/0.94  --res_passive_queues_freq               [15;5]
% 0.96/0.94  --res_forward_subs                      full
% 0.96/0.94  --res_backward_subs                     full
% 0.96/0.94  --res_forward_subs_resolution           true
% 0.96/0.94  --res_backward_subs_resolution          true
% 0.96/0.94  --res_orphan_elimination                true
% 0.96/0.94  --res_time_limit                        2.
% 0.96/0.94  --res_out_proof                         true
% 0.96/0.94  
% 0.96/0.94  ------ Superposition Options
% 0.96/0.94  
% 0.96/0.94  --superposition_flag                    true
% 0.96/0.94  --sup_passive_queue_type                priority_queues
% 0.96/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.96/0.94  --sup_passive_queues_freq               [8;1;4]
% 0.96/0.94  --demod_completeness_check              fast
% 0.96/0.94  --demod_use_ground                      true
% 0.96/0.94  --sup_to_prop_solver                    passive
% 0.96/0.94  --sup_prop_simpl_new                    true
% 0.96/0.94  --sup_prop_simpl_given                  true
% 0.96/0.94  --sup_fun_splitting                     false
% 0.96/0.94  --sup_smt_interval                      50000
% 0.96/0.94  
% 0.96/0.94  ------ Superposition Simplification Setup
% 0.96/0.94  
% 0.96/0.94  --sup_indices_passive                   []
% 0.96/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.96/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 0.96/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.94  --sup_full_bw                           [BwDemod]
% 0.96/0.94  --sup_immed_triv                        [TrivRules]
% 0.96/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.96/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.94  --sup_immed_bw_main                     []
% 0.96/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 0.96/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.96/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.96/0.94  
% 0.96/0.94  ------ Combination Options
% 0.96/0.94  
% 0.96/0.94  --comb_res_mult                         3
% 0.96/0.94  --comb_sup_mult                         2
% 0.96/0.94  --comb_inst_mult                        10
% 0.96/0.94  
% 0.96/0.94  ------ Debug Options
% 0.96/0.94  
% 0.96/0.94  --dbg_backtrace                         false
% 0.96/0.94  --dbg_dump_prop_clauses                 false
% 0.96/0.94  --dbg_dump_prop_clauses_file            -
% 0.96/0.94  --dbg_out_stat                          false
% 0.96/0.94  
% 0.96/0.94  
% 0.96/0.94  
% 0.96/0.94  
% 0.96/0.94  ------ Proving...
% 0.96/0.94  
% 0.96/0.94  
% 0.96/0.94  % SZS status Theorem for theBenchmark.p
% 0.96/0.94  
% 0.96/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 0.96/0.94  
% 0.96/0.94  fof(f8,conjecture,(
% 0.96/0.94    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 0.96/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.94  
% 0.96/0.94  fof(f9,negated_conjecture,(
% 0.96/0.94    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 0.96/0.94    inference(negated_conjecture,[],[f8])).
% 0.96/0.94  
% 0.96/0.94  fof(f11,plain,(
% 0.96/0.94    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 0.96/0.94    inference(ennf_transformation,[],[f9])).
% 0.96/0.94  
% 0.96/0.94  fof(f17,plain,(
% 0.96/0.94    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK1 != sK2 & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1))),
% 0.96/0.94    introduced(choice_axiom,[])).
% 0.96/0.94  
% 0.96/0.94  fof(f18,plain,(
% 0.96/0.94    sK1 != sK2 & k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 0.96/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f11,f17])).
% 0.96/0.94  
% 0.96/0.94  fof(f33,plain,(
% 0.96/0.94    k2_xboole_0(k1_tarski(sK1),k1_tarski(sK2)) = k1_tarski(sK1)),
% 0.96/0.94    inference(cnf_transformation,[],[f18])).
% 0.96/0.94  
% 0.96/0.94  fof(f1,axiom,(
% 0.96/0.94    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.96/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.94  
% 0.96/0.94  fof(f19,plain,(
% 0.96/0.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.96/0.94    inference(cnf_transformation,[],[f1])).
% 0.96/0.94  
% 0.96/0.94  fof(f5,axiom,(
% 0.96/0.94    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.96/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.94  
% 0.96/0.94  fof(f30,plain,(
% 0.96/0.94    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.96/0.94    inference(cnf_transformation,[],[f5])).
% 0.96/0.94  
% 0.96/0.94  fof(f47,plain,(
% 0.96/0.94    k5_xboole_0(k2_tarski(sK1,sK1),k4_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK1,sK1))) = k2_tarski(sK1,sK1)),
% 0.96/0.94    inference(definition_unfolding,[],[f33,f19,f30,f30,f30])).
% 0.96/0.94  
% 0.96/0.94  fof(f2,axiom,(
% 0.96/0.94    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.96/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.94  
% 0.96/0.94  fof(f10,plain,(
% 0.96/0.94    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.96/0.94    inference(ennf_transformation,[],[f2])).
% 0.96/0.94  
% 0.96/0.94  fof(f12,plain,(
% 0.96/0.94    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.96/0.94    inference(nnf_transformation,[],[f10])).
% 0.96/0.94  
% 0.96/0.94  fof(f13,plain,(
% 0.96/0.94    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.96/0.94    inference(flattening,[],[f12])).
% 0.96/0.94  
% 0.96/0.94  fof(f14,plain,(
% 0.96/0.94    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.96/0.94    inference(rectify,[],[f13])).
% 0.96/0.94  
% 0.96/0.94  fof(f15,plain,(
% 0.96/0.94    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 0.96/0.94    introduced(choice_axiom,[])).
% 0.96/0.94  
% 0.96/0.94  fof(f16,plain,(
% 0.96/0.94    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.96/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 0.96/0.94  
% 0.96/0.94  fof(f22,plain,(
% 0.96/0.94    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.96/0.94    inference(cnf_transformation,[],[f16])).
% 0.96/0.94  
% 0.96/0.94  fof(f3,axiom,(
% 0.96/0.94    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 0.96/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.94  
% 0.96/0.94  fof(f28,plain,(
% 0.96/0.94    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 0.96/0.94    inference(cnf_transformation,[],[f3])).
% 0.96/0.94  
% 0.96/0.94  fof(f35,plain,(
% 0.96/0.94    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = k1_enumset1(X0,X1,X2)) )),
% 0.96/0.94    inference(definition_unfolding,[],[f28,f19,f30])).
% 0.96/0.94  
% 0.96/0.94  fof(f43,plain,(
% 0.96/0.94    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X1 != X5 | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) != X3) )),
% 0.96/0.94    inference(definition_unfolding,[],[f22,f35])).
% 0.96/0.94  
% 0.96/0.94  fof(f50,plain,(
% 0.96/0.94    ( ! [X2,X0,X5,X3] : (r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0))) != X3) )),
% 0.96/0.94    inference(equality_resolution,[],[f43])).
% 0.96/0.94  
% 0.96/0.94  fof(f51,plain,(
% 0.96/0.94    ( ! [X2,X0,X5] : (r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X5,X2),k2_tarski(X0,X0))))) )),
% 0.96/0.94    inference(equality_resolution,[],[f50])).
% 0.96/0.94  
% 0.96/0.94  fof(f6,axiom,(
% 0.96/0.94    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.96/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.96/0.94  
% 0.96/0.94  fof(f31,plain,(
% 0.96/0.94    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.96/0.94    inference(cnf_transformation,[],[f6])).
% 0.96/0.94  
% 0.96/0.94  fof(f37,plain,(
% 0.96/0.94    ( ! [X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))) = k2_tarski(X0,X1)) )),
% 0.96/0.94    inference(definition_unfolding,[],[f31,f35])).
% 0.96/0.94  
% 0.96/0.94  fof(f20,plain,(
% 0.96/0.94    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.96/0.94    inference(cnf_transformation,[],[f16])).
% 0.96/0.94  
% 0.96/0.94  fof(f45,plain,(
% 0.96/0.94    ( ! [X2,X0,X5,X3,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) != X3) )),
% 0.96/0.94    inference(definition_unfolding,[],[f20,f35])).
% 0.96/0.94  
% 0.96/0.94  fof(f54,plain,(
% 0.96/0.94    ( ! [X2,X0,X5,X1] : (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) )),
% 0.96/0.94    inference(equality_resolution,[],[f45])).
% 0.96/0.94  
% 0.96/0.94  fof(f21,plain,(
% 0.96/0.94    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.96/0.94    inference(cnf_transformation,[],[f16])).
% 0.96/0.94  
% 0.96/0.94  fof(f44,plain,(
% 0.96/0.94    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) != X3) )),
% 0.96/0.94    inference(definition_unfolding,[],[f21,f35])).
% 0.96/0.94  
% 0.96/0.94  fof(f52,plain,(
% 0.96/0.94    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X5,X5),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5))) != X3) )),
% 0.96/0.94    inference(equality_resolution,[],[f44])).
% 0.96/0.94  
% 0.96/0.94  fof(f53,plain,(
% 0.96/0.94    ( ! [X2,X5,X1] : (r2_hidden(X5,k5_xboole_0(k2_tarski(X5,X5),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X5,X5))))) )),
% 0.96/0.94    inference(equality_resolution,[],[f52])).
% 0.96/0.94  
% 0.96/0.94  fof(f34,plain,(
% 0.96/0.94    sK1 != sK2),
% 0.96/0.94    inference(cnf_transformation,[],[f18])).
% 0.96/0.94  
% 0.96/0.94  cnf(c_11,negated_conjecture,
% 0.96/0.94      ( k5_xboole_0(k2_tarski(sK1,sK1),k4_xboole_0(k2_tarski(sK2,sK2),k2_tarski(sK1,sK1))) = k2_tarski(sK1,sK1) ),
% 0.96/0.94      inference(cnf_transformation,[],[f47]) ).
% 0.96/0.94  
% 0.96/0.94  cnf(c_6,plain,
% 0.96/0.94      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X1)))) ),
% 0.96/0.94      inference(cnf_transformation,[],[f51]) ).
% 0.96/0.94  
% 0.96/0.94  cnf(c_451,plain,
% 0.96/0.94      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X1)))) = iProver_top ),
% 0.96/0.94      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 0.96/0.94  
% 0.96/0.94  cnf(c_694,plain,
% 0.96/0.94      ( r2_hidden(sK2,k2_tarski(sK1,sK1)) = iProver_top ),
% 0.96/0.94      inference(superposition,[status(thm)],[c_11,c_451]) ).
% 0.96/0.94  
% 0.96/0.94  cnf(c_0,plain,
% 0.96/0.94      ( k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X1),k2_tarski(X0,X0))) = k2_tarski(X0,X1) ),
% 0.96/0.94      inference(cnf_transformation,[],[f37]) ).
% 0.96/0.94  
% 0.96/0.94  cnf(c_8,plain,
% 0.96/0.94      ( ~ r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1))))
% 0.96/0.94      | X0 = X1
% 0.96/0.94      | X0 = X2
% 0.96/0.94      | X0 = X3 ),
% 0.96/0.94      inference(cnf_transformation,[],[f54]) ).
% 0.96/0.94  
% 0.96/0.94  cnf(c_449,plain,
% 0.96/0.94      ( X0 = X1
% 0.96/0.94      | X0 = X2
% 0.96/0.94      | X0 = X3
% 0.96/0.94      | r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X1,X1)))) != iProver_top ),
% 0.96/0.94      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 0.96/0.94  
% 0.96/0.94  cnf(c_975,plain,
% 0.96/0.94      ( X0 = X1
% 0.96/0.94      | X2 = X1
% 0.96/0.94      | r2_hidden(X1,k2_tarski(X2,X0)) != iProver_top ),
% 0.96/0.94      inference(superposition,[status(thm)],[c_0,c_449]) ).
% 0.96/0.94  
% 0.96/0.94  cnf(c_1227,plain,
% 0.96/0.94      ( sK2 = sK1 ),
% 0.96/0.94      inference(superposition,[status(thm)],[c_694,c_975]) ).
% 0.96/0.94  
% 0.96/0.94  cnf(c_313,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.96/0.94  
% 0.96/0.94  cnf(c_524,plain,
% 0.96/0.94      ( sK2 != X0 | sK1 != X0 | sK1 = sK2 ),
% 0.96/0.94      inference(instantiation,[status(thm)],[c_313]) ).
% 0.96/0.94  
% 0.96/0.94  cnf(c_525,plain,
% 0.96/0.94      ( sK2 != sK1 | sK1 = sK2 | sK1 != sK1 ),
% 0.96/0.94      inference(instantiation,[status(thm)],[c_524]) ).
% 0.96/0.94  
% 0.96/0.94  cnf(c_7,plain,
% 0.96/0.94      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) ),
% 0.96/0.94      inference(cnf_transformation,[],[f53]) ).
% 0.96/0.94  
% 0.96/0.94  cnf(c_17,plain,
% 0.96/0.94      ( r2_hidden(sK1,k5_xboole_0(k2_tarski(sK1,sK1),k4_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)))) ),
% 0.96/0.94      inference(instantiation,[status(thm)],[c_7]) ).
% 0.96/0.94  
% 0.96/0.94  cnf(c_14,plain,
% 0.96/0.94      ( ~ r2_hidden(sK1,k5_xboole_0(k2_tarski(sK1,sK1),k4_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1))))
% 0.96/0.94      | sK1 = sK1 ),
% 0.96/0.94      inference(instantiation,[status(thm)],[c_8]) ).
% 0.96/0.94  
% 0.96/0.94  cnf(c_10,negated_conjecture,
% 0.96/0.94      ( sK1 != sK2 ),
% 0.96/0.94      inference(cnf_transformation,[],[f34]) ).
% 0.96/0.94  
% 0.96/0.94  cnf(contradiction,plain,
% 0.96/0.94      ( $false ),
% 0.96/0.94      inference(minisat,[status(thm)],[c_1227,c_525,c_17,c_14,c_10]) ).
% 0.96/0.94  
% 0.96/0.94  
% 0.96/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 0.96/0.94  
% 0.96/0.94  ------                               Statistics
% 0.96/0.94  
% 0.96/0.94  ------ General
% 0.96/0.94  
% 0.96/0.94  abstr_ref_over_cycles:                  0
% 0.96/0.94  abstr_ref_under_cycles:                 0
% 0.96/0.94  gc_basic_clause_elim:                   0
% 0.96/0.94  forced_gc_time:                         0
% 0.96/0.94  parsing_time:                           0.009
% 0.96/0.94  unif_index_cands_time:                  0.
% 0.96/0.94  unif_index_add_time:                    0.
% 0.96/0.94  orderings_time:                         0.
% 0.96/0.94  out_proof_time:                         0.007
% 0.96/0.94  total_time:                             0.082
% 0.96/0.94  num_of_symbols:                         38
% 0.96/0.94  num_of_terms:                           2206
% 0.96/0.94  
% 0.96/0.94  ------ Preprocessing
% 0.96/0.94  
% 0.96/0.94  num_of_splits:                          0
% 0.96/0.94  num_of_split_atoms:                     0
% 0.96/0.94  num_of_reused_defs:                     0
% 0.96/0.94  num_eq_ax_congr_red:                    8
% 0.96/0.94  num_of_sem_filtered_clauses:            1
% 0.96/0.94  num_of_subtypes:                        0
% 0.96/0.94  monotx_restored_types:                  0
% 0.96/0.94  sat_num_of_epr_types:                   0
% 0.96/0.94  sat_num_of_non_cyclic_types:            0
% 0.96/0.94  sat_guarded_non_collapsed_types:        0
% 0.96/0.94  num_pure_diseq_elim:                    0
% 0.96/0.94  simp_replaced_by:                       0
% 0.96/0.94  res_preprocessed:                       49
% 0.96/0.94  prep_upred:                             0
% 0.96/0.94  prep_unflattend:                        14
% 0.96/0.94  smt_new_axioms:                         0
% 0.96/0.94  pred_elim_cands:                        1
% 0.96/0.94  pred_elim:                              0
% 0.96/0.94  pred_elim_cl:                           0
% 0.96/0.94  pred_elim_cycles:                       1
% 0.96/0.94  merged_defs:                            0
% 0.96/0.94  merged_defs_ncl:                        0
% 0.96/0.94  bin_hyper_res:                          0
% 0.96/0.94  prep_cycles:                            3
% 0.96/0.94  pred_elim_time:                         0.004
% 0.96/0.94  splitting_time:                         0.
% 0.96/0.94  sem_filter_time:                        0.
% 0.96/0.94  monotx_time:                            0.
% 0.96/0.94  subtype_inf_time:                       0.
% 0.96/0.94  
% 0.96/0.94  ------ Problem properties
% 0.96/0.94  
% 0.96/0.94  clauses:                                12
% 0.96/0.94  conjectures:                            2
% 0.96/0.94  epr:                                    1
% 0.96/0.94  horn:                                   10
% 0.96/0.94  ground:                                 2
% 0.96/0.94  unary:                                  7
% 0.96/0.94  binary:                                 0
% 0.96/0.94  lits:                                   25
% 0.96/0.94  lits_eq:                                17
% 0.96/0.94  fd_pure:                                0
% 0.96/0.94  fd_pseudo:                              0
% 0.96/0.94  fd_cond:                                0
% 0.96/0.94  fd_pseudo_cond:                         4
% 0.96/0.94  ac_symbols:                             0
% 0.96/0.94  
% 0.96/0.94  ------ Propositional Solver
% 0.96/0.94  
% 0.96/0.94  prop_solver_calls:                      22
% 0.96/0.94  prop_fast_solver_calls:                 283
% 0.96/0.94  smt_solver_calls:                       0
% 0.96/0.94  smt_fast_solver_calls:                  0
% 0.96/0.94  prop_num_of_clauses:                    400
% 0.96/0.94  prop_preprocess_simplified:             2160
% 0.96/0.94  prop_fo_subsumed:                       0
% 0.96/0.94  prop_solver_time:                       0.
% 0.96/0.94  smt_solver_time:                        0.
% 0.96/0.94  smt_fast_solver_time:                   0.
% 0.96/0.94  prop_fast_solver_time:                  0.
% 0.96/0.94  prop_unsat_core_time:                   0.
% 0.96/0.94  
% 0.96/0.94  ------ QBF
% 0.96/0.94  
% 0.96/0.94  qbf_q_res:                              0
% 0.96/0.94  qbf_num_tautologies:                    0
% 0.96/0.94  qbf_prep_cycles:                        0
% 0.96/0.94  
% 0.96/0.94  ------ BMC1
% 0.96/0.94  
% 0.96/0.94  bmc1_current_bound:                     -1
% 0.96/0.94  bmc1_last_solved_bound:                 -1
% 0.96/0.94  bmc1_unsat_core_size:                   -1
% 0.96/0.94  bmc1_unsat_core_parents_size:           -1
% 0.96/0.94  bmc1_merge_next_fun:                    0
% 0.96/0.94  bmc1_unsat_core_clauses_time:           0.
% 0.96/0.94  
% 0.96/0.94  ------ Instantiation
% 0.96/0.94  
% 0.96/0.94  inst_num_of_clauses:                    162
% 0.96/0.94  inst_num_in_passive:                    103
% 0.96/0.94  inst_num_in_active:                     59
% 0.96/0.94  inst_num_in_unprocessed:                0
% 0.96/0.94  inst_num_of_loops:                      60
% 0.96/0.94  inst_num_of_learning_restarts:          0
% 0.96/0.94  inst_num_moves_active_passive:          0
% 0.96/0.94  inst_lit_activity:                      0
% 0.96/0.94  inst_lit_activity_moves:                0
% 0.96/0.94  inst_num_tautologies:                   0
% 0.96/0.94  inst_num_prop_implied:                  0
% 0.96/0.94  inst_num_existing_simplified:           0
% 0.96/0.94  inst_num_eq_res_simplified:             0
% 0.96/0.94  inst_num_child_elim:                    0
% 0.96/0.94  inst_num_of_dismatching_blockings:      32
% 0.96/0.94  inst_num_of_non_proper_insts:           118
% 0.96/0.94  inst_num_of_duplicates:                 0
% 0.96/0.94  inst_inst_num_from_inst_to_res:         0
% 0.96/0.94  inst_dismatching_checking_time:         0.
% 0.96/0.94  
% 0.96/0.94  ------ Resolution
% 0.96/0.94  
% 0.96/0.94  res_num_of_clauses:                     0
% 0.96/0.94  res_num_in_passive:                     0
% 0.96/0.94  res_num_in_active:                      0
% 0.96/0.94  res_num_of_loops:                       52
% 0.96/0.94  res_forward_subset_subsumed:            13
% 0.96/0.94  res_backward_subset_subsumed:           0
% 0.96/0.94  res_forward_subsumed:                   0
% 0.96/0.94  res_backward_subsumed:                  0
% 0.96/0.94  res_forward_subsumption_resolution:     0
% 0.96/0.94  res_backward_subsumption_resolution:    0
% 0.96/0.94  res_clause_to_clause_subsumption:       56
% 0.96/0.94  res_orphan_elimination:                 0
% 0.96/0.94  res_tautology_del:                      10
% 0.96/0.94  res_num_eq_res_simplified:              0
% 0.96/0.94  res_num_sel_changes:                    0
% 0.96/0.94  res_moves_from_active_to_pass:          0
% 0.96/0.94  
% 0.96/0.94  ------ Superposition
% 0.96/0.94  
% 0.96/0.94  sup_time_total:                         0.
% 0.96/0.94  sup_time_generating:                    0.
% 0.96/0.94  sup_time_sim_full:                      0.
% 0.96/0.94  sup_time_sim_immed:                     0.
% 0.96/0.94  
% 0.96/0.94  sup_num_of_clauses:                     18
% 0.96/0.94  sup_num_in_active:                      12
% 0.96/0.94  sup_num_in_passive:                     6
% 0.96/0.94  sup_num_of_loops:                       11
% 0.96/0.94  sup_fw_superposition:                   15
% 0.96/0.94  sup_bw_superposition:                   0
% 0.96/0.94  sup_immediate_simplified:               2
% 0.96/0.94  sup_given_eliminated:                   0
% 0.96/0.94  comparisons_done:                       0
% 0.96/0.94  comparisons_avoided:                    0
% 0.96/0.94  
% 0.96/0.94  ------ Simplifications
% 0.96/0.94  
% 0.96/0.94  
% 0.96/0.94  sim_fw_subset_subsumed:                 0
% 0.96/0.94  sim_bw_subset_subsumed:                 0
% 0.96/0.94  sim_fw_subsumed:                        1
% 0.96/0.94  sim_bw_subsumed:                        1
% 0.96/0.94  sim_fw_subsumption_res:                 0
% 0.96/0.94  sim_bw_subsumption_res:                 0
% 0.96/0.94  sim_tautology_del:                      0
% 0.96/0.94  sim_eq_tautology_del:                   3
% 0.96/0.94  sim_eq_res_simp:                        0
% 0.96/0.94  sim_fw_demodulated:                     0
% 0.96/0.94  sim_bw_demodulated:                     0
% 0.96/0.94  sim_light_normalised:                   1
% 0.96/0.94  sim_joinable_taut:                      0
% 0.96/0.94  sim_joinable_simp:                      0
% 0.96/0.94  sim_ac_normalised:                      0
% 0.96/0.94  sim_smt_subsumption:                    0
% 0.96/0.94  
%------------------------------------------------------------------------------
