%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:29:24 EST 2020

% Result     : Theorem 0.98s
% Output     : CNFRefutation 0.98s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 111 expanded)
%              Number of clauses        :   19 (  21 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :  220 ( 356 expanded)
%              Number of equality atoms :  163 ( 261 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = k1_enumset1(X0,X1,X2) ),
    inference(definition_unfolding,[],[f36,f23,f37])).

fof(f56,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = k2_enumset1(X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f42])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f21,plain,
    ( ? [X0,X1] :
        ( X0 != X1
        & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) )
   => ( sK2 != sK3
      & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( sK2 != sK3
    & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f11,f21])).

fof(f40,plain,(
    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    k5_xboole_0(k2_tarski(sK2,sK2),k4_xboole_0(k2_tarski(sK3,sK3),k2_tarski(sK2,sK2))) = k2_tarski(sK2,sK2) ),
    inference(definition_unfolding,[],[f40,f23,f37,f37,f37])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f27,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) != X3 ) ),
    inference(definition_unfolding,[],[f27,f42])).

fof(f58,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0))) != X3 ) ),
    inference(equality_resolution,[],[f48])).

fof(f59,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0)))) ),
    inference(equality_resolution,[],[f58])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f17])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK1(X0,X1) != X0
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( sK1(X0,X1) = X0
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK1(X0,X1) != X0
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( sK1(X0,X1) = X0
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).

fof(f32,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f32,f37])).

fof(f67,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k2_tarski(X0,X0)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f33,f37])).

fof(f65,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f54])).

fof(f66,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f65])).

fof(f41,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f22])).

cnf(c_13,plain,
    ( k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_15,negated_conjecture,
    ( k5_xboole_0(k2_tarski(sK2,sK2),k4_xboole_0(k2_tarski(sK3,sK3),k2_tarski(sK2,sK2))) = k2_tarski(sK2,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1448,plain,
    ( k2_enumset1(sK2,sK2,sK3,sK3) = k2_tarski(sK2,sK2) ),
    inference(superposition,[status(thm)],[c_13,c_15])).

cnf(c_5,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X1)))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_881,plain,
    ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_906,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_13,c_881])).

cnf(c_1570,plain,
    ( r2_hidden(sK3,k2_tarski(sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1448,c_906])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_tarski(X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1030,plain,
    ( ~ r2_hidden(sK3,k2_tarski(X0,X0))
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1031,plain,
    ( sK3 = X0
    | r2_hidden(sK3,k2_tarski(X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1030])).

cnf(c_1033,plain,
    ( sK3 = sK2
    | r2_hidden(sK3,k2_tarski(sK2,sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_680,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1002,plain,
    ( sK3 != X0
    | sK2 != X0
    | sK2 = sK3 ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_1003,plain,
    ( sK3 != sK2
    | sK2 = sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_11,plain,
    ( r2_hidden(X0,k2_tarski(X0,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_21,plain,
    ( r2_hidden(sK2,k2_tarski(sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_18,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK2,sK2))
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_14,negated_conjecture,
    ( sK2 != sK3 ),
    inference(cnf_transformation,[],[f41])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1570,c_1033,c_1003,c_21,c_18,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:40:40 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 0.98/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.98/0.97  
% 0.98/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.98/0.97  
% 0.98/0.97  ------  iProver source info
% 0.98/0.97  
% 0.98/0.97  git: date: 2020-06-30 10:37:57 +0100
% 0.98/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.98/0.97  git: non_committed_changes: false
% 0.98/0.97  git: last_make_outside_of_git: false
% 0.98/0.97  
% 0.98/0.97  ------ 
% 0.98/0.97  
% 0.98/0.97  ------ Input Options
% 0.98/0.97  
% 0.98/0.97  --out_options                           all
% 0.98/0.97  --tptp_safe_out                         true
% 0.98/0.97  --problem_path                          ""
% 0.98/0.97  --include_path                          ""
% 0.98/0.97  --clausifier                            res/vclausify_rel
% 0.98/0.97  --clausifier_options                    --mode clausify
% 0.98/0.97  --stdin                                 false
% 0.98/0.97  --stats_out                             all
% 0.98/0.97  
% 0.98/0.97  ------ General Options
% 0.98/0.97  
% 0.98/0.97  --fof                                   false
% 0.98/0.97  --time_out_real                         305.
% 0.98/0.97  --time_out_virtual                      -1.
% 0.98/0.97  --symbol_type_check                     false
% 0.98/0.97  --clausify_out                          false
% 0.98/0.97  --sig_cnt_out                           false
% 0.98/0.97  --trig_cnt_out                          false
% 0.98/0.97  --trig_cnt_out_tolerance                1.
% 0.98/0.97  --trig_cnt_out_sk_spl                   false
% 0.98/0.97  --abstr_cl_out                          false
% 0.98/0.97  
% 0.98/0.97  ------ Global Options
% 0.98/0.97  
% 0.98/0.97  --schedule                              default
% 0.98/0.97  --add_important_lit                     false
% 0.98/0.97  --prop_solver_per_cl                    1000
% 0.98/0.97  --min_unsat_core                        false
% 0.98/0.97  --soft_assumptions                      false
% 0.98/0.97  --soft_lemma_size                       3
% 0.98/0.97  --prop_impl_unit_size                   0
% 0.98/0.97  --prop_impl_unit                        []
% 0.98/0.97  --share_sel_clauses                     true
% 0.98/0.97  --reset_solvers                         false
% 0.98/0.97  --bc_imp_inh                            [conj_cone]
% 0.98/0.97  --conj_cone_tolerance                   3.
% 0.98/0.97  --extra_neg_conj                        none
% 0.98/0.97  --large_theory_mode                     true
% 0.98/0.97  --prolific_symb_bound                   200
% 0.98/0.97  --lt_threshold                          2000
% 0.98/0.97  --clause_weak_htbl                      true
% 0.98/0.97  --gc_record_bc_elim                     false
% 0.98/0.97  
% 0.98/0.97  ------ Preprocessing Options
% 0.98/0.97  
% 0.98/0.97  --preprocessing_flag                    true
% 0.98/0.97  --time_out_prep_mult                    0.1
% 0.98/0.97  --splitting_mode                        input
% 0.98/0.97  --splitting_grd                         true
% 0.98/0.97  --splitting_cvd                         false
% 0.98/0.97  --splitting_cvd_svl                     false
% 0.98/0.97  --splitting_nvd                         32
% 0.98/0.97  --sub_typing                            true
% 0.98/0.97  --prep_gs_sim                           true
% 0.98/0.97  --prep_unflatten                        true
% 0.98/0.97  --prep_res_sim                          true
% 0.98/0.97  --prep_upred                            true
% 0.98/0.97  --prep_sem_filter                       exhaustive
% 0.98/0.97  --prep_sem_filter_out                   false
% 0.98/0.97  --pred_elim                             true
% 0.98/0.97  --res_sim_input                         true
% 0.98/0.97  --eq_ax_congr_red                       true
% 0.98/0.97  --pure_diseq_elim                       true
% 0.98/0.97  --brand_transform                       false
% 0.98/0.97  --non_eq_to_eq                          false
% 0.98/0.97  --prep_def_merge                        true
% 0.98/0.97  --prep_def_merge_prop_impl              false
% 0.98/0.97  --prep_def_merge_mbd                    true
% 0.98/0.97  --prep_def_merge_tr_red                 false
% 0.98/0.97  --prep_def_merge_tr_cl                  false
% 0.98/0.97  --smt_preprocessing                     true
% 0.98/0.97  --smt_ac_axioms                         fast
% 0.98/0.97  --preprocessed_out                      false
% 0.98/0.97  --preprocessed_stats                    false
% 0.98/0.97  
% 0.98/0.97  ------ Abstraction refinement Options
% 0.98/0.97  
% 0.98/0.97  --abstr_ref                             []
% 0.98/0.97  --abstr_ref_prep                        false
% 0.98/0.97  --abstr_ref_until_sat                   false
% 0.98/0.97  --abstr_ref_sig_restrict                funpre
% 0.98/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 0.98/0.97  --abstr_ref_under                       []
% 0.98/0.97  
% 0.98/0.97  ------ SAT Options
% 0.98/0.97  
% 0.98/0.97  --sat_mode                              false
% 0.98/0.97  --sat_fm_restart_options                ""
% 0.98/0.97  --sat_gr_def                            false
% 0.98/0.97  --sat_epr_types                         true
% 0.98/0.97  --sat_non_cyclic_types                  false
% 0.98/0.97  --sat_finite_models                     false
% 0.98/0.97  --sat_fm_lemmas                         false
% 0.98/0.97  --sat_fm_prep                           false
% 0.98/0.97  --sat_fm_uc_incr                        true
% 0.98/0.97  --sat_out_model                         small
% 0.98/0.97  --sat_out_clauses                       false
% 0.98/0.97  
% 0.98/0.97  ------ QBF Options
% 0.98/0.97  
% 0.98/0.97  --qbf_mode                              false
% 0.98/0.97  --qbf_elim_univ                         false
% 0.98/0.97  --qbf_dom_inst                          none
% 0.98/0.97  --qbf_dom_pre_inst                      false
% 0.98/0.97  --qbf_sk_in                             false
% 0.98/0.97  --qbf_pred_elim                         true
% 0.98/0.97  --qbf_split                             512
% 0.98/0.97  
% 0.98/0.97  ------ BMC1 Options
% 0.98/0.97  
% 0.98/0.97  --bmc1_incremental                      false
% 0.98/0.97  --bmc1_axioms                           reachable_all
% 0.98/0.97  --bmc1_min_bound                        0
% 0.98/0.97  --bmc1_max_bound                        -1
% 0.98/0.97  --bmc1_max_bound_default                -1
% 0.98/0.97  --bmc1_symbol_reachability              true
% 0.98/0.97  --bmc1_property_lemmas                  false
% 0.98/0.97  --bmc1_k_induction                      false
% 0.98/0.97  --bmc1_non_equiv_states                 false
% 0.98/0.97  --bmc1_deadlock                         false
% 0.98/0.97  --bmc1_ucm                              false
% 0.98/0.97  --bmc1_add_unsat_core                   none
% 0.98/0.97  --bmc1_unsat_core_children              false
% 0.98/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 0.98/0.97  --bmc1_out_stat                         full
% 0.98/0.97  --bmc1_ground_init                      false
% 0.98/0.97  --bmc1_pre_inst_next_state              false
% 0.98/0.97  --bmc1_pre_inst_state                   false
% 0.98/0.97  --bmc1_pre_inst_reach_state             false
% 0.98/0.97  --bmc1_out_unsat_core                   false
% 0.98/0.97  --bmc1_aig_witness_out                  false
% 0.98/0.97  --bmc1_verbose                          false
% 0.98/0.97  --bmc1_dump_clauses_tptp                false
% 0.98/0.97  --bmc1_dump_unsat_core_tptp             false
% 0.98/0.97  --bmc1_dump_file                        -
% 0.98/0.97  --bmc1_ucm_expand_uc_limit              128
% 0.98/0.97  --bmc1_ucm_n_expand_iterations          6
% 0.98/0.97  --bmc1_ucm_extend_mode                  1
% 0.98/0.97  --bmc1_ucm_init_mode                    2
% 0.98/0.97  --bmc1_ucm_cone_mode                    none
% 0.98/0.97  --bmc1_ucm_reduced_relation_type        0
% 0.98/0.97  --bmc1_ucm_relax_model                  4
% 0.98/0.97  --bmc1_ucm_full_tr_after_sat            true
% 0.98/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 0.98/0.97  --bmc1_ucm_layered_model                none
% 0.98/0.97  --bmc1_ucm_max_lemma_size               10
% 0.98/0.97  
% 0.98/0.97  ------ AIG Options
% 0.98/0.97  
% 0.98/0.97  --aig_mode                              false
% 0.98/0.97  
% 0.98/0.97  ------ Instantiation Options
% 0.98/0.97  
% 0.98/0.97  --instantiation_flag                    true
% 0.98/0.97  --inst_sos_flag                         false
% 0.98/0.97  --inst_sos_phase                        true
% 0.98/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.98/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.98/0.97  --inst_lit_sel_side                     num_symb
% 0.98/0.97  --inst_solver_per_active                1400
% 0.98/0.97  --inst_solver_calls_frac                1.
% 0.98/0.97  --inst_passive_queue_type               priority_queues
% 0.98/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.98/0.97  --inst_passive_queues_freq              [25;2]
% 0.98/0.97  --inst_dismatching                      true
% 0.98/0.97  --inst_eager_unprocessed_to_passive     true
% 0.98/0.97  --inst_prop_sim_given                   true
% 0.98/0.97  --inst_prop_sim_new                     false
% 0.98/0.97  --inst_subs_new                         false
% 0.98/0.97  --inst_eq_res_simp                      false
% 0.98/0.97  --inst_subs_given                       false
% 0.98/0.97  --inst_orphan_elimination               true
% 0.98/0.97  --inst_learning_loop_flag               true
% 0.98/0.97  --inst_learning_start                   3000
% 0.98/0.97  --inst_learning_factor                  2
% 0.98/0.97  --inst_start_prop_sim_after_learn       3
% 0.98/0.97  --inst_sel_renew                        solver
% 0.98/0.97  --inst_lit_activity_flag                true
% 0.98/0.97  --inst_restr_to_given                   false
% 0.98/0.97  --inst_activity_threshold               500
% 0.98/0.97  --inst_out_proof                        true
% 0.98/0.97  
% 0.98/0.97  ------ Resolution Options
% 0.98/0.97  
% 0.98/0.97  --resolution_flag                       true
% 0.98/0.97  --res_lit_sel                           adaptive
% 0.98/0.97  --res_lit_sel_side                      none
% 0.98/0.97  --res_ordering                          kbo
% 0.98/0.97  --res_to_prop_solver                    active
% 0.98/0.97  --res_prop_simpl_new                    false
% 0.98/0.97  --res_prop_simpl_given                  true
% 0.98/0.97  --res_passive_queue_type                priority_queues
% 0.98/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.98/0.97  --res_passive_queues_freq               [15;5]
% 0.98/0.97  --res_forward_subs                      full
% 0.98/0.97  --res_backward_subs                     full
% 0.98/0.97  --res_forward_subs_resolution           true
% 0.98/0.97  --res_backward_subs_resolution          true
% 0.98/0.97  --res_orphan_elimination                true
% 0.98/0.97  --res_time_limit                        2.
% 0.98/0.97  --res_out_proof                         true
% 0.98/0.97  
% 0.98/0.97  ------ Superposition Options
% 0.98/0.97  
% 0.98/0.97  --superposition_flag                    true
% 0.98/0.97  --sup_passive_queue_type                priority_queues
% 0.98/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.98/0.97  --sup_passive_queues_freq               [8;1;4]
% 0.98/0.97  --demod_completeness_check              fast
% 0.98/0.97  --demod_use_ground                      true
% 0.98/0.97  --sup_to_prop_solver                    passive
% 0.98/0.97  --sup_prop_simpl_new                    true
% 0.98/0.97  --sup_prop_simpl_given                  true
% 0.98/0.97  --sup_fun_splitting                     false
% 0.98/0.97  --sup_smt_interval                      50000
% 0.98/0.97  
% 0.98/0.97  ------ Superposition Simplification Setup
% 0.98/0.97  
% 0.98/0.97  --sup_indices_passive                   []
% 0.98/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 0.98/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/0.97  --sup_full_bw                           [BwDemod]
% 0.98/0.97  --sup_immed_triv                        [TrivRules]
% 0.98/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.98/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/0.97  --sup_immed_bw_main                     []
% 0.98/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 0.98/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/0.97  
% 0.98/0.97  ------ Combination Options
% 0.98/0.97  
% 0.98/0.97  --comb_res_mult                         3
% 0.98/0.97  --comb_sup_mult                         2
% 0.98/0.97  --comb_inst_mult                        10
% 0.98/0.97  
% 0.98/0.97  ------ Debug Options
% 0.98/0.97  
% 0.98/0.97  --dbg_backtrace                         false
% 0.98/0.97  --dbg_dump_prop_clauses                 false
% 0.98/0.97  --dbg_dump_prop_clauses_file            -
% 0.98/0.97  --dbg_out_stat                          false
% 0.98/0.97  ------ Parsing...
% 0.98/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.98/0.97  
% 0.98/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 0.98/0.97  
% 0.98/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.98/0.97  
% 0.98/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.98/0.97  ------ Proving...
% 0.98/0.97  ------ Problem Properties 
% 0.98/0.97  
% 0.98/0.97  
% 0.98/0.97  clauses                                 16
% 0.98/0.97  conjectures                             2
% 0.98/0.97  EPR                                     1
% 0.98/0.97  Horn                                    13
% 0.98/0.97  unary                                   8
% 0.98/0.97  binary                                  1
% 0.98/0.97  lits                                    34
% 0.98/0.97  lits eq                                 22
% 0.98/0.97  fd_pure                                 0
% 0.98/0.97  fd_pseudo                               0
% 0.98/0.97  fd_cond                                 0
% 0.98/0.97  fd_pseudo_cond                          6
% 0.98/0.97  AC symbols                              0
% 0.98/0.97  
% 0.98/0.97  ------ Schedule dynamic 5 is on 
% 0.98/0.97  
% 0.98/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.98/0.97  
% 0.98/0.97  
% 0.98/0.97  ------ 
% 0.98/0.97  Current options:
% 0.98/0.97  ------ 
% 0.98/0.97  
% 0.98/0.97  ------ Input Options
% 0.98/0.97  
% 0.98/0.97  --out_options                           all
% 0.98/0.97  --tptp_safe_out                         true
% 0.98/0.97  --problem_path                          ""
% 0.98/0.97  --include_path                          ""
% 0.98/0.97  --clausifier                            res/vclausify_rel
% 0.98/0.97  --clausifier_options                    --mode clausify
% 0.98/0.97  --stdin                                 false
% 0.98/0.97  --stats_out                             all
% 0.98/0.97  
% 0.98/0.97  ------ General Options
% 0.98/0.97  
% 0.98/0.97  --fof                                   false
% 0.98/0.97  --time_out_real                         305.
% 0.98/0.97  --time_out_virtual                      -1.
% 0.98/0.97  --symbol_type_check                     false
% 0.98/0.97  --clausify_out                          false
% 0.98/0.97  --sig_cnt_out                           false
% 0.98/0.97  --trig_cnt_out                          false
% 0.98/0.97  --trig_cnt_out_tolerance                1.
% 0.98/0.97  --trig_cnt_out_sk_spl                   false
% 0.98/0.97  --abstr_cl_out                          false
% 0.98/0.97  
% 0.98/0.97  ------ Global Options
% 0.98/0.97  
% 0.98/0.97  --schedule                              default
% 0.98/0.97  --add_important_lit                     false
% 0.98/0.97  --prop_solver_per_cl                    1000
% 0.98/0.97  --min_unsat_core                        false
% 0.98/0.97  --soft_assumptions                      false
% 0.98/0.97  --soft_lemma_size                       3
% 0.98/0.97  --prop_impl_unit_size                   0
% 0.98/0.97  --prop_impl_unit                        []
% 0.98/0.97  --share_sel_clauses                     true
% 0.98/0.97  --reset_solvers                         false
% 0.98/0.97  --bc_imp_inh                            [conj_cone]
% 0.98/0.97  --conj_cone_tolerance                   3.
% 0.98/0.97  --extra_neg_conj                        none
% 0.98/0.97  --large_theory_mode                     true
% 0.98/0.97  --prolific_symb_bound                   200
% 0.98/0.97  --lt_threshold                          2000
% 0.98/0.97  --clause_weak_htbl                      true
% 0.98/0.97  --gc_record_bc_elim                     false
% 0.98/0.97  
% 0.98/0.97  ------ Preprocessing Options
% 0.98/0.97  
% 0.98/0.97  --preprocessing_flag                    true
% 0.98/0.97  --time_out_prep_mult                    0.1
% 0.98/0.97  --splitting_mode                        input
% 0.98/0.97  --splitting_grd                         true
% 0.98/0.97  --splitting_cvd                         false
% 0.98/0.97  --splitting_cvd_svl                     false
% 0.98/0.97  --splitting_nvd                         32
% 0.98/0.97  --sub_typing                            true
% 0.98/0.97  --prep_gs_sim                           true
% 0.98/0.97  --prep_unflatten                        true
% 0.98/0.97  --prep_res_sim                          true
% 0.98/0.97  --prep_upred                            true
% 0.98/0.97  --prep_sem_filter                       exhaustive
% 0.98/0.97  --prep_sem_filter_out                   false
% 0.98/0.97  --pred_elim                             true
% 0.98/0.97  --res_sim_input                         true
% 0.98/0.97  --eq_ax_congr_red                       true
% 0.98/0.97  --pure_diseq_elim                       true
% 0.98/0.97  --brand_transform                       false
% 0.98/0.97  --non_eq_to_eq                          false
% 0.98/0.97  --prep_def_merge                        true
% 0.98/0.97  --prep_def_merge_prop_impl              false
% 0.98/0.97  --prep_def_merge_mbd                    true
% 0.98/0.97  --prep_def_merge_tr_red                 false
% 0.98/0.97  --prep_def_merge_tr_cl                  false
% 0.98/0.97  --smt_preprocessing                     true
% 0.98/0.97  --smt_ac_axioms                         fast
% 0.98/0.97  --preprocessed_out                      false
% 0.98/0.97  --preprocessed_stats                    false
% 0.98/0.97  
% 0.98/0.97  ------ Abstraction refinement Options
% 0.98/0.97  
% 0.98/0.97  --abstr_ref                             []
% 0.98/0.97  --abstr_ref_prep                        false
% 0.98/0.97  --abstr_ref_until_sat                   false
% 0.98/0.97  --abstr_ref_sig_restrict                funpre
% 0.98/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 0.98/0.97  --abstr_ref_under                       []
% 0.98/0.97  
% 0.98/0.97  ------ SAT Options
% 0.98/0.97  
% 0.98/0.97  --sat_mode                              false
% 0.98/0.97  --sat_fm_restart_options                ""
% 0.98/0.97  --sat_gr_def                            false
% 0.98/0.97  --sat_epr_types                         true
% 0.98/0.97  --sat_non_cyclic_types                  false
% 0.98/0.97  --sat_finite_models                     false
% 0.98/0.97  --sat_fm_lemmas                         false
% 0.98/0.97  --sat_fm_prep                           false
% 0.98/0.97  --sat_fm_uc_incr                        true
% 0.98/0.97  --sat_out_model                         small
% 0.98/0.97  --sat_out_clauses                       false
% 0.98/0.97  
% 0.98/0.97  ------ QBF Options
% 0.98/0.97  
% 0.98/0.97  --qbf_mode                              false
% 0.98/0.97  --qbf_elim_univ                         false
% 0.98/0.97  --qbf_dom_inst                          none
% 0.98/0.97  --qbf_dom_pre_inst                      false
% 0.98/0.97  --qbf_sk_in                             false
% 0.98/0.97  --qbf_pred_elim                         true
% 0.98/0.97  --qbf_split                             512
% 0.98/0.97  
% 0.98/0.97  ------ BMC1 Options
% 0.98/0.97  
% 0.98/0.97  --bmc1_incremental                      false
% 0.98/0.97  --bmc1_axioms                           reachable_all
% 0.98/0.97  --bmc1_min_bound                        0
% 0.98/0.97  --bmc1_max_bound                        -1
% 0.98/0.97  --bmc1_max_bound_default                -1
% 0.98/0.97  --bmc1_symbol_reachability              true
% 0.98/0.97  --bmc1_property_lemmas                  false
% 0.98/0.97  --bmc1_k_induction                      false
% 0.98/0.97  --bmc1_non_equiv_states                 false
% 0.98/0.97  --bmc1_deadlock                         false
% 0.98/0.97  --bmc1_ucm                              false
% 0.98/0.97  --bmc1_add_unsat_core                   none
% 0.98/0.97  --bmc1_unsat_core_children              false
% 0.98/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 0.98/0.97  --bmc1_out_stat                         full
% 0.98/0.97  --bmc1_ground_init                      false
% 0.98/0.97  --bmc1_pre_inst_next_state              false
% 0.98/0.97  --bmc1_pre_inst_state                   false
% 0.98/0.97  --bmc1_pre_inst_reach_state             false
% 0.98/0.97  --bmc1_out_unsat_core                   false
% 0.98/0.97  --bmc1_aig_witness_out                  false
% 0.98/0.97  --bmc1_verbose                          false
% 0.98/0.97  --bmc1_dump_clauses_tptp                false
% 0.98/0.97  --bmc1_dump_unsat_core_tptp             false
% 0.98/0.97  --bmc1_dump_file                        -
% 0.98/0.97  --bmc1_ucm_expand_uc_limit              128
% 0.98/0.97  --bmc1_ucm_n_expand_iterations          6
% 0.98/0.97  --bmc1_ucm_extend_mode                  1
% 0.98/0.97  --bmc1_ucm_init_mode                    2
% 0.98/0.97  --bmc1_ucm_cone_mode                    none
% 0.98/0.97  --bmc1_ucm_reduced_relation_type        0
% 0.98/0.97  --bmc1_ucm_relax_model                  4
% 0.98/0.97  --bmc1_ucm_full_tr_after_sat            true
% 0.98/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 0.98/0.97  --bmc1_ucm_layered_model                none
% 0.98/0.97  --bmc1_ucm_max_lemma_size               10
% 0.98/0.97  
% 0.98/0.97  ------ AIG Options
% 0.98/0.97  
% 0.98/0.97  --aig_mode                              false
% 0.98/0.97  
% 0.98/0.97  ------ Instantiation Options
% 0.98/0.97  
% 0.98/0.97  --instantiation_flag                    true
% 0.98/0.97  --inst_sos_flag                         false
% 0.98/0.97  --inst_sos_phase                        true
% 0.98/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.98/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.98/0.97  --inst_lit_sel_side                     none
% 0.98/0.97  --inst_solver_per_active                1400
% 0.98/0.97  --inst_solver_calls_frac                1.
% 0.98/0.97  --inst_passive_queue_type               priority_queues
% 0.98/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.98/0.97  --inst_passive_queues_freq              [25;2]
% 0.98/0.97  --inst_dismatching                      true
% 0.98/0.97  --inst_eager_unprocessed_to_passive     true
% 0.98/0.97  --inst_prop_sim_given                   true
% 0.98/0.97  --inst_prop_sim_new                     false
% 0.98/0.97  --inst_subs_new                         false
% 0.98/0.97  --inst_eq_res_simp                      false
% 0.98/0.97  --inst_subs_given                       false
% 0.98/0.97  --inst_orphan_elimination               true
% 0.98/0.97  --inst_learning_loop_flag               true
% 0.98/0.97  --inst_learning_start                   3000
% 0.98/0.97  --inst_learning_factor                  2
% 0.98/0.97  --inst_start_prop_sim_after_learn       3
% 0.98/0.97  --inst_sel_renew                        solver
% 0.98/0.97  --inst_lit_activity_flag                true
% 0.98/0.97  --inst_restr_to_given                   false
% 0.98/0.97  --inst_activity_threshold               500
% 0.98/0.97  --inst_out_proof                        true
% 0.98/0.97  
% 0.98/0.97  ------ Resolution Options
% 0.98/0.97  
% 0.98/0.97  --resolution_flag                       false
% 0.98/0.97  --res_lit_sel                           adaptive
% 0.98/0.97  --res_lit_sel_side                      none
% 0.98/0.97  --res_ordering                          kbo
% 0.98/0.97  --res_to_prop_solver                    active
% 0.98/0.97  --res_prop_simpl_new                    false
% 0.98/0.97  --res_prop_simpl_given                  true
% 0.98/0.97  --res_passive_queue_type                priority_queues
% 0.98/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.98/0.97  --res_passive_queues_freq               [15;5]
% 0.98/0.97  --res_forward_subs                      full
% 0.98/0.97  --res_backward_subs                     full
% 0.98/0.97  --res_forward_subs_resolution           true
% 0.98/0.97  --res_backward_subs_resolution          true
% 0.98/0.97  --res_orphan_elimination                true
% 0.98/0.97  --res_time_limit                        2.
% 0.98/0.97  --res_out_proof                         true
% 0.98/0.97  
% 0.98/0.97  ------ Superposition Options
% 0.98/0.97  
% 0.98/0.97  --superposition_flag                    true
% 0.98/0.97  --sup_passive_queue_type                priority_queues
% 0.98/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.98/0.97  --sup_passive_queues_freq               [8;1;4]
% 0.98/0.97  --demod_completeness_check              fast
% 0.98/0.97  --demod_use_ground                      true
% 0.98/0.97  --sup_to_prop_solver                    passive
% 0.98/0.97  --sup_prop_simpl_new                    true
% 0.98/0.97  --sup_prop_simpl_given                  true
% 0.98/0.97  --sup_fun_splitting                     false
% 0.98/0.97  --sup_smt_interval                      50000
% 0.98/0.97  
% 0.98/0.97  ------ Superposition Simplification Setup
% 0.98/0.97  
% 0.98/0.97  --sup_indices_passive                   []
% 0.98/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.98/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 0.98/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/0.97  --sup_full_bw                           [BwDemod]
% 0.98/0.97  --sup_immed_triv                        [TrivRules]
% 0.98/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.98/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/0.98  --sup_immed_bw_main                     []
% 0.98/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 0.98/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.98/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.98/0.98  
% 0.98/0.98  ------ Combination Options
% 0.98/0.98  
% 0.98/0.98  --comb_res_mult                         3
% 0.98/0.98  --comb_sup_mult                         2
% 0.98/0.98  --comb_inst_mult                        10
% 0.98/0.98  
% 0.98/0.98  ------ Debug Options
% 0.98/0.98  
% 0.98/0.98  --dbg_backtrace                         false
% 0.98/0.98  --dbg_dump_prop_clauses                 false
% 0.98/0.98  --dbg_dump_prop_clauses_file            -
% 0.98/0.98  --dbg_out_stat                          false
% 0.98/0.98  
% 0.98/0.98  
% 0.98/0.98  
% 0.98/0.98  
% 0.98/0.98  ------ Proving...
% 0.98/0.98  
% 0.98/0.98  
% 0.98/0.98  % SZS status Theorem for theBenchmark.p
% 0.98/0.98  
% 0.98/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 0.98/0.98  
% 0.98/0.98  fof(f7,axiom,(
% 0.98/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.98/0.98  
% 0.98/0.98  fof(f39,plain,(
% 0.98/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.98/0.98    inference(cnf_transformation,[],[f7])).
% 0.98/0.98  
% 0.98/0.98  fof(f4,axiom,(
% 0.98/0.98    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)),
% 0.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.98/0.98  
% 0.98/0.98  fof(f36,plain,(
% 0.98/0.98    ( ! [X2,X0,X1] : (k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2)) )),
% 0.98/0.98    inference(cnf_transformation,[],[f4])).
% 0.98/0.98  
% 0.98/0.98  fof(f1,axiom,(
% 0.98/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.98/0.98  
% 0.98/0.98  fof(f23,plain,(
% 0.98/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.98/0.98    inference(cnf_transformation,[],[f1])).
% 0.98/0.98  
% 0.98/0.98  fof(f5,axiom,(
% 0.98/0.98    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.98/0.98  
% 0.98/0.98  fof(f37,plain,(
% 0.98/0.98    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.98/0.98    inference(cnf_transformation,[],[f5])).
% 0.98/0.98  
% 0.98/0.98  fof(f42,plain,(
% 0.98/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = k1_enumset1(X0,X1,X2)) )),
% 0.98/0.98    inference(definition_unfolding,[],[f36,f23,f37])).
% 0.98/0.98  
% 0.98/0.98  fof(f56,plain,(
% 0.98/0.98    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.98/0.98    inference(definition_unfolding,[],[f39,f42])).
% 0.98/0.98  
% 0.98/0.98  fof(f8,conjecture,(
% 0.98/0.98    ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 0.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.98/0.98  
% 0.98/0.98  fof(f9,negated_conjecture,(
% 0.98/0.98    ~! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) => X0 = X1)),
% 0.98/0.98    inference(negated_conjecture,[],[f8])).
% 0.98/0.98  
% 0.98/0.98  fof(f11,plain,(
% 0.98/0.98    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0))),
% 0.98/0.98    inference(ennf_transformation,[],[f9])).
% 0.98/0.98  
% 0.98/0.98  fof(f21,plain,(
% 0.98/0.98    ? [X0,X1] : (X0 != X1 & k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)) => (sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2))),
% 0.98/0.98    introduced(choice_axiom,[])).
% 0.98/0.98  
% 0.98/0.98  fof(f22,plain,(
% 0.98/0.98    sK2 != sK3 & k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 0.98/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f11,f21])).
% 0.98/0.98  
% 0.98/0.98  fof(f40,plain,(
% 0.98/0.98    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k1_tarski(sK2)),
% 0.98/0.98    inference(cnf_transformation,[],[f22])).
% 0.98/0.98  
% 0.98/0.98  fof(f57,plain,(
% 0.98/0.98    k5_xboole_0(k2_tarski(sK2,sK2),k4_xboole_0(k2_tarski(sK3,sK3),k2_tarski(sK2,sK2))) = k2_tarski(sK2,sK2)),
% 0.98/0.98    inference(definition_unfolding,[],[f40,f23,f37,f37,f37])).
% 0.98/0.98  
% 0.98/0.98  fof(f2,axiom,(
% 0.98/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.98/0.98  
% 0.98/0.98  fof(f10,plain,(
% 0.98/0.98    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.98/0.98    inference(ennf_transformation,[],[f2])).
% 0.98/0.98  
% 0.98/0.98  fof(f12,plain,(
% 0.98/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.98/0.98    inference(nnf_transformation,[],[f10])).
% 0.98/0.98  
% 0.98/0.98  fof(f13,plain,(
% 0.98/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.98/0.98    inference(flattening,[],[f12])).
% 0.98/0.98  
% 0.98/0.98  fof(f14,plain,(
% 0.98/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.98/0.98    inference(rectify,[],[f13])).
% 0.98/0.98  
% 0.98/0.98  fof(f15,plain,(
% 0.98/0.98    ! [X3,X2,X1,X0] : (? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3))) => (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3))))),
% 0.98/0.98    introduced(choice_axiom,[])).
% 0.98/0.98  
% 0.98/0.98  fof(f16,plain,(
% 0.98/0.98    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | (((sK0(X0,X1,X2,X3) != X2 & sK0(X0,X1,X2,X3) != X1 & sK0(X0,X1,X2,X3) != X0) | ~r2_hidden(sK0(X0,X1,X2,X3),X3)) & (sK0(X0,X1,X2,X3) = X2 | sK0(X0,X1,X2,X3) = X1 | sK0(X0,X1,X2,X3) = X0 | r2_hidden(sK0(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X2 != X5 & X1 != X5 & X0 != X5)) & (X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X3))) | k1_enumset1(X0,X1,X2) != X3))),
% 0.98/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f15])).
% 0.98/0.98  
% 0.98/0.98  fof(f27,plain,(
% 0.98/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k1_enumset1(X0,X1,X2) != X3) )),
% 0.98/0.98    inference(cnf_transformation,[],[f16])).
% 0.98/0.98  
% 0.98/0.98  fof(f48,plain,(
% 0.98/0.98    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) != X3) )),
% 0.98/0.98    inference(definition_unfolding,[],[f27,f42])).
% 0.98/0.98  
% 0.98/0.98  fof(f58,plain,(
% 0.98/0.98    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0))) != X3) )),
% 0.98/0.98    inference(equality_resolution,[],[f48])).
% 0.98/0.98  
% 0.98/0.98  fof(f59,plain,(
% 0.98/0.98    ( ! [X0,X5,X1] : (r2_hidden(X5,k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X5),k2_tarski(X0,X0))))) )),
% 0.98/0.98    inference(equality_resolution,[],[f58])).
% 0.98/0.98  
% 0.98/0.98  fof(f3,axiom,(
% 0.98/0.98    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.98/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.98/0.98  
% 0.98/0.98  fof(f17,plain,(
% 0.98/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.98/0.98    inference(nnf_transformation,[],[f3])).
% 0.98/0.98  
% 0.98/0.98  fof(f18,plain,(
% 0.98/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.98/0.98    inference(rectify,[],[f17])).
% 0.98/0.98  
% 0.98/0.98  fof(f19,plain,(
% 0.98/0.98    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 0.98/0.98    introduced(choice_axiom,[])).
% 0.98/0.98  
% 0.98/0.98  fof(f20,plain,(
% 0.98/0.98    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.98/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f19])).
% 0.98/0.98  
% 0.98/0.98  fof(f32,plain,(
% 0.98/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.98/0.98    inference(cnf_transformation,[],[f20])).
% 0.98/0.98  
% 0.98/0.98  fof(f55,plain,(
% 0.98/0.98    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 0.98/0.98    inference(definition_unfolding,[],[f32,f37])).
% 0.98/0.98  
% 0.98/0.98  fof(f67,plain,(
% 0.98/0.98    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k2_tarski(X0,X0))) )),
% 0.98/0.98    inference(equality_resolution,[],[f55])).
% 0.98/0.98  
% 0.98/0.98  fof(f33,plain,(
% 0.98/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.98/0.98    inference(cnf_transformation,[],[f20])).
% 0.98/0.98  
% 0.98/0.98  fof(f54,plain,(
% 0.98/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 0.98/0.98    inference(definition_unfolding,[],[f33,f37])).
% 0.98/0.98  
% 0.98/0.98  fof(f65,plain,(
% 0.98/0.98    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 0.98/0.98    inference(equality_resolution,[],[f54])).
% 0.98/0.98  
% 0.98/0.98  fof(f66,plain,(
% 0.98/0.98    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 0.98/0.98    inference(equality_resolution,[],[f65])).
% 0.98/0.98  
% 0.98/0.98  fof(f41,plain,(
% 0.98/0.98    sK2 != sK3),
% 0.98/0.98    inference(cnf_transformation,[],[f22])).
% 0.98/0.98  
% 0.98/0.98  cnf(c_13,plain,
% 0.98/0.98      ( k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) = k2_enumset1(X0,X0,X1,X2) ),
% 0.98/0.98      inference(cnf_transformation,[],[f56]) ).
% 0.98/0.98  
% 0.98/0.98  cnf(c_15,negated_conjecture,
% 0.98/0.98      ( k5_xboole_0(k2_tarski(sK2,sK2),k4_xboole_0(k2_tarski(sK3,sK3),k2_tarski(sK2,sK2))) = k2_tarski(sK2,sK2) ),
% 0.98/0.98      inference(cnf_transformation,[],[f57]) ).
% 0.98/0.98  
% 0.98/0.98  cnf(c_1448,plain,
% 0.98/0.98      ( k2_enumset1(sK2,sK2,sK3,sK3) = k2_tarski(sK2,sK2) ),
% 0.98/0.98      inference(superposition,[status(thm)],[c_13,c_15]) ).
% 0.98/0.98  
% 0.98/0.98  cnf(c_5,plain,
% 0.98/0.98      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X1)))) ),
% 0.98/0.98      inference(cnf_transformation,[],[f59]) ).
% 0.98/0.98  
% 0.98/0.98  cnf(c_881,plain,
% 0.98/0.98      ( r2_hidden(X0,k5_xboole_0(k2_tarski(X1,X1),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X1)))) = iProver_top ),
% 0.98/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 0.98/0.98  
% 0.98/0.98  cnf(c_906,plain,
% 0.98/0.98      ( r2_hidden(X0,k2_enumset1(X1,X1,X2,X0)) = iProver_top ),
% 0.98/0.98      inference(demodulation,[status(thm)],[c_13,c_881]) ).
% 0.98/0.98  
% 0.98/0.98  cnf(c_1570,plain,
% 0.98/0.98      ( r2_hidden(sK3,k2_tarski(sK2,sK2)) = iProver_top ),
% 0.98/0.98      inference(superposition,[status(thm)],[c_1448,c_906]) ).
% 0.98/0.98  
% 0.98/0.98  cnf(c_12,plain,
% 0.98/0.98      ( ~ r2_hidden(X0,k2_tarski(X1,X1)) | X0 = X1 ),
% 0.98/0.98      inference(cnf_transformation,[],[f67]) ).
% 0.98/0.98  
% 0.98/0.98  cnf(c_1030,plain,
% 0.98/0.98      ( ~ r2_hidden(sK3,k2_tarski(X0,X0)) | sK3 = X0 ),
% 0.98/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 0.98/0.98  
% 0.98/0.98  cnf(c_1031,plain,
% 0.98/0.98      ( sK3 = X0 | r2_hidden(sK3,k2_tarski(X0,X0)) != iProver_top ),
% 0.98/0.98      inference(predicate_to_equality,[status(thm)],[c_1030]) ).
% 0.98/0.98  
% 0.98/0.98  cnf(c_1033,plain,
% 0.98/0.98      ( sK3 = sK2 | r2_hidden(sK3,k2_tarski(sK2,sK2)) != iProver_top ),
% 0.98/0.98      inference(instantiation,[status(thm)],[c_1031]) ).
% 0.98/0.98  
% 0.98/0.98  cnf(c_680,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.98/0.98  
% 0.98/0.98  cnf(c_1002,plain,
% 0.98/0.98      ( sK3 != X0 | sK2 != X0 | sK2 = sK3 ),
% 0.98/0.98      inference(instantiation,[status(thm)],[c_680]) ).
% 0.98/0.98  
% 0.98/0.98  cnf(c_1003,plain,
% 0.98/0.98      ( sK3 != sK2 | sK2 = sK3 | sK2 != sK2 ),
% 0.98/0.98      inference(instantiation,[status(thm)],[c_1002]) ).
% 0.98/0.98  
% 0.98/0.98  cnf(c_11,plain,
% 0.98/0.98      ( r2_hidden(X0,k2_tarski(X0,X0)) ),
% 0.98/0.98      inference(cnf_transformation,[],[f66]) ).
% 0.98/0.98  
% 0.98/0.98  cnf(c_21,plain,
% 0.98/0.98      ( r2_hidden(sK2,k2_tarski(sK2,sK2)) ),
% 0.98/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 0.98/0.98  
% 0.98/0.98  cnf(c_18,plain,
% 0.98/0.98      ( ~ r2_hidden(sK2,k2_tarski(sK2,sK2)) | sK2 = sK2 ),
% 0.98/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 0.98/0.98  
% 0.98/0.98  cnf(c_14,negated_conjecture,
% 0.98/0.98      ( sK2 != sK3 ),
% 0.98/0.98      inference(cnf_transformation,[],[f41]) ).
% 0.98/0.98  
% 0.98/0.98  cnf(contradiction,plain,
% 0.98/0.98      ( $false ),
% 0.98/0.98      inference(minisat,
% 0.98/0.98                [status(thm)],
% 0.98/0.98                [c_1570,c_1033,c_1003,c_21,c_18,c_14]) ).
% 0.98/0.98  
% 0.98/0.98  
% 0.98/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 0.98/0.98  
% 0.98/0.98  ------                               Statistics
% 0.98/0.98  
% 0.98/0.98  ------ General
% 0.98/0.98  
% 0.98/0.98  abstr_ref_over_cycles:                  0
% 0.98/0.98  abstr_ref_under_cycles:                 0
% 0.98/0.98  gc_basic_clause_elim:                   0
% 0.98/0.98  forced_gc_time:                         0
% 0.98/0.98  parsing_time:                           0.007
% 0.98/0.98  unif_index_cands_time:                  0.
% 0.98/0.98  unif_index_add_time:                    0.
% 0.98/0.98  orderings_time:                         0.
% 0.98/0.98  out_proof_time:                         0.007
% 0.98/0.98  total_time:                             0.084
% 0.98/0.98  num_of_symbols:                         40
% 0.98/0.98  num_of_terms:                           1951
% 0.98/0.98  
% 0.98/0.98  ------ Preprocessing
% 0.98/0.98  
% 0.98/0.98  num_of_splits:                          0
% 0.98/0.98  num_of_split_atoms:                     0
% 0.98/0.98  num_of_reused_defs:                     0
% 0.98/0.98  num_eq_ax_congr_red:                    20
% 0.98/0.98  num_of_sem_filtered_clauses:            1
% 0.98/0.98  num_of_subtypes:                        0
% 0.98/0.98  monotx_restored_types:                  0
% 0.98/0.98  sat_num_of_epr_types:                   0
% 0.98/0.98  sat_num_of_non_cyclic_types:            0
% 0.98/0.98  sat_guarded_non_collapsed_types:        0
% 0.98/0.98  num_pure_diseq_elim:                    0
% 0.98/0.98  simp_replaced_by:                       0
% 0.98/0.98  res_preprocessed:                       61
% 0.98/0.98  prep_upred:                             0
% 0.98/0.98  prep_unflattend:                        36
% 0.98/0.98  smt_new_axioms:                         0
% 0.98/0.98  pred_elim_cands:                        1
% 0.98/0.98  pred_elim:                              0
% 0.98/0.98  pred_elim_cl:                           0
% 0.98/0.98  pred_elim_cycles:                       1
% 0.98/0.98  merged_defs:                            0
% 0.98/0.98  merged_defs_ncl:                        0
% 0.98/0.98  bin_hyper_res:                          0
% 0.98/0.98  prep_cycles:                            3
% 0.98/0.98  pred_elim_time:                         0.018
% 0.98/0.98  splitting_time:                         0.
% 0.98/0.98  sem_filter_time:                        0.
% 0.98/0.98  monotx_time:                            0.
% 0.98/0.98  subtype_inf_time:                       0.
% 0.98/0.98  
% 0.98/0.98  ------ Problem properties
% 0.98/0.98  
% 0.98/0.98  clauses:                                16
% 0.98/0.98  conjectures:                            2
% 0.98/0.98  epr:                                    1
% 0.98/0.98  horn:                                   13
% 0.98/0.98  ground:                                 2
% 0.98/0.98  unary:                                  8
% 0.98/0.98  binary:                                 1
% 0.98/0.98  lits:                                   34
% 0.98/0.98  lits_eq:                                22
% 0.98/0.98  fd_pure:                                0
% 0.98/0.98  fd_pseudo:                              0
% 0.98/0.98  fd_cond:                                0
% 0.98/0.98  fd_pseudo_cond:                         6
% 0.98/0.98  ac_symbols:                             0
% 0.98/0.98  
% 0.98/0.98  ------ Propositional Solver
% 0.98/0.98  
% 0.98/0.98  prop_solver_calls:                      21
% 0.98/0.98  prop_fast_solver_calls:                 403
% 0.98/0.98  smt_solver_calls:                       0
% 0.98/0.98  smt_fast_solver_calls:                  0
% 0.98/0.98  prop_num_of_clauses:                    417
% 0.98/0.98  prop_preprocess_simplified:             2248
% 0.98/0.98  prop_fo_subsumed:                       0
% 0.98/0.98  prop_solver_time:                       0.
% 0.98/0.98  smt_solver_time:                        0.
% 0.98/0.98  smt_fast_solver_time:                   0.
% 0.98/0.98  prop_fast_solver_time:                  0.
% 0.98/0.98  prop_unsat_core_time:                   0.
% 0.98/0.98  
% 0.98/0.98  ------ QBF
% 0.98/0.98  
% 0.98/0.98  qbf_q_res:                              0
% 0.98/0.98  qbf_num_tautologies:                    0
% 0.98/0.98  qbf_prep_cycles:                        0
% 0.98/0.98  
% 0.98/0.98  ------ BMC1
% 0.98/0.98  
% 0.98/0.98  bmc1_current_bound:                     -1
% 0.98/0.98  bmc1_last_solved_bound:                 -1
% 0.98/0.98  bmc1_unsat_core_size:                   -1
% 0.98/0.98  bmc1_unsat_core_parents_size:           -1
% 0.98/0.98  bmc1_merge_next_fun:                    0
% 0.98/0.98  bmc1_unsat_core_clauses_time:           0.
% 0.98/0.98  
% 0.98/0.98  ------ Instantiation
% 0.98/0.98  
% 0.98/0.98  inst_num_of_clauses:                    123
% 0.98/0.98  inst_num_in_passive:                    39
% 0.98/0.98  inst_num_in_active:                     59
% 0.98/0.98  inst_num_in_unprocessed:                25
% 0.98/0.98  inst_num_of_loops:                      60
% 0.98/0.98  inst_num_of_learning_restarts:          0
% 0.98/0.98  inst_num_moves_active_passive:          0
% 0.98/0.98  inst_lit_activity:                      0
% 0.98/0.98  inst_lit_activity_moves:                0
% 0.98/0.98  inst_num_tautologies:                   0
% 0.98/0.98  inst_num_prop_implied:                  0
% 0.98/0.98  inst_num_existing_simplified:           0
% 0.98/0.98  inst_num_eq_res_simplified:             0
% 0.98/0.98  inst_num_child_elim:                    0
% 0.98/0.98  inst_num_of_dismatching_blockings:      18
% 0.98/0.98  inst_num_of_non_proper_insts:           69
% 0.98/0.98  inst_num_of_duplicates:                 0
% 0.98/0.98  inst_inst_num_from_inst_to_res:         0
% 0.98/0.98  inst_dismatching_checking_time:         0.
% 0.98/0.98  
% 0.98/0.98  ------ Resolution
% 0.98/0.98  
% 0.98/0.98  res_num_of_clauses:                     0
% 0.98/0.98  res_num_in_passive:                     0
% 0.98/0.98  res_num_in_active:                      0
% 0.98/0.98  res_num_of_loops:                       64
% 0.98/0.98  res_forward_subset_subsumed:            16
% 0.98/0.98  res_backward_subset_subsumed:           0
% 0.98/0.98  res_forward_subsumed:                   0
% 0.98/0.98  res_backward_subsumed:                  0
% 0.98/0.98  res_forward_subsumption_resolution:     0
% 0.98/0.98  res_backward_subsumption_resolution:    0
% 0.98/0.98  res_clause_to_clause_subsumption:       129
% 0.98/0.98  res_orphan_elimination:                 0
% 0.98/0.98  res_tautology_del:                      6
% 0.98/0.98  res_num_eq_res_simplified:              0
% 0.98/0.98  res_num_sel_changes:                    0
% 0.98/0.98  res_moves_from_active_to_pass:          0
% 0.98/0.98  
% 0.98/0.98  ------ Superposition
% 0.98/0.98  
% 0.98/0.98  sup_time_total:                         0.
% 0.98/0.98  sup_time_generating:                    0.
% 0.98/0.98  sup_time_sim_full:                      0.
% 0.98/0.98  sup_time_sim_immed:                     0.
% 0.98/0.98  
% 0.98/0.98  sup_num_of_clauses:                     23
% 0.98/0.98  sup_num_in_active:                      12
% 0.98/0.98  sup_num_in_passive:                     11
% 0.98/0.98  sup_num_of_loops:                       11
% 0.98/0.98  sup_fw_superposition:                   3
% 0.98/0.98  sup_bw_superposition:                   9
% 0.98/0.98  sup_immediate_simplified:               1
% 0.98/0.98  sup_given_eliminated:                   0
% 0.98/0.98  comparisons_done:                       0
% 0.98/0.98  comparisons_avoided:                    2
% 0.98/0.98  
% 0.98/0.98  ------ Simplifications
% 0.98/0.98  
% 0.98/0.98  
% 0.98/0.98  sim_fw_subset_subsumed:                 0
% 0.98/0.98  sim_bw_subset_subsumed:                 0
% 0.98/0.98  sim_fw_subsumed:                        1
% 0.98/0.98  sim_bw_subsumed:                        0
% 0.98/0.98  sim_fw_subsumption_res:                 0
% 0.98/0.98  sim_bw_subsumption_res:                 0
% 0.98/0.98  sim_tautology_del:                      0
% 0.98/0.98  sim_eq_tautology_del:                   1
% 0.98/0.98  sim_eq_res_simp:                        0
% 0.98/0.98  sim_fw_demodulated:                     5
% 0.98/0.98  sim_bw_demodulated:                     3
% 0.98/0.98  sim_light_normalised:                   0
% 0.98/0.98  sim_joinable_taut:                      0
% 0.98/0.98  sim_joinable_simp:                      0
% 0.98/0.98  sim_ac_normalised:                      0
% 0.98/0.98  sim_smt_subsumption:                    0
% 0.98/0.98  
%------------------------------------------------------------------------------
