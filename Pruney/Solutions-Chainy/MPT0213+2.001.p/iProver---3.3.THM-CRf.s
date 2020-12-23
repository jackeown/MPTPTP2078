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
% DateTime   : Thu Dec  3 11:28:38 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 429 expanded)
%              Number of clauses        :   33 ( 145 expanded)
%              Number of leaves         :   11 ( 115 expanded)
%              Depth                    :   18
%              Number of atoms          :  230 (2325 expanded)
%              Number of equality atoms :   77 ( 475 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f14])).

fof(f18,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK3(X0,X5),X0)
        & r2_hidden(X5,sK3(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(X2,X4) )
     => ( r2_hidden(sK2(X0,X1),X0)
        & r2_hidden(X2,sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK1(X0,X1),X3) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK1(X0,X1),X4) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK1(X0,X1),X3) )
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( ( r2_hidden(sK2(X0,X1),X0)
              & r2_hidden(sK1(X0,X1),sK2(X0,X1)) )
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK3(X0,X5),X0)
                & r2_hidden(X5,sK3(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f18,f17,f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
      | r2_hidden(sK2(X0,X1),X0)
      | r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),X0)
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f9])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f10])).

fof(f12,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f23])).

fof(f28,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X5] :
      ( r2_hidden(X5,sK3(X0,X5))
      | ~ r2_hidden(X5,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,conjecture,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(negated_conjecture,[],[f5])).

fof(f7,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(flattening,[],[f6])).

fof(f34,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_9,plain,
    ( r2_hidden(sK2(X0,X1),X0)
    | r2_hidden(sK1(X0,X1),X1)
    | k3_tarski(X0) = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_369,plain,
    ( k3_tarski(X0) = X1
    | r2_hidden(sK2(X0,X1),X0) = iProver_top
    | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k3_tarski(X1))
    | r2_hidden(sK3(X1,X0),X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_366,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f27])).

cnf(c_4,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_373,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_634,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_373])).

cnf(c_707,plain,
    ( r2_hidden(X0,k3_tarski(k1_xboole_0)) != iProver_top
    | r2_hidden(sK3(k1_xboole_0,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_366,c_634])).

cnf(c_13,plain,
    ( r2_hidden(X0,sK3(X1,X0))
    | ~ r2_hidden(X0,k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_365,plain,
    ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
    | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f20])).

cnf(c_377,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_699,plain,
    ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_365,c_377])).

cnf(c_3199,plain,
    ( r2_hidden(X0,k3_tarski(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_707,c_699])).

cnf(c_3454,plain,
    ( k3_tarski(k3_tarski(k1_xboole_0)) = X0
    | r2_hidden(sK1(k3_tarski(k1_xboole_0),X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_369,c_3199])).

cnf(c_635,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k2_xboole_0(X2,X1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_373,c_377])).

cnf(c_1305,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_635])).

cnf(c_1329,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k2_xboole_0(X2,X1),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_373,c_1305])).

cnf(c_1841,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_1329])).

cnf(c_6662,plain,
    ( k3_tarski(k3_tarski(k1_xboole_0)) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3454,c_1841])).

cnf(c_6664,plain,
    ( k3_tarski(k3_tarski(k1_xboole_0)) = k3_tarski(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_3454,c_3199])).

cnf(c_8526,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0
    | r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6662,c_6664])).

cnf(c_14,negated_conjecture,
    ( k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_150,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_159,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_150])).

cnf(c_151,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_481,plain,
    ( k3_tarski(k1_xboole_0) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_151])).

cnf(c_482,plain,
    ( k3_tarski(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k3_tarski(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_8530,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8526,c_14,c_159,c_482])).

cnf(c_8537,plain,
    ( k3_tarski(k1_xboole_0) = X0
    | r2_hidden(sK1(k1_xboole_0,X0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_369,c_8530])).

cnf(c_9027,plain,
    ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8537,c_8530])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9027,c_482,c_159,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.06/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.02  
% 3.06/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.06/1.02  
% 3.06/1.02  ------  iProver source info
% 3.06/1.02  
% 3.06/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.06/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.06/1.02  git: non_committed_changes: false
% 3.06/1.02  git: last_make_outside_of_git: false
% 3.06/1.02  
% 3.06/1.02  ------ 
% 3.06/1.02  
% 3.06/1.02  ------ Input Options
% 3.06/1.02  
% 3.06/1.02  --out_options                           all
% 3.06/1.02  --tptp_safe_out                         true
% 3.06/1.02  --problem_path                          ""
% 3.06/1.02  --include_path                          ""
% 3.06/1.02  --clausifier                            res/vclausify_rel
% 3.06/1.02  --clausifier_options                    --mode clausify
% 3.06/1.02  --stdin                                 false
% 3.06/1.02  --stats_out                             all
% 3.06/1.02  
% 3.06/1.02  ------ General Options
% 3.06/1.02  
% 3.06/1.02  --fof                                   false
% 3.06/1.02  --time_out_real                         305.
% 3.06/1.02  --time_out_virtual                      -1.
% 3.06/1.02  --symbol_type_check                     false
% 3.06/1.02  --clausify_out                          false
% 3.06/1.02  --sig_cnt_out                           false
% 3.06/1.02  --trig_cnt_out                          false
% 3.06/1.02  --trig_cnt_out_tolerance                1.
% 3.06/1.02  --trig_cnt_out_sk_spl                   false
% 3.06/1.02  --abstr_cl_out                          false
% 3.06/1.02  
% 3.06/1.02  ------ Global Options
% 3.06/1.02  
% 3.06/1.02  --schedule                              default
% 3.06/1.02  --add_important_lit                     false
% 3.06/1.02  --prop_solver_per_cl                    1000
% 3.06/1.02  --min_unsat_core                        false
% 3.06/1.02  --soft_assumptions                      false
% 3.06/1.02  --soft_lemma_size                       3
% 3.06/1.02  --prop_impl_unit_size                   0
% 3.06/1.02  --prop_impl_unit                        []
% 3.06/1.02  --share_sel_clauses                     true
% 3.06/1.02  --reset_solvers                         false
% 3.06/1.02  --bc_imp_inh                            [conj_cone]
% 3.06/1.02  --conj_cone_tolerance                   3.
% 3.06/1.02  --extra_neg_conj                        none
% 3.06/1.02  --large_theory_mode                     true
% 3.06/1.02  --prolific_symb_bound                   200
% 3.06/1.02  --lt_threshold                          2000
% 3.06/1.02  --clause_weak_htbl                      true
% 3.06/1.02  --gc_record_bc_elim                     false
% 3.06/1.02  
% 3.06/1.02  ------ Preprocessing Options
% 3.06/1.02  
% 3.06/1.02  --preprocessing_flag                    true
% 3.06/1.02  --time_out_prep_mult                    0.1
% 3.06/1.02  --splitting_mode                        input
% 3.06/1.02  --splitting_grd                         true
% 3.06/1.02  --splitting_cvd                         false
% 3.06/1.02  --splitting_cvd_svl                     false
% 3.06/1.02  --splitting_nvd                         32
% 3.06/1.02  --sub_typing                            true
% 3.06/1.02  --prep_gs_sim                           true
% 3.06/1.02  --prep_unflatten                        true
% 3.06/1.02  --prep_res_sim                          true
% 3.06/1.02  --prep_upred                            true
% 3.06/1.02  --prep_sem_filter                       exhaustive
% 3.06/1.02  --prep_sem_filter_out                   false
% 3.06/1.02  --pred_elim                             true
% 3.06/1.02  --res_sim_input                         true
% 3.06/1.02  --eq_ax_congr_red                       true
% 3.06/1.02  --pure_diseq_elim                       true
% 3.06/1.02  --brand_transform                       false
% 3.06/1.02  --non_eq_to_eq                          false
% 3.06/1.02  --prep_def_merge                        true
% 3.06/1.02  --prep_def_merge_prop_impl              false
% 3.06/1.02  --prep_def_merge_mbd                    true
% 3.06/1.02  --prep_def_merge_tr_red                 false
% 3.06/1.02  --prep_def_merge_tr_cl                  false
% 3.06/1.02  --smt_preprocessing                     true
% 3.06/1.02  --smt_ac_axioms                         fast
% 3.06/1.02  --preprocessed_out                      false
% 3.06/1.02  --preprocessed_stats                    false
% 3.06/1.02  
% 3.06/1.02  ------ Abstraction refinement Options
% 3.06/1.02  
% 3.06/1.02  --abstr_ref                             []
% 3.06/1.02  --abstr_ref_prep                        false
% 3.06/1.02  --abstr_ref_until_sat                   false
% 3.06/1.02  --abstr_ref_sig_restrict                funpre
% 3.06/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/1.02  --abstr_ref_under                       []
% 3.06/1.02  
% 3.06/1.02  ------ SAT Options
% 3.06/1.02  
% 3.06/1.02  --sat_mode                              false
% 3.06/1.02  --sat_fm_restart_options                ""
% 3.06/1.02  --sat_gr_def                            false
% 3.06/1.02  --sat_epr_types                         true
% 3.06/1.02  --sat_non_cyclic_types                  false
% 3.06/1.02  --sat_finite_models                     false
% 3.06/1.02  --sat_fm_lemmas                         false
% 3.06/1.02  --sat_fm_prep                           false
% 3.06/1.02  --sat_fm_uc_incr                        true
% 3.06/1.02  --sat_out_model                         small
% 3.06/1.02  --sat_out_clauses                       false
% 3.06/1.02  
% 3.06/1.02  ------ QBF Options
% 3.06/1.02  
% 3.06/1.02  --qbf_mode                              false
% 3.06/1.02  --qbf_elim_univ                         false
% 3.06/1.02  --qbf_dom_inst                          none
% 3.06/1.02  --qbf_dom_pre_inst                      false
% 3.06/1.02  --qbf_sk_in                             false
% 3.06/1.02  --qbf_pred_elim                         true
% 3.06/1.02  --qbf_split                             512
% 3.06/1.02  
% 3.06/1.02  ------ BMC1 Options
% 3.06/1.02  
% 3.06/1.02  --bmc1_incremental                      false
% 3.06/1.02  --bmc1_axioms                           reachable_all
% 3.06/1.02  --bmc1_min_bound                        0
% 3.06/1.02  --bmc1_max_bound                        -1
% 3.06/1.02  --bmc1_max_bound_default                -1
% 3.06/1.02  --bmc1_symbol_reachability              true
% 3.06/1.02  --bmc1_property_lemmas                  false
% 3.06/1.02  --bmc1_k_induction                      false
% 3.06/1.02  --bmc1_non_equiv_states                 false
% 3.06/1.02  --bmc1_deadlock                         false
% 3.06/1.02  --bmc1_ucm                              false
% 3.06/1.02  --bmc1_add_unsat_core                   none
% 3.06/1.02  --bmc1_unsat_core_children              false
% 3.06/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/1.02  --bmc1_out_stat                         full
% 3.06/1.02  --bmc1_ground_init                      false
% 3.06/1.02  --bmc1_pre_inst_next_state              false
% 3.06/1.02  --bmc1_pre_inst_state                   false
% 3.06/1.02  --bmc1_pre_inst_reach_state             false
% 3.06/1.02  --bmc1_out_unsat_core                   false
% 3.06/1.02  --bmc1_aig_witness_out                  false
% 3.06/1.02  --bmc1_verbose                          false
% 3.06/1.02  --bmc1_dump_clauses_tptp                false
% 3.06/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.06/1.02  --bmc1_dump_file                        -
% 3.06/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.06/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.06/1.02  --bmc1_ucm_extend_mode                  1
% 3.06/1.02  --bmc1_ucm_init_mode                    2
% 3.06/1.02  --bmc1_ucm_cone_mode                    none
% 3.06/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.06/1.02  --bmc1_ucm_relax_model                  4
% 3.06/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.06/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/1.02  --bmc1_ucm_layered_model                none
% 3.06/1.02  --bmc1_ucm_max_lemma_size               10
% 3.06/1.02  
% 3.06/1.02  ------ AIG Options
% 3.06/1.02  
% 3.06/1.02  --aig_mode                              false
% 3.06/1.02  
% 3.06/1.02  ------ Instantiation Options
% 3.06/1.02  
% 3.06/1.02  --instantiation_flag                    true
% 3.06/1.02  --inst_sos_flag                         false
% 3.06/1.02  --inst_sos_phase                        true
% 3.06/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/1.02  --inst_lit_sel_side                     num_symb
% 3.06/1.02  --inst_solver_per_active                1400
% 3.06/1.02  --inst_solver_calls_frac                1.
% 3.06/1.02  --inst_passive_queue_type               priority_queues
% 3.06/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/1.02  --inst_passive_queues_freq              [25;2]
% 3.06/1.02  --inst_dismatching                      true
% 3.06/1.02  --inst_eager_unprocessed_to_passive     true
% 3.06/1.02  --inst_prop_sim_given                   true
% 3.06/1.02  --inst_prop_sim_new                     false
% 3.06/1.02  --inst_subs_new                         false
% 3.06/1.02  --inst_eq_res_simp                      false
% 3.06/1.02  --inst_subs_given                       false
% 3.06/1.02  --inst_orphan_elimination               true
% 3.06/1.02  --inst_learning_loop_flag               true
% 3.06/1.02  --inst_learning_start                   3000
% 3.06/1.02  --inst_learning_factor                  2
% 3.06/1.02  --inst_start_prop_sim_after_learn       3
% 3.06/1.02  --inst_sel_renew                        solver
% 3.06/1.02  --inst_lit_activity_flag                true
% 3.06/1.02  --inst_restr_to_given                   false
% 3.06/1.02  --inst_activity_threshold               500
% 3.06/1.02  --inst_out_proof                        true
% 3.06/1.02  
% 3.06/1.02  ------ Resolution Options
% 3.06/1.02  
% 3.06/1.02  --resolution_flag                       true
% 3.06/1.02  --res_lit_sel                           adaptive
% 3.06/1.02  --res_lit_sel_side                      none
% 3.06/1.02  --res_ordering                          kbo
% 3.06/1.02  --res_to_prop_solver                    active
% 3.06/1.02  --res_prop_simpl_new                    false
% 3.06/1.02  --res_prop_simpl_given                  true
% 3.06/1.02  --res_passive_queue_type                priority_queues
% 3.06/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/1.02  --res_passive_queues_freq               [15;5]
% 3.06/1.02  --res_forward_subs                      full
% 3.06/1.02  --res_backward_subs                     full
% 3.06/1.02  --res_forward_subs_resolution           true
% 3.06/1.02  --res_backward_subs_resolution          true
% 3.06/1.02  --res_orphan_elimination                true
% 3.06/1.02  --res_time_limit                        2.
% 3.06/1.02  --res_out_proof                         true
% 3.06/1.02  
% 3.06/1.02  ------ Superposition Options
% 3.06/1.02  
% 3.06/1.02  --superposition_flag                    true
% 3.06/1.02  --sup_passive_queue_type                priority_queues
% 3.06/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.06/1.02  --demod_completeness_check              fast
% 3.06/1.02  --demod_use_ground                      true
% 3.06/1.02  --sup_to_prop_solver                    passive
% 3.06/1.02  --sup_prop_simpl_new                    true
% 3.06/1.02  --sup_prop_simpl_given                  true
% 3.06/1.02  --sup_fun_splitting                     false
% 3.06/1.02  --sup_smt_interval                      50000
% 3.06/1.02  
% 3.06/1.02  ------ Superposition Simplification Setup
% 3.06/1.02  
% 3.06/1.02  --sup_indices_passive                   []
% 3.06/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.02  --sup_full_bw                           [BwDemod]
% 3.06/1.02  --sup_immed_triv                        [TrivRules]
% 3.06/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.02  --sup_immed_bw_main                     []
% 3.06/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.02  
% 3.06/1.02  ------ Combination Options
% 3.06/1.02  
% 3.06/1.02  --comb_res_mult                         3
% 3.06/1.02  --comb_sup_mult                         2
% 3.06/1.02  --comb_inst_mult                        10
% 3.06/1.02  
% 3.06/1.02  ------ Debug Options
% 3.06/1.02  
% 3.06/1.02  --dbg_backtrace                         false
% 3.06/1.02  --dbg_dump_prop_clauses                 false
% 3.06/1.02  --dbg_dump_prop_clauses_file            -
% 3.06/1.02  --dbg_out_stat                          false
% 3.06/1.02  ------ Parsing...
% 3.06/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.06/1.02  
% 3.06/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.06/1.02  
% 3.06/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.06/1.02  
% 3.06/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.06/1.02  ------ Proving...
% 3.06/1.02  ------ Problem Properties 
% 3.06/1.02  
% 3.06/1.02  
% 3.06/1.02  clauses                                 15
% 3.06/1.02  conjectures                             1
% 3.06/1.02  EPR                                     1
% 3.06/1.02  Horn                                    11
% 3.06/1.02  unary                                   2
% 3.06/1.02  binary                                  5
% 3.06/1.02  lits                                    38
% 3.06/1.02  lits eq                                 8
% 3.06/1.02  fd_pure                                 0
% 3.06/1.02  fd_pseudo                               0
% 3.06/1.02  fd_cond                                 0
% 3.06/1.02  fd_pseudo_cond                          6
% 3.06/1.02  AC symbols                              0
% 3.06/1.02  
% 3.06/1.02  ------ Schedule dynamic 5 is on 
% 3.06/1.02  
% 3.06/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.06/1.02  
% 3.06/1.02  
% 3.06/1.02  ------ 
% 3.06/1.02  Current options:
% 3.06/1.02  ------ 
% 3.06/1.02  
% 3.06/1.02  ------ Input Options
% 3.06/1.02  
% 3.06/1.02  --out_options                           all
% 3.06/1.02  --tptp_safe_out                         true
% 3.06/1.02  --problem_path                          ""
% 3.06/1.02  --include_path                          ""
% 3.06/1.02  --clausifier                            res/vclausify_rel
% 3.06/1.02  --clausifier_options                    --mode clausify
% 3.06/1.02  --stdin                                 false
% 3.06/1.02  --stats_out                             all
% 3.06/1.02  
% 3.06/1.02  ------ General Options
% 3.06/1.02  
% 3.06/1.02  --fof                                   false
% 3.06/1.02  --time_out_real                         305.
% 3.06/1.02  --time_out_virtual                      -1.
% 3.06/1.02  --symbol_type_check                     false
% 3.06/1.02  --clausify_out                          false
% 3.06/1.02  --sig_cnt_out                           false
% 3.06/1.02  --trig_cnt_out                          false
% 3.06/1.02  --trig_cnt_out_tolerance                1.
% 3.06/1.02  --trig_cnt_out_sk_spl                   false
% 3.06/1.02  --abstr_cl_out                          false
% 3.06/1.02  
% 3.06/1.02  ------ Global Options
% 3.06/1.02  
% 3.06/1.02  --schedule                              default
% 3.06/1.02  --add_important_lit                     false
% 3.06/1.02  --prop_solver_per_cl                    1000
% 3.06/1.02  --min_unsat_core                        false
% 3.06/1.02  --soft_assumptions                      false
% 3.06/1.02  --soft_lemma_size                       3
% 3.06/1.02  --prop_impl_unit_size                   0
% 3.06/1.02  --prop_impl_unit                        []
% 3.06/1.02  --share_sel_clauses                     true
% 3.06/1.02  --reset_solvers                         false
% 3.06/1.02  --bc_imp_inh                            [conj_cone]
% 3.06/1.02  --conj_cone_tolerance                   3.
% 3.06/1.02  --extra_neg_conj                        none
% 3.06/1.02  --large_theory_mode                     true
% 3.06/1.02  --prolific_symb_bound                   200
% 3.06/1.02  --lt_threshold                          2000
% 3.06/1.02  --clause_weak_htbl                      true
% 3.06/1.02  --gc_record_bc_elim                     false
% 3.06/1.02  
% 3.06/1.02  ------ Preprocessing Options
% 3.06/1.02  
% 3.06/1.02  --preprocessing_flag                    true
% 3.06/1.02  --time_out_prep_mult                    0.1
% 3.06/1.02  --splitting_mode                        input
% 3.06/1.02  --splitting_grd                         true
% 3.06/1.02  --splitting_cvd                         false
% 3.06/1.02  --splitting_cvd_svl                     false
% 3.06/1.02  --splitting_nvd                         32
% 3.06/1.02  --sub_typing                            true
% 3.06/1.02  --prep_gs_sim                           true
% 3.06/1.02  --prep_unflatten                        true
% 3.06/1.02  --prep_res_sim                          true
% 3.06/1.02  --prep_upred                            true
% 3.06/1.02  --prep_sem_filter                       exhaustive
% 3.06/1.02  --prep_sem_filter_out                   false
% 3.06/1.02  --pred_elim                             true
% 3.06/1.02  --res_sim_input                         true
% 3.06/1.02  --eq_ax_congr_red                       true
% 3.06/1.02  --pure_diseq_elim                       true
% 3.06/1.02  --brand_transform                       false
% 3.06/1.02  --non_eq_to_eq                          false
% 3.06/1.02  --prep_def_merge                        true
% 3.06/1.02  --prep_def_merge_prop_impl              false
% 3.06/1.02  --prep_def_merge_mbd                    true
% 3.06/1.02  --prep_def_merge_tr_red                 false
% 3.06/1.02  --prep_def_merge_tr_cl                  false
% 3.06/1.02  --smt_preprocessing                     true
% 3.06/1.02  --smt_ac_axioms                         fast
% 3.06/1.02  --preprocessed_out                      false
% 3.06/1.02  --preprocessed_stats                    false
% 3.06/1.02  
% 3.06/1.02  ------ Abstraction refinement Options
% 3.06/1.02  
% 3.06/1.02  --abstr_ref                             []
% 3.06/1.02  --abstr_ref_prep                        false
% 3.06/1.02  --abstr_ref_until_sat                   false
% 3.06/1.02  --abstr_ref_sig_restrict                funpre
% 3.06/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/1.02  --abstr_ref_under                       []
% 3.06/1.02  
% 3.06/1.02  ------ SAT Options
% 3.06/1.02  
% 3.06/1.02  --sat_mode                              false
% 3.06/1.02  --sat_fm_restart_options                ""
% 3.06/1.02  --sat_gr_def                            false
% 3.06/1.02  --sat_epr_types                         true
% 3.06/1.02  --sat_non_cyclic_types                  false
% 3.06/1.02  --sat_finite_models                     false
% 3.06/1.02  --sat_fm_lemmas                         false
% 3.06/1.02  --sat_fm_prep                           false
% 3.06/1.02  --sat_fm_uc_incr                        true
% 3.06/1.02  --sat_out_model                         small
% 3.06/1.02  --sat_out_clauses                       false
% 3.06/1.02  
% 3.06/1.02  ------ QBF Options
% 3.06/1.02  
% 3.06/1.02  --qbf_mode                              false
% 3.06/1.02  --qbf_elim_univ                         false
% 3.06/1.02  --qbf_dom_inst                          none
% 3.06/1.02  --qbf_dom_pre_inst                      false
% 3.06/1.02  --qbf_sk_in                             false
% 3.06/1.02  --qbf_pred_elim                         true
% 3.06/1.02  --qbf_split                             512
% 3.06/1.02  
% 3.06/1.02  ------ BMC1 Options
% 3.06/1.02  
% 3.06/1.02  --bmc1_incremental                      false
% 3.06/1.02  --bmc1_axioms                           reachable_all
% 3.06/1.02  --bmc1_min_bound                        0
% 3.06/1.02  --bmc1_max_bound                        -1
% 3.06/1.02  --bmc1_max_bound_default                -1
% 3.06/1.02  --bmc1_symbol_reachability              true
% 3.06/1.02  --bmc1_property_lemmas                  false
% 3.06/1.02  --bmc1_k_induction                      false
% 3.06/1.02  --bmc1_non_equiv_states                 false
% 3.06/1.02  --bmc1_deadlock                         false
% 3.06/1.02  --bmc1_ucm                              false
% 3.06/1.02  --bmc1_add_unsat_core                   none
% 3.06/1.02  --bmc1_unsat_core_children              false
% 3.06/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/1.02  --bmc1_out_stat                         full
% 3.06/1.02  --bmc1_ground_init                      false
% 3.06/1.02  --bmc1_pre_inst_next_state              false
% 3.06/1.02  --bmc1_pre_inst_state                   false
% 3.06/1.02  --bmc1_pre_inst_reach_state             false
% 3.06/1.02  --bmc1_out_unsat_core                   false
% 3.06/1.02  --bmc1_aig_witness_out                  false
% 3.06/1.02  --bmc1_verbose                          false
% 3.06/1.02  --bmc1_dump_clauses_tptp                false
% 3.06/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.06/1.02  --bmc1_dump_file                        -
% 3.06/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.06/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.06/1.02  --bmc1_ucm_extend_mode                  1
% 3.06/1.02  --bmc1_ucm_init_mode                    2
% 3.06/1.02  --bmc1_ucm_cone_mode                    none
% 3.06/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.06/1.02  --bmc1_ucm_relax_model                  4
% 3.06/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.06/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/1.02  --bmc1_ucm_layered_model                none
% 3.06/1.02  --bmc1_ucm_max_lemma_size               10
% 3.06/1.02  
% 3.06/1.02  ------ AIG Options
% 3.06/1.02  
% 3.06/1.02  --aig_mode                              false
% 3.06/1.02  
% 3.06/1.02  ------ Instantiation Options
% 3.06/1.02  
% 3.06/1.02  --instantiation_flag                    true
% 3.06/1.02  --inst_sos_flag                         false
% 3.06/1.02  --inst_sos_phase                        true
% 3.06/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/1.02  --inst_lit_sel_side                     none
% 3.06/1.02  --inst_solver_per_active                1400
% 3.06/1.02  --inst_solver_calls_frac                1.
% 3.06/1.02  --inst_passive_queue_type               priority_queues
% 3.06/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/1.02  --inst_passive_queues_freq              [25;2]
% 3.06/1.02  --inst_dismatching                      true
% 3.06/1.02  --inst_eager_unprocessed_to_passive     true
% 3.06/1.02  --inst_prop_sim_given                   true
% 3.06/1.02  --inst_prop_sim_new                     false
% 3.06/1.02  --inst_subs_new                         false
% 3.06/1.02  --inst_eq_res_simp                      false
% 3.06/1.02  --inst_subs_given                       false
% 3.06/1.02  --inst_orphan_elimination               true
% 3.06/1.02  --inst_learning_loop_flag               true
% 3.06/1.02  --inst_learning_start                   3000
% 3.06/1.02  --inst_learning_factor                  2
% 3.06/1.02  --inst_start_prop_sim_after_learn       3
% 3.06/1.02  --inst_sel_renew                        solver
% 3.06/1.02  --inst_lit_activity_flag                true
% 3.06/1.02  --inst_restr_to_given                   false
% 3.06/1.02  --inst_activity_threshold               500
% 3.06/1.02  --inst_out_proof                        true
% 3.06/1.02  
% 3.06/1.02  ------ Resolution Options
% 3.06/1.02  
% 3.06/1.02  --resolution_flag                       false
% 3.06/1.02  --res_lit_sel                           adaptive
% 3.06/1.02  --res_lit_sel_side                      none
% 3.06/1.02  --res_ordering                          kbo
% 3.06/1.02  --res_to_prop_solver                    active
% 3.06/1.02  --res_prop_simpl_new                    false
% 3.06/1.02  --res_prop_simpl_given                  true
% 3.06/1.02  --res_passive_queue_type                priority_queues
% 3.06/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/1.02  --res_passive_queues_freq               [15;5]
% 3.06/1.02  --res_forward_subs                      full
% 3.06/1.02  --res_backward_subs                     full
% 3.06/1.02  --res_forward_subs_resolution           true
% 3.06/1.02  --res_backward_subs_resolution          true
% 3.06/1.02  --res_orphan_elimination                true
% 3.06/1.02  --res_time_limit                        2.
% 3.06/1.02  --res_out_proof                         true
% 3.06/1.02  
% 3.06/1.02  ------ Superposition Options
% 3.06/1.02  
% 3.06/1.02  --superposition_flag                    true
% 3.06/1.02  --sup_passive_queue_type                priority_queues
% 3.06/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.06/1.02  --demod_completeness_check              fast
% 3.06/1.02  --demod_use_ground                      true
% 3.06/1.02  --sup_to_prop_solver                    passive
% 3.06/1.02  --sup_prop_simpl_new                    true
% 3.06/1.02  --sup_prop_simpl_given                  true
% 3.06/1.02  --sup_fun_splitting                     false
% 3.06/1.02  --sup_smt_interval                      50000
% 3.06/1.02  
% 3.06/1.02  ------ Superposition Simplification Setup
% 3.06/1.02  
% 3.06/1.02  --sup_indices_passive                   []
% 3.06/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.02  --sup_full_bw                           [BwDemod]
% 3.06/1.02  --sup_immed_triv                        [TrivRules]
% 3.06/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.02  --sup_immed_bw_main                     []
% 3.06/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/1.02  
% 3.06/1.02  ------ Combination Options
% 3.06/1.02  
% 3.06/1.02  --comb_res_mult                         3
% 3.06/1.02  --comb_sup_mult                         2
% 3.06/1.02  --comb_inst_mult                        10
% 3.06/1.02  
% 3.06/1.02  ------ Debug Options
% 3.06/1.02  
% 3.06/1.02  --dbg_backtrace                         false
% 3.06/1.02  --dbg_dump_prop_clauses                 false
% 3.06/1.02  --dbg_dump_prop_clauses_file            -
% 3.06/1.02  --dbg_out_stat                          false
% 3.06/1.02  
% 3.06/1.02  
% 3.06/1.02  
% 3.06/1.02  
% 3.06/1.02  ------ Proving...
% 3.06/1.02  
% 3.06/1.02  
% 3.06/1.02  % SZS status Theorem for theBenchmark.p
% 3.06/1.02  
% 3.06/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.06/1.02  
% 3.06/1.02  fof(f4,axiom,(
% 3.06/1.02    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f14,plain,(
% 3.06/1.02    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 3.06/1.02    inference(nnf_transformation,[],[f4])).
% 3.06/1.02  
% 3.06/1.02  fof(f15,plain,(
% 3.06/1.02    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.06/1.02    inference(rectify,[],[f14])).
% 3.06/1.02  
% 3.06/1.02  fof(f18,plain,(
% 3.06/1.02    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))))),
% 3.06/1.02    introduced(choice_axiom,[])).
% 3.06/1.02  
% 3.06/1.02  fof(f17,plain,(
% 3.06/1.02    ( ! [X2] : (! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) => (r2_hidden(sK2(X0,X1),X0) & r2_hidden(X2,sK2(X0,X1))))) )),
% 3.06/1.02    introduced(choice_axiom,[])).
% 3.06/1.02  
% 3.06/1.02  fof(f16,plain,(
% 3.06/1.02    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK1(X0,X1),X4)) | r2_hidden(sK1(X0,X1),X1))))),
% 3.06/1.02    introduced(choice_axiom,[])).
% 3.06/1.02  
% 3.06/1.02  fof(f19,plain,(
% 3.06/1.02    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK1(X0,X1),X3)) | ~r2_hidden(sK1(X0,X1),X1)) & ((r2_hidden(sK2(X0,X1),X0) & r2_hidden(sK1(X0,X1),sK2(X0,X1))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK3(X0,X5),X0) & r2_hidden(X5,sK3(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 3.06/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f15,f18,f17,f16])).
% 3.06/1.02  
% 3.06/1.02  fof(f32,plain,(
% 3.06/1.02    ( ! [X0,X1] : (k3_tarski(X0) = X1 | r2_hidden(sK2(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f19])).
% 3.06/1.02  
% 3.06/1.02  fof(f29,plain,(
% 3.06/1.02    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 3.06/1.02    inference(cnf_transformation,[],[f19])).
% 3.06/1.02  
% 3.06/1.02  fof(f39,plain,(
% 3.06/1.02    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),X0) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 3.06/1.02    inference(equality_resolution,[],[f29])).
% 3.06/1.02  
% 3.06/1.02  fof(f3,axiom,(
% 3.06/1.02    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f27,plain,(
% 3.06/1.02    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.06/1.02    inference(cnf_transformation,[],[f3])).
% 3.06/1.02  
% 3.06/1.02  fof(f2,axiom,(
% 3.06/1.02    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f9,plain,(
% 3.06/1.02    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.06/1.02    inference(nnf_transformation,[],[f2])).
% 3.06/1.02  
% 3.06/1.02  fof(f10,plain,(
% 3.06/1.02    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.06/1.02    inference(flattening,[],[f9])).
% 3.06/1.02  
% 3.06/1.02  fof(f11,plain,(
% 3.06/1.02    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.06/1.02    inference(rectify,[],[f10])).
% 3.06/1.02  
% 3.06/1.02  fof(f12,plain,(
% 3.06/1.02    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.06/1.02    introduced(choice_axiom,[])).
% 3.06/1.02  
% 3.06/1.02  fof(f13,plain,(
% 3.06/1.02    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 3.06/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).
% 3.06/1.02  
% 3.06/1.02  fof(f23,plain,(
% 3.06/1.02    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 3.06/1.02    inference(cnf_transformation,[],[f13])).
% 3.06/1.02  
% 3.06/1.02  fof(f35,plain,(
% 3.06/1.02    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 3.06/1.02    inference(equality_resolution,[],[f23])).
% 3.06/1.02  
% 3.06/1.02  fof(f28,plain,(
% 3.06/1.02    ( ! [X0,X5,X1] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,X1) | k3_tarski(X0) != X1) )),
% 3.06/1.02    inference(cnf_transformation,[],[f19])).
% 3.06/1.02  
% 3.06/1.02  fof(f40,plain,(
% 3.06/1.02    ( ! [X0,X5] : (r2_hidden(X5,sK3(X0,X5)) | ~r2_hidden(X5,k3_tarski(X0))) )),
% 3.06/1.02    inference(equality_resolution,[],[f28])).
% 3.06/1.02  
% 3.06/1.02  fof(f1,axiom,(
% 3.06/1.02    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f8,plain,(
% 3.06/1.02    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 3.06/1.02    inference(ennf_transformation,[],[f1])).
% 3.06/1.02  
% 3.06/1.02  fof(f20,plain,(
% 3.06/1.02    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.06/1.02    inference(cnf_transformation,[],[f8])).
% 3.06/1.02  
% 3.06/1.02  fof(f5,conjecture,(
% 3.06/1.02    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 3.06/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.02  
% 3.06/1.02  fof(f6,negated_conjecture,(
% 3.06/1.02    ~k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 3.06/1.02    inference(negated_conjecture,[],[f5])).
% 3.06/1.02  
% 3.06/1.02  fof(f7,plain,(
% 3.06/1.02    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 3.06/1.02    inference(flattening,[],[f6])).
% 3.06/1.02  
% 3.06/1.02  fof(f34,plain,(
% 3.06/1.02    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 3.06/1.02    inference(cnf_transformation,[],[f7])).
% 3.06/1.02  
% 3.06/1.02  cnf(c_9,plain,
% 3.06/1.02      ( r2_hidden(sK2(X0,X1),X0)
% 3.06/1.02      | r2_hidden(sK1(X0,X1),X1)
% 3.06/1.02      | k3_tarski(X0) = X1 ),
% 3.06/1.02      inference(cnf_transformation,[],[f32]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_369,plain,
% 3.06/1.02      ( k3_tarski(X0) = X1
% 3.06/1.02      | r2_hidden(sK2(X0,X1),X0) = iProver_top
% 3.06/1.02      | r2_hidden(sK1(X0,X1),X1) = iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_12,plain,
% 3.06/1.02      ( ~ r2_hidden(X0,k3_tarski(X1)) | r2_hidden(sK3(X1,X0),X1) ),
% 3.06/1.02      inference(cnf_transformation,[],[f39]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_366,plain,
% 3.06/1.02      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 3.06/1.02      | r2_hidden(sK3(X1,X0),X1) = iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_7,plain,
% 3.06/1.02      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.06/1.02      inference(cnf_transformation,[],[f27]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_4,plain,
% 3.06/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 3.06/1.02      inference(cnf_transformation,[],[f35]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_373,plain,
% 3.06/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.06/1.02      | r2_hidden(X0,k2_xboole_0(X2,X1)) = iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_634,plain,
% 3.06/1.02      ( r2_hidden(X0,X1) = iProver_top
% 3.06/1.02      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_7,c_373]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_707,plain,
% 3.06/1.02      ( r2_hidden(X0,k3_tarski(k1_xboole_0)) != iProver_top
% 3.06/1.02      | r2_hidden(sK3(k1_xboole_0,X0),X1) = iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_366,c_634]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_13,plain,
% 3.06/1.02      ( r2_hidden(X0,sK3(X1,X0)) | ~ r2_hidden(X0,k3_tarski(X1)) ),
% 3.06/1.02      inference(cnf_transformation,[],[f40]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_365,plain,
% 3.06/1.02      ( r2_hidden(X0,sK3(X1,X0)) = iProver_top
% 3.06/1.02      | r2_hidden(X0,k3_tarski(X1)) != iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_0,plain,
% 3.06/1.02      ( ~ r2_hidden(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.06/1.02      inference(cnf_transformation,[],[f20]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_377,plain,
% 3.06/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.06/1.02      | r2_hidden(X1,X0) != iProver_top ),
% 3.06/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_699,plain,
% 3.06/1.02      ( r2_hidden(X0,k3_tarski(X1)) != iProver_top
% 3.06/1.02      | r2_hidden(sK3(X1,X0),X0) != iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_365,c_377]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_3199,plain,
% 3.06/1.02      ( r2_hidden(X0,k3_tarski(k1_xboole_0)) != iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_707,c_699]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_3454,plain,
% 3.06/1.02      ( k3_tarski(k3_tarski(k1_xboole_0)) = X0
% 3.06/1.02      | r2_hidden(sK1(k3_tarski(k1_xboole_0),X0),X0) = iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_369,c_3199]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_635,plain,
% 3.06/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.06/1.02      | r2_hidden(k2_xboole_0(X2,X1),X0) != iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_373,c_377]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_1305,plain,
% 3.06/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.06/1.02      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_7,c_635]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_1329,plain,
% 3.06/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.06/1.02      | r2_hidden(k2_xboole_0(X2,X1),k1_xboole_0) != iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_373,c_1305]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_1841,plain,
% 3.06/1.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top
% 3.06/1.02      | r2_hidden(X1,k1_xboole_0) != iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_7,c_1329]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_6662,plain,
% 3.06/1.02      ( k3_tarski(k3_tarski(k1_xboole_0)) = k1_xboole_0
% 3.06/1.02      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_3454,c_1841]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_6664,plain,
% 3.06/1.02      ( k3_tarski(k3_tarski(k1_xboole_0)) = k3_tarski(k1_xboole_0) ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_3454,c_3199]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_8526,plain,
% 3.06/1.02      ( k3_tarski(k1_xboole_0) = k1_xboole_0
% 3.06/1.02      | r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.06/1.02      inference(demodulation,[status(thm)],[c_6662,c_6664]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_14,negated_conjecture,
% 3.06/1.02      ( k1_xboole_0 != k3_tarski(k1_xboole_0) ),
% 3.06/1.02      inference(cnf_transformation,[],[f34]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_150,plain,( X0 = X0 ),theory(equality) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_159,plain,
% 3.06/1.02      ( k1_xboole_0 = k1_xboole_0 ),
% 3.06/1.02      inference(instantiation,[status(thm)],[c_150]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_151,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_481,plain,
% 3.06/1.02      ( k3_tarski(k1_xboole_0) != X0
% 3.06/1.02      | k1_xboole_0 != X0
% 3.06/1.02      | k1_xboole_0 = k3_tarski(k1_xboole_0) ),
% 3.06/1.02      inference(instantiation,[status(thm)],[c_151]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_482,plain,
% 3.06/1.02      ( k3_tarski(k1_xboole_0) != k1_xboole_0
% 3.06/1.02      | k1_xboole_0 = k3_tarski(k1_xboole_0)
% 3.06/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 3.06/1.02      inference(instantiation,[status(thm)],[c_481]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_8530,plain,
% 3.06/1.02      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.06/1.02      inference(global_propositional_subsumption,
% 3.06/1.02                [status(thm)],
% 3.06/1.02                [c_8526,c_14,c_159,c_482]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_8537,plain,
% 3.06/1.02      ( k3_tarski(k1_xboole_0) = X0
% 3.06/1.02      | r2_hidden(sK1(k1_xboole_0,X0),X0) = iProver_top ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_369,c_8530]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(c_9027,plain,
% 3.06/1.02      ( k3_tarski(k1_xboole_0) = k1_xboole_0 ),
% 3.06/1.02      inference(superposition,[status(thm)],[c_8537,c_8530]) ).
% 3.06/1.02  
% 3.06/1.02  cnf(contradiction,plain,
% 3.06/1.02      ( $false ),
% 3.06/1.02      inference(minisat,[status(thm)],[c_9027,c_482,c_159,c_14]) ).
% 3.06/1.02  
% 3.06/1.02  
% 3.06/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.06/1.02  
% 3.06/1.02  ------                               Statistics
% 3.06/1.02  
% 3.06/1.02  ------ General
% 3.06/1.02  
% 3.06/1.02  abstr_ref_over_cycles:                  0
% 3.06/1.02  abstr_ref_under_cycles:                 0
% 3.06/1.02  gc_basic_clause_elim:                   0
% 3.06/1.02  forced_gc_time:                         0
% 3.06/1.02  parsing_time:                           0.008
% 3.06/1.02  unif_index_cands_time:                  0.
% 3.06/1.02  unif_index_add_time:                    0.
% 3.06/1.02  orderings_time:                         0.
% 3.06/1.02  out_proof_time:                         0.008
% 3.06/1.02  total_time:                             0.352
% 3.06/1.02  num_of_symbols:                         39
% 3.06/1.02  num_of_terms:                           11293
% 3.06/1.02  
% 3.06/1.02  ------ Preprocessing
% 3.06/1.02  
% 3.06/1.02  num_of_splits:                          0
% 3.06/1.02  num_of_split_atoms:                     0
% 3.06/1.02  num_of_reused_defs:                     0
% 3.06/1.02  num_eq_ax_congr_red:                    20
% 3.06/1.02  num_of_sem_filtered_clauses:            1
% 3.06/1.02  num_of_subtypes:                        0
% 3.06/1.02  monotx_restored_types:                  0
% 3.06/1.02  sat_num_of_epr_types:                   0
% 3.06/1.02  sat_num_of_non_cyclic_types:            0
% 3.06/1.02  sat_guarded_non_collapsed_types:        0
% 3.06/1.02  num_pure_diseq_elim:                    0
% 3.06/1.02  simp_replaced_by:                       0
% 3.06/1.02  res_preprocessed:                       56
% 3.06/1.02  prep_upred:                             0
% 3.06/1.02  prep_unflattend:                        0
% 3.06/1.02  smt_new_axioms:                         0
% 3.06/1.02  pred_elim_cands:                        1
% 3.06/1.02  pred_elim:                              0
% 3.06/1.02  pred_elim_cl:                           0
% 3.06/1.02  pred_elim_cycles:                       1
% 3.06/1.02  merged_defs:                            0
% 3.06/1.02  merged_defs_ncl:                        0
% 3.06/1.02  bin_hyper_res:                          0
% 3.06/1.02  prep_cycles:                            3
% 3.06/1.02  pred_elim_time:                         0.
% 3.06/1.02  splitting_time:                         0.
% 3.06/1.02  sem_filter_time:                        0.
% 3.06/1.02  monotx_time:                            0.
% 3.06/1.02  subtype_inf_time:                       0.
% 3.06/1.02  
% 3.06/1.02  ------ Problem properties
% 3.06/1.02  
% 3.06/1.02  clauses:                                15
% 3.06/1.02  conjectures:                            1
% 3.06/1.02  epr:                                    1
% 3.06/1.02  horn:                                   11
% 3.06/1.02  ground:                                 1
% 3.06/1.02  unary:                                  2
% 3.06/1.02  binary:                                 5
% 3.06/1.02  lits:                                   38
% 3.06/1.02  lits_eq:                                8
% 3.06/1.02  fd_pure:                                0
% 3.06/1.02  fd_pseudo:                              0
% 3.06/1.02  fd_cond:                                0
% 3.06/1.02  fd_pseudo_cond:                         6
% 3.06/1.02  ac_symbols:                             0
% 3.06/1.02  
% 3.06/1.02  ------ Propositional Solver
% 3.06/1.02  
% 3.06/1.02  prop_solver_calls:                      25
% 3.06/1.02  prop_fast_solver_calls:                 424
% 3.06/1.02  smt_solver_calls:                       0
% 3.06/1.02  smt_fast_solver_calls:                  0
% 3.06/1.02  prop_num_of_clauses:                    3091
% 3.06/1.02  prop_preprocess_simplified:             6651
% 3.06/1.02  prop_fo_subsumed:                       6
% 3.06/1.02  prop_solver_time:                       0.
% 3.06/1.02  smt_solver_time:                        0.
% 3.06/1.02  smt_fast_solver_time:                   0.
% 3.06/1.02  prop_fast_solver_time:                  0.
% 3.06/1.02  prop_unsat_core_time:                   0.
% 3.06/1.02  
% 3.06/1.02  ------ QBF
% 3.06/1.02  
% 3.06/1.02  qbf_q_res:                              0
% 3.06/1.02  qbf_num_tautologies:                    0
% 3.06/1.02  qbf_prep_cycles:                        0
% 3.06/1.02  
% 3.06/1.02  ------ BMC1
% 3.06/1.02  
% 3.06/1.02  bmc1_current_bound:                     -1
% 3.06/1.02  bmc1_last_solved_bound:                 -1
% 3.06/1.02  bmc1_unsat_core_size:                   -1
% 3.06/1.02  bmc1_unsat_core_parents_size:           -1
% 3.06/1.02  bmc1_merge_next_fun:                    0
% 3.06/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.06/1.02  
% 3.06/1.02  ------ Instantiation
% 3.06/1.02  
% 3.06/1.02  inst_num_of_clauses:                    775
% 3.06/1.02  inst_num_in_passive:                    188
% 3.06/1.02  inst_num_in_active:                     223
% 3.06/1.02  inst_num_in_unprocessed:                364
% 3.06/1.02  inst_num_of_loops:                      280
% 3.06/1.02  inst_num_of_learning_restarts:          0
% 3.06/1.02  inst_num_moves_active_passive:          54
% 3.06/1.02  inst_lit_activity:                      0
% 3.06/1.02  inst_lit_activity_moves:                0
% 3.06/1.02  inst_num_tautologies:                   0
% 3.06/1.02  inst_num_prop_implied:                  0
% 3.06/1.02  inst_num_existing_simplified:           0
% 3.06/1.02  inst_num_eq_res_simplified:             0
% 3.06/1.02  inst_num_child_elim:                    0
% 3.06/1.02  inst_num_of_dismatching_blockings:      474
% 3.06/1.02  inst_num_of_non_proper_insts:           464
% 3.06/1.02  inst_num_of_duplicates:                 0
% 3.06/1.02  inst_inst_num_from_inst_to_res:         0
% 3.06/1.02  inst_dismatching_checking_time:         0.
% 3.06/1.02  
% 3.06/1.02  ------ Resolution
% 3.06/1.02  
% 3.06/1.02  res_num_of_clauses:                     0
% 3.06/1.02  res_num_in_passive:                     0
% 3.06/1.02  res_num_in_active:                      0
% 3.06/1.02  res_num_of_loops:                       59
% 3.06/1.02  res_forward_subset_subsumed:            43
% 3.06/1.02  res_backward_subset_subsumed:           0
% 3.06/1.02  res_forward_subsumed:                   0
% 3.06/1.02  res_backward_subsumed:                  0
% 3.06/1.02  res_forward_subsumption_resolution:     0
% 3.06/1.02  res_backward_subsumption_resolution:    0
% 3.06/1.02  res_clause_to_clause_subsumption:       2039
% 3.06/1.02  res_orphan_elimination:                 0
% 3.06/1.02  res_tautology_del:                      49
% 3.06/1.02  res_num_eq_res_simplified:              0
% 3.06/1.02  res_num_sel_changes:                    0
% 3.06/1.02  res_moves_from_active_to_pass:          0
% 3.06/1.02  
% 3.06/1.02  ------ Superposition
% 3.06/1.02  
% 3.06/1.02  sup_time_total:                         0.
% 3.06/1.02  sup_time_generating:                    0.
% 3.06/1.02  sup_time_sim_full:                      0.
% 3.06/1.02  sup_time_sim_immed:                     0.
% 3.06/1.02  
% 3.06/1.02  sup_num_of_clauses:                     356
% 3.06/1.02  sup_num_in_active:                      39
% 3.06/1.02  sup_num_in_passive:                     317
% 3.06/1.02  sup_num_of_loops:                       55
% 3.06/1.02  sup_fw_superposition:                   287
% 3.06/1.02  sup_bw_superposition:                   282
% 3.06/1.02  sup_immediate_simplified:               68
% 3.06/1.02  sup_given_eliminated:                   2
% 3.06/1.02  comparisons_done:                       0
% 3.06/1.02  comparisons_avoided:                    2
% 3.06/1.02  
% 3.06/1.02  ------ Simplifications
% 3.06/1.02  
% 3.06/1.02  
% 3.06/1.02  sim_fw_subset_subsumed:                 22
% 3.06/1.02  sim_bw_subset_subsumed:                 24
% 3.06/1.02  sim_fw_subsumed:                        24
% 3.06/1.02  sim_bw_subsumed:                        4
% 3.06/1.02  sim_fw_subsumption_res:                 0
% 3.06/1.02  sim_bw_subsumption_res:                 0
% 3.06/1.02  sim_tautology_del:                      26
% 3.06/1.02  sim_eq_tautology_del:                   31
% 3.06/1.02  sim_eq_res_simp:                        11
% 3.06/1.02  sim_fw_demodulated:                     7
% 3.06/1.02  sim_bw_demodulated:                     29
% 3.06/1.02  sim_light_normalised:                   17
% 3.06/1.02  sim_joinable_taut:                      0
% 3.06/1.02  sim_joinable_simp:                      0
% 3.06/1.02  sim_ac_normalised:                      0
% 3.06/1.02  sim_smt_subsumption:                    0
% 3.06/1.02  
%------------------------------------------------------------------------------
