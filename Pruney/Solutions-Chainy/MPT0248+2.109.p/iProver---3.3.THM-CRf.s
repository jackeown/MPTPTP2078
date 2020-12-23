%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:32:25 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   78 (1178 expanded)
%              Number of clauses        :   33 ( 145 expanded)
%              Number of leaves         :   11 ( 349 expanded)
%              Depth                    :   14
%              Number of atoms          :  180 (2596 expanded)
%              Number of equality atoms :  137 (2301 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) )
   => ( ( k1_xboole_0 != sK2
        | k1_tarski(sK0) != sK1 )
      & ( k1_tarski(sK0) != sK2
        | k1_xboole_0 != sK1 )
      & ( k1_tarski(sK0) != sK2
        | k1_tarski(sK0) != sK1 )
      & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ( k1_xboole_0 != sK2
      | k1_tarski(sK0) != sK1 )
    & ( k1_tarski(sK0) != sK2
      | k1_xboole_0 != sK1 )
    & ( k1_tarski(sK0) != sK2
      | k1_tarski(sK0) != sK1 )
    & k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f19])).

fof(f34,plain,(
    k2_xboole_0(sK1,sK2) = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f27,f38])).

fof(f50,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f34,f39,f40])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f24,f39])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f17])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f30,f40,f40])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f26,f39])).

fof(f35,plain,
    ( k1_tarski(sK0) != sK2
    | k1_tarski(sK0) != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != sK2
    | k2_enumset1(sK0,sK0,sK0,sK0) != sK1 ),
    inference(definition_unfolding,[],[f35,f40,f40])).

fof(f36,plain,
    ( k1_tarski(sK0) != sK2
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != sK2
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f36,f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f39])).

fof(f37,plain,
    ( k1_xboole_0 != sK2
    | k1_tarski(sK0) != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,
    ( k1_xboole_0 != sK2
    | k2_enumset1(sK0,sK0,sK0,sK0) != sK1 ),
    inference(definition_unfolding,[],[f37,f40])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_305,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12,negated_conjecture,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_304,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_797,plain,
    ( r1_tarski(X0,k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_304])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_299,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_815,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = X0
    | k1_xboole_0 = X0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_797,c_299])).

cnf(c_1701,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_305,c_815])).

cnf(c_5,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_302,plain,
    ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_588,plain,
    ( r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_302])).

cnf(c_693,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_588,c_299])).

cnf(c_11,negated_conjecture,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != sK1
    | k2_enumset1(sK0,sK0,sK0,sK0) != sK2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1170,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != sK2
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_693,c_11])).

cnf(c_10,negated_conjecture,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != sK2
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_589,plain,
    ( r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_588])).

cnf(c_1254,plain,
    ( ~ r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | k2_enumset1(sK0,sK0,sK0,sK0) = sK1
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1345,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1170,c_11,c_10,c_589,c_1254])).

cnf(c_2368,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1701,c_11,c_10,c_589,c_1254])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_303,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_701,plain,
    ( k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
    inference(superposition,[status(thm)],[c_305,c_303])).

cnf(c_1423,plain,
    ( k3_tarski(sK1) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_693,c_701])).

cnf(c_9,negated_conjecture,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != sK1
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1172,plain,
    ( sK1 = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_693,c_9])).

cnf(c_1939,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1423,c_11,c_10,c_589,c_1172,c_1254,c_1701])).

cnf(c_1950,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_1939,c_12])).

cnf(c_2372,plain,
    ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(demodulation,[status(thm)],[c_2368,c_1950])).

cnf(c_2412,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2372,c_701])).

cnf(c_1949,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1939,c_9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2412,c_1949,c_1701,c_1345])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.31  % Computer   : n011.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 20:24:27 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.16/0.31  % Running in FOF mode
% 1.76/0.95  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/0.95  
% 1.76/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.76/0.95  
% 1.76/0.95  ------  iProver source info
% 1.76/0.95  
% 1.76/0.95  git: date: 2020-06-30 10:37:57 +0100
% 1.76/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.76/0.95  git: non_committed_changes: false
% 1.76/0.95  git: last_make_outside_of_git: false
% 1.76/0.95  
% 1.76/0.95  ------ 
% 1.76/0.95  
% 1.76/0.95  ------ Input Options
% 1.76/0.95  
% 1.76/0.95  --out_options                           all
% 1.76/0.95  --tptp_safe_out                         true
% 1.76/0.95  --problem_path                          ""
% 1.76/0.95  --include_path                          ""
% 1.76/0.95  --clausifier                            res/vclausify_rel
% 1.76/0.95  --clausifier_options                    --mode clausify
% 1.76/0.95  --stdin                                 false
% 1.76/0.95  --stats_out                             all
% 1.76/0.95  
% 1.76/0.95  ------ General Options
% 1.76/0.95  
% 1.76/0.95  --fof                                   false
% 1.76/0.95  --time_out_real                         305.
% 1.76/0.95  --time_out_virtual                      -1.
% 1.76/0.95  --symbol_type_check                     false
% 1.76/0.95  --clausify_out                          false
% 1.76/0.95  --sig_cnt_out                           false
% 1.76/0.95  --trig_cnt_out                          false
% 1.76/0.95  --trig_cnt_out_tolerance                1.
% 1.76/0.95  --trig_cnt_out_sk_spl                   false
% 1.76/0.95  --abstr_cl_out                          false
% 1.76/0.95  
% 1.76/0.95  ------ Global Options
% 1.76/0.95  
% 1.76/0.95  --schedule                              default
% 1.76/0.95  --add_important_lit                     false
% 1.76/0.95  --prop_solver_per_cl                    1000
% 1.76/0.95  --min_unsat_core                        false
% 1.76/0.95  --soft_assumptions                      false
% 1.76/0.95  --soft_lemma_size                       3
% 1.76/0.95  --prop_impl_unit_size                   0
% 1.76/0.95  --prop_impl_unit                        []
% 1.76/0.95  --share_sel_clauses                     true
% 1.76/0.95  --reset_solvers                         false
% 1.76/0.95  --bc_imp_inh                            [conj_cone]
% 1.76/0.95  --conj_cone_tolerance                   3.
% 1.76/0.95  --extra_neg_conj                        none
% 1.76/0.95  --large_theory_mode                     true
% 1.76/0.95  --prolific_symb_bound                   200
% 1.76/0.95  --lt_threshold                          2000
% 1.76/0.95  --clause_weak_htbl                      true
% 1.76/0.95  --gc_record_bc_elim                     false
% 1.76/0.95  
% 1.76/0.95  ------ Preprocessing Options
% 1.76/0.95  
% 1.76/0.95  --preprocessing_flag                    true
% 1.76/0.95  --time_out_prep_mult                    0.1
% 1.76/0.95  --splitting_mode                        input
% 1.76/0.95  --splitting_grd                         true
% 1.76/0.95  --splitting_cvd                         false
% 1.76/0.95  --splitting_cvd_svl                     false
% 1.76/0.95  --splitting_nvd                         32
% 1.76/0.95  --sub_typing                            true
% 1.76/0.95  --prep_gs_sim                           true
% 1.76/0.95  --prep_unflatten                        true
% 1.76/0.95  --prep_res_sim                          true
% 1.76/0.95  --prep_upred                            true
% 1.76/0.95  --prep_sem_filter                       exhaustive
% 1.76/0.95  --prep_sem_filter_out                   false
% 1.76/0.95  --pred_elim                             true
% 1.76/0.95  --res_sim_input                         true
% 1.76/0.95  --eq_ax_congr_red                       true
% 1.76/0.95  --pure_diseq_elim                       true
% 1.76/0.95  --brand_transform                       false
% 1.76/0.95  --non_eq_to_eq                          false
% 1.76/0.95  --prep_def_merge                        true
% 1.76/0.95  --prep_def_merge_prop_impl              false
% 1.76/0.95  --prep_def_merge_mbd                    true
% 1.76/0.95  --prep_def_merge_tr_red                 false
% 1.76/0.95  --prep_def_merge_tr_cl                  false
% 1.76/0.95  --smt_preprocessing                     true
% 1.76/0.95  --smt_ac_axioms                         fast
% 1.76/0.95  --preprocessed_out                      false
% 1.76/0.95  --preprocessed_stats                    false
% 1.76/0.95  
% 1.76/0.95  ------ Abstraction refinement Options
% 1.76/0.95  
% 1.76/0.95  --abstr_ref                             []
% 1.76/0.95  --abstr_ref_prep                        false
% 1.76/0.95  --abstr_ref_until_sat                   false
% 1.76/0.95  --abstr_ref_sig_restrict                funpre
% 1.76/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 1.76/0.95  --abstr_ref_under                       []
% 1.76/0.95  
% 1.76/0.95  ------ SAT Options
% 1.76/0.95  
% 1.76/0.95  --sat_mode                              false
% 1.76/0.95  --sat_fm_restart_options                ""
% 1.76/0.95  --sat_gr_def                            false
% 1.76/0.95  --sat_epr_types                         true
% 1.76/0.95  --sat_non_cyclic_types                  false
% 1.76/0.95  --sat_finite_models                     false
% 1.76/0.95  --sat_fm_lemmas                         false
% 1.76/0.95  --sat_fm_prep                           false
% 1.76/0.95  --sat_fm_uc_incr                        true
% 1.76/0.95  --sat_out_model                         small
% 1.76/0.95  --sat_out_clauses                       false
% 1.76/0.95  
% 1.76/0.95  ------ QBF Options
% 1.76/0.95  
% 1.76/0.95  --qbf_mode                              false
% 1.76/0.95  --qbf_elim_univ                         false
% 1.76/0.95  --qbf_dom_inst                          none
% 1.76/0.95  --qbf_dom_pre_inst                      false
% 1.76/0.95  --qbf_sk_in                             false
% 1.76/0.95  --qbf_pred_elim                         true
% 1.76/0.95  --qbf_split                             512
% 1.76/0.95  
% 1.76/0.95  ------ BMC1 Options
% 1.76/0.95  
% 1.76/0.95  --bmc1_incremental                      false
% 1.76/0.95  --bmc1_axioms                           reachable_all
% 1.76/0.95  --bmc1_min_bound                        0
% 1.76/0.95  --bmc1_max_bound                        -1
% 1.76/0.95  --bmc1_max_bound_default                -1
% 1.76/0.95  --bmc1_symbol_reachability              true
% 1.76/0.95  --bmc1_property_lemmas                  false
% 1.76/0.95  --bmc1_k_induction                      false
% 1.76/0.95  --bmc1_non_equiv_states                 false
% 1.76/0.95  --bmc1_deadlock                         false
% 1.76/0.95  --bmc1_ucm                              false
% 1.76/0.95  --bmc1_add_unsat_core                   none
% 1.76/0.95  --bmc1_unsat_core_children              false
% 1.76/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 1.76/0.95  --bmc1_out_stat                         full
% 1.76/0.95  --bmc1_ground_init                      false
% 1.76/0.95  --bmc1_pre_inst_next_state              false
% 1.76/0.95  --bmc1_pre_inst_state                   false
% 1.76/0.95  --bmc1_pre_inst_reach_state             false
% 1.76/0.95  --bmc1_out_unsat_core                   false
% 1.76/0.95  --bmc1_aig_witness_out                  false
% 1.76/0.95  --bmc1_verbose                          false
% 1.76/0.95  --bmc1_dump_clauses_tptp                false
% 1.76/0.95  --bmc1_dump_unsat_core_tptp             false
% 1.76/0.95  --bmc1_dump_file                        -
% 1.76/0.95  --bmc1_ucm_expand_uc_limit              128
% 1.76/0.95  --bmc1_ucm_n_expand_iterations          6
% 1.76/0.95  --bmc1_ucm_extend_mode                  1
% 1.76/0.95  --bmc1_ucm_init_mode                    2
% 1.76/0.95  --bmc1_ucm_cone_mode                    none
% 1.76/0.95  --bmc1_ucm_reduced_relation_type        0
% 1.76/0.95  --bmc1_ucm_relax_model                  4
% 1.76/0.95  --bmc1_ucm_full_tr_after_sat            true
% 1.76/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 1.76/0.95  --bmc1_ucm_layered_model                none
% 1.76/0.95  --bmc1_ucm_max_lemma_size               10
% 1.76/0.95  
% 1.76/0.95  ------ AIG Options
% 1.76/0.95  
% 1.76/0.95  --aig_mode                              false
% 1.76/0.95  
% 1.76/0.95  ------ Instantiation Options
% 1.76/0.95  
% 1.76/0.95  --instantiation_flag                    true
% 1.76/0.95  --inst_sos_flag                         false
% 1.76/0.95  --inst_sos_phase                        true
% 1.76/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.76/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.76/0.95  --inst_lit_sel_side                     num_symb
% 1.76/0.95  --inst_solver_per_active                1400
% 1.76/0.95  --inst_solver_calls_frac                1.
% 1.76/0.95  --inst_passive_queue_type               priority_queues
% 1.76/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.76/0.95  --inst_passive_queues_freq              [25;2]
% 1.76/0.95  --inst_dismatching                      true
% 1.76/0.95  --inst_eager_unprocessed_to_passive     true
% 1.76/0.95  --inst_prop_sim_given                   true
% 1.76/0.95  --inst_prop_sim_new                     false
% 1.76/0.95  --inst_subs_new                         false
% 1.76/0.95  --inst_eq_res_simp                      false
% 1.76/0.95  --inst_subs_given                       false
% 1.76/0.95  --inst_orphan_elimination               true
% 1.76/0.95  --inst_learning_loop_flag               true
% 1.76/0.95  --inst_learning_start                   3000
% 1.76/0.95  --inst_learning_factor                  2
% 1.76/0.95  --inst_start_prop_sim_after_learn       3
% 1.76/0.95  --inst_sel_renew                        solver
% 1.76/0.95  --inst_lit_activity_flag                true
% 1.76/0.95  --inst_restr_to_given                   false
% 1.76/0.95  --inst_activity_threshold               500
% 1.76/0.95  --inst_out_proof                        true
% 1.76/0.95  
% 1.76/0.95  ------ Resolution Options
% 1.76/0.95  
% 1.76/0.95  --resolution_flag                       true
% 1.76/0.95  --res_lit_sel                           adaptive
% 1.76/0.95  --res_lit_sel_side                      none
% 1.76/0.95  --res_ordering                          kbo
% 1.76/0.95  --res_to_prop_solver                    active
% 1.76/0.95  --res_prop_simpl_new                    false
% 1.76/0.95  --res_prop_simpl_given                  true
% 1.76/0.95  --res_passive_queue_type                priority_queues
% 1.76/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.76/0.95  --res_passive_queues_freq               [15;5]
% 1.76/0.95  --res_forward_subs                      full
% 1.76/0.95  --res_backward_subs                     full
% 1.76/0.95  --res_forward_subs_resolution           true
% 1.76/0.95  --res_backward_subs_resolution          true
% 1.76/0.95  --res_orphan_elimination                true
% 1.76/0.95  --res_time_limit                        2.
% 1.76/0.95  --res_out_proof                         true
% 1.76/0.95  
% 1.76/0.95  ------ Superposition Options
% 1.76/0.95  
% 1.76/0.95  --superposition_flag                    true
% 1.76/0.95  --sup_passive_queue_type                priority_queues
% 1.76/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.76/0.95  --sup_passive_queues_freq               [8;1;4]
% 1.76/0.95  --demod_completeness_check              fast
% 1.76/0.95  --demod_use_ground                      true
% 1.76/0.95  --sup_to_prop_solver                    passive
% 1.76/0.95  --sup_prop_simpl_new                    true
% 1.76/0.95  --sup_prop_simpl_given                  true
% 1.76/0.95  --sup_fun_splitting                     false
% 1.76/0.95  --sup_smt_interval                      50000
% 1.76/0.95  
% 1.76/0.95  ------ Superposition Simplification Setup
% 1.76/0.95  
% 1.76/0.95  --sup_indices_passive                   []
% 1.76/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 1.76/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.95  --sup_full_bw                           [BwDemod]
% 1.76/0.95  --sup_immed_triv                        [TrivRules]
% 1.76/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.76/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.95  --sup_immed_bw_main                     []
% 1.76/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 1.76/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/0.95  
% 1.76/0.95  ------ Combination Options
% 1.76/0.95  
% 1.76/0.95  --comb_res_mult                         3
% 1.76/0.95  --comb_sup_mult                         2
% 1.76/0.95  --comb_inst_mult                        10
% 1.76/0.95  
% 1.76/0.95  ------ Debug Options
% 1.76/0.95  
% 1.76/0.95  --dbg_backtrace                         false
% 1.76/0.95  --dbg_dump_prop_clauses                 false
% 1.76/0.95  --dbg_dump_prop_clauses_file            -
% 1.76/0.95  --dbg_out_stat                          false
% 1.76/0.95  ------ Parsing...
% 1.76/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.76/0.95  
% 1.76/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.76/0.95  
% 1.76/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.76/0.95  
% 1.76/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.76/0.95  ------ Proving...
% 1.76/0.95  ------ Problem Properties 
% 1.76/0.95  
% 1.76/0.95  
% 1.76/0.95  clauses                                 12
% 1.76/0.95  conjectures                             4
% 1.76/0.95  EPR                                     2
% 1.76/0.95  Horn                                    11
% 1.76/0.95  unary                                   5
% 1.76/0.95  binary                                  5
% 1.76/0.95  lits                                    21
% 1.76/0.95  lits eq                                 11
% 1.76/0.95  fd_pure                                 0
% 1.76/0.95  fd_pseudo                               0
% 1.76/0.95  fd_cond                                 0
% 1.76/0.95  fd_pseudo_cond                          2
% 1.76/0.95  AC symbols                              0
% 1.76/0.95  
% 1.76/0.95  ------ Schedule dynamic 5 is on 
% 1.76/0.95  
% 1.76/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.76/0.95  
% 1.76/0.95  
% 1.76/0.95  ------ 
% 1.76/0.95  Current options:
% 1.76/0.95  ------ 
% 1.76/0.95  
% 1.76/0.95  ------ Input Options
% 1.76/0.95  
% 1.76/0.95  --out_options                           all
% 1.76/0.95  --tptp_safe_out                         true
% 1.76/0.95  --problem_path                          ""
% 1.76/0.95  --include_path                          ""
% 1.76/0.95  --clausifier                            res/vclausify_rel
% 1.76/0.95  --clausifier_options                    --mode clausify
% 1.76/0.95  --stdin                                 false
% 1.76/0.95  --stats_out                             all
% 1.76/0.95  
% 1.76/0.95  ------ General Options
% 1.76/0.95  
% 1.76/0.95  --fof                                   false
% 1.76/0.95  --time_out_real                         305.
% 1.76/0.95  --time_out_virtual                      -1.
% 1.76/0.95  --symbol_type_check                     false
% 1.76/0.95  --clausify_out                          false
% 1.76/0.95  --sig_cnt_out                           false
% 1.76/0.95  --trig_cnt_out                          false
% 1.76/0.95  --trig_cnt_out_tolerance                1.
% 1.76/0.95  --trig_cnt_out_sk_spl                   false
% 1.76/0.95  --abstr_cl_out                          false
% 1.76/0.95  
% 1.76/0.95  ------ Global Options
% 1.76/0.95  
% 1.76/0.95  --schedule                              default
% 1.76/0.95  --add_important_lit                     false
% 1.76/0.95  --prop_solver_per_cl                    1000
% 1.76/0.95  --min_unsat_core                        false
% 1.76/0.95  --soft_assumptions                      false
% 1.76/0.95  --soft_lemma_size                       3
% 1.76/0.95  --prop_impl_unit_size                   0
% 1.76/0.95  --prop_impl_unit                        []
% 1.76/0.95  --share_sel_clauses                     true
% 1.76/0.95  --reset_solvers                         false
% 1.76/0.95  --bc_imp_inh                            [conj_cone]
% 1.76/0.95  --conj_cone_tolerance                   3.
% 1.76/0.95  --extra_neg_conj                        none
% 1.76/0.95  --large_theory_mode                     true
% 1.76/0.95  --prolific_symb_bound                   200
% 1.76/0.95  --lt_threshold                          2000
% 1.76/0.95  --clause_weak_htbl                      true
% 1.76/0.95  --gc_record_bc_elim                     false
% 1.76/0.95  
% 1.76/0.95  ------ Preprocessing Options
% 1.76/0.95  
% 1.76/0.95  --preprocessing_flag                    true
% 1.76/0.95  --time_out_prep_mult                    0.1
% 1.76/0.95  --splitting_mode                        input
% 1.76/0.95  --splitting_grd                         true
% 1.76/0.95  --splitting_cvd                         false
% 1.76/0.95  --splitting_cvd_svl                     false
% 1.76/0.95  --splitting_nvd                         32
% 1.76/0.95  --sub_typing                            true
% 1.76/0.95  --prep_gs_sim                           true
% 1.76/0.95  --prep_unflatten                        true
% 1.76/0.95  --prep_res_sim                          true
% 1.76/0.95  --prep_upred                            true
% 1.76/0.95  --prep_sem_filter                       exhaustive
% 1.76/0.95  --prep_sem_filter_out                   false
% 1.76/0.95  --pred_elim                             true
% 1.76/0.95  --res_sim_input                         true
% 1.76/0.95  --eq_ax_congr_red                       true
% 1.76/0.95  --pure_diseq_elim                       true
% 1.76/0.95  --brand_transform                       false
% 1.76/0.95  --non_eq_to_eq                          false
% 1.76/0.95  --prep_def_merge                        true
% 1.76/0.95  --prep_def_merge_prop_impl              false
% 1.76/0.95  --prep_def_merge_mbd                    true
% 1.76/0.95  --prep_def_merge_tr_red                 false
% 1.76/0.95  --prep_def_merge_tr_cl                  false
% 1.76/0.95  --smt_preprocessing                     true
% 1.76/0.95  --smt_ac_axioms                         fast
% 1.76/0.95  --preprocessed_out                      false
% 1.76/0.95  --preprocessed_stats                    false
% 1.76/0.95  
% 1.76/0.95  ------ Abstraction refinement Options
% 1.76/0.95  
% 1.76/0.95  --abstr_ref                             []
% 1.76/0.95  --abstr_ref_prep                        false
% 1.76/0.95  --abstr_ref_until_sat                   false
% 1.76/0.95  --abstr_ref_sig_restrict                funpre
% 1.76/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 1.76/0.95  --abstr_ref_under                       []
% 1.76/0.95  
% 1.76/0.95  ------ SAT Options
% 1.76/0.95  
% 1.76/0.95  --sat_mode                              false
% 1.76/0.95  --sat_fm_restart_options                ""
% 1.76/0.95  --sat_gr_def                            false
% 1.76/0.95  --sat_epr_types                         true
% 1.76/0.95  --sat_non_cyclic_types                  false
% 1.76/0.95  --sat_finite_models                     false
% 1.76/0.95  --sat_fm_lemmas                         false
% 1.76/0.95  --sat_fm_prep                           false
% 1.76/0.95  --sat_fm_uc_incr                        true
% 1.76/0.95  --sat_out_model                         small
% 1.76/0.95  --sat_out_clauses                       false
% 1.76/0.95  
% 1.76/0.95  ------ QBF Options
% 1.76/0.95  
% 1.76/0.95  --qbf_mode                              false
% 1.76/0.95  --qbf_elim_univ                         false
% 1.76/0.95  --qbf_dom_inst                          none
% 1.76/0.95  --qbf_dom_pre_inst                      false
% 1.76/0.95  --qbf_sk_in                             false
% 1.76/0.95  --qbf_pred_elim                         true
% 1.76/0.95  --qbf_split                             512
% 1.76/0.95  
% 1.76/0.95  ------ BMC1 Options
% 1.76/0.95  
% 1.76/0.95  --bmc1_incremental                      false
% 1.76/0.95  --bmc1_axioms                           reachable_all
% 1.76/0.95  --bmc1_min_bound                        0
% 1.76/0.95  --bmc1_max_bound                        -1
% 1.76/0.95  --bmc1_max_bound_default                -1
% 1.76/0.95  --bmc1_symbol_reachability              true
% 1.76/0.95  --bmc1_property_lemmas                  false
% 1.76/0.95  --bmc1_k_induction                      false
% 1.76/0.95  --bmc1_non_equiv_states                 false
% 1.76/0.95  --bmc1_deadlock                         false
% 1.76/0.95  --bmc1_ucm                              false
% 1.76/0.95  --bmc1_add_unsat_core                   none
% 1.76/0.95  --bmc1_unsat_core_children              false
% 1.76/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 1.76/0.95  --bmc1_out_stat                         full
% 1.76/0.95  --bmc1_ground_init                      false
% 1.76/0.95  --bmc1_pre_inst_next_state              false
% 1.76/0.95  --bmc1_pre_inst_state                   false
% 1.76/0.95  --bmc1_pre_inst_reach_state             false
% 1.76/0.95  --bmc1_out_unsat_core                   false
% 1.76/0.95  --bmc1_aig_witness_out                  false
% 1.76/0.95  --bmc1_verbose                          false
% 1.76/0.95  --bmc1_dump_clauses_tptp                false
% 1.76/0.95  --bmc1_dump_unsat_core_tptp             false
% 1.76/0.95  --bmc1_dump_file                        -
% 1.76/0.95  --bmc1_ucm_expand_uc_limit              128
% 1.76/0.95  --bmc1_ucm_n_expand_iterations          6
% 1.76/0.95  --bmc1_ucm_extend_mode                  1
% 1.76/0.95  --bmc1_ucm_init_mode                    2
% 1.76/0.95  --bmc1_ucm_cone_mode                    none
% 1.76/0.95  --bmc1_ucm_reduced_relation_type        0
% 1.76/0.95  --bmc1_ucm_relax_model                  4
% 1.76/0.95  --bmc1_ucm_full_tr_after_sat            true
% 1.76/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 1.76/0.95  --bmc1_ucm_layered_model                none
% 1.76/0.95  --bmc1_ucm_max_lemma_size               10
% 1.76/0.95  
% 1.76/0.95  ------ AIG Options
% 1.76/0.95  
% 1.76/0.95  --aig_mode                              false
% 1.76/0.95  
% 1.76/0.95  ------ Instantiation Options
% 1.76/0.95  
% 1.76/0.95  --instantiation_flag                    true
% 1.76/0.95  --inst_sos_flag                         false
% 1.76/0.95  --inst_sos_phase                        true
% 1.76/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.76/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.76/0.95  --inst_lit_sel_side                     none
% 1.76/0.95  --inst_solver_per_active                1400
% 1.76/0.95  --inst_solver_calls_frac                1.
% 1.76/0.95  --inst_passive_queue_type               priority_queues
% 1.76/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.76/0.95  --inst_passive_queues_freq              [25;2]
% 1.76/0.95  --inst_dismatching                      true
% 1.76/0.95  --inst_eager_unprocessed_to_passive     true
% 1.76/0.95  --inst_prop_sim_given                   true
% 1.76/0.95  --inst_prop_sim_new                     false
% 1.76/0.95  --inst_subs_new                         false
% 1.76/0.95  --inst_eq_res_simp                      false
% 1.76/0.95  --inst_subs_given                       false
% 1.76/0.95  --inst_orphan_elimination               true
% 1.76/0.95  --inst_learning_loop_flag               true
% 1.76/0.95  --inst_learning_start                   3000
% 1.76/0.95  --inst_learning_factor                  2
% 1.76/0.95  --inst_start_prop_sim_after_learn       3
% 1.76/0.95  --inst_sel_renew                        solver
% 1.76/0.95  --inst_lit_activity_flag                true
% 1.76/0.95  --inst_restr_to_given                   false
% 1.76/0.95  --inst_activity_threshold               500
% 1.76/0.95  --inst_out_proof                        true
% 1.76/0.95  
% 1.76/0.95  ------ Resolution Options
% 1.76/0.95  
% 1.76/0.95  --resolution_flag                       false
% 1.76/0.95  --res_lit_sel                           adaptive
% 1.76/0.95  --res_lit_sel_side                      none
% 1.76/0.95  --res_ordering                          kbo
% 1.76/0.95  --res_to_prop_solver                    active
% 1.76/0.95  --res_prop_simpl_new                    false
% 1.76/0.95  --res_prop_simpl_given                  true
% 1.76/0.95  --res_passive_queue_type                priority_queues
% 1.76/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.76/0.95  --res_passive_queues_freq               [15;5]
% 1.76/0.95  --res_forward_subs                      full
% 1.76/0.95  --res_backward_subs                     full
% 1.76/0.95  --res_forward_subs_resolution           true
% 1.76/0.95  --res_backward_subs_resolution          true
% 1.76/0.95  --res_orphan_elimination                true
% 1.76/0.95  --res_time_limit                        2.
% 1.76/0.95  --res_out_proof                         true
% 1.76/0.95  
% 1.76/0.95  ------ Superposition Options
% 1.76/0.95  
% 1.76/0.95  --superposition_flag                    true
% 1.76/0.95  --sup_passive_queue_type                priority_queues
% 1.76/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.76/0.95  --sup_passive_queues_freq               [8;1;4]
% 1.76/0.95  --demod_completeness_check              fast
% 1.76/0.95  --demod_use_ground                      true
% 1.76/0.95  --sup_to_prop_solver                    passive
% 1.76/0.95  --sup_prop_simpl_new                    true
% 1.76/0.95  --sup_prop_simpl_given                  true
% 1.76/0.95  --sup_fun_splitting                     false
% 1.76/0.95  --sup_smt_interval                      50000
% 1.76/0.95  
% 1.76/0.95  ------ Superposition Simplification Setup
% 1.76/0.95  
% 1.76/0.95  --sup_indices_passive                   []
% 1.76/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.76/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 1.76/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.95  --sup_full_bw                           [BwDemod]
% 1.76/0.95  --sup_immed_triv                        [TrivRules]
% 1.76/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.76/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.95  --sup_immed_bw_main                     []
% 1.76/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 1.76/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.76/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.76/0.95  
% 1.76/0.95  ------ Combination Options
% 1.76/0.95  
% 1.76/0.95  --comb_res_mult                         3
% 1.76/0.95  --comb_sup_mult                         2
% 1.76/0.95  --comb_inst_mult                        10
% 1.76/0.95  
% 1.76/0.95  ------ Debug Options
% 1.76/0.95  
% 1.76/0.95  --dbg_backtrace                         false
% 1.76/0.95  --dbg_dump_prop_clauses                 false
% 1.76/0.95  --dbg_dump_prop_clauses_file            -
% 1.76/0.95  --dbg_out_stat                          false
% 1.76/0.95  
% 1.76/0.95  
% 1.76/0.95  
% 1.76/0.95  
% 1.76/0.95  ------ Proving...
% 1.76/0.95  
% 1.76/0.95  
% 1.76/0.95  % SZS status Theorem for theBenchmark.p
% 1.76/0.95  
% 1.76/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 1.76/0.95  
% 1.76/0.95  fof(f1,axiom,(
% 1.76/0.95    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.76/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.95  
% 1.76/0.95  fof(f15,plain,(
% 1.76/0.95    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.76/0.95    inference(nnf_transformation,[],[f1])).
% 1.76/0.95  
% 1.76/0.95  fof(f16,plain,(
% 1.76/0.95    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.76/0.95    inference(flattening,[],[f15])).
% 1.76/0.95  
% 1.76/0.95  fof(f21,plain,(
% 1.76/0.95    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.76/0.95    inference(cnf_transformation,[],[f16])).
% 1.76/0.95  
% 1.76/0.95  fof(f52,plain,(
% 1.76/0.95    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.76/0.95    inference(equality_resolution,[],[f21])).
% 1.76/0.95  
% 1.76/0.95  fof(f10,conjecture,(
% 1.76/0.95    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.76/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.95  
% 1.76/0.95  fof(f11,negated_conjecture,(
% 1.76/0.95    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.76/0.95    inference(negated_conjecture,[],[f10])).
% 1.76/0.95  
% 1.76/0.95  fof(f14,plain,(
% 1.76/0.95    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.76/0.95    inference(ennf_transformation,[],[f11])).
% 1.76/0.95  
% 1.76/0.95  fof(f19,plain,(
% 1.76/0.95    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k2_xboole_0(X1,X2) = k1_tarski(X0)) => ((k1_xboole_0 != sK2 | k1_tarski(sK0) != sK1) & (k1_tarski(sK0) != sK2 | k1_xboole_0 != sK1) & (k1_tarski(sK0) != sK2 | k1_tarski(sK0) != sK1) & k2_xboole_0(sK1,sK2) = k1_tarski(sK0))),
% 1.76/0.95    introduced(choice_axiom,[])).
% 1.76/0.95  
% 1.76/0.95  fof(f20,plain,(
% 1.76/0.95    (k1_xboole_0 != sK2 | k1_tarski(sK0) != sK1) & (k1_tarski(sK0) != sK2 | k1_xboole_0 != sK1) & (k1_tarski(sK0) != sK2 | k1_tarski(sK0) != sK1) & k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 1.76/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f19])).
% 1.76/0.95  
% 1.76/0.95  fof(f34,plain,(
% 1.76/0.95    k2_xboole_0(sK1,sK2) = k1_tarski(sK0)),
% 1.76/0.95    inference(cnf_transformation,[],[f20])).
% 1.76/0.95  
% 1.76/0.95  fof(f9,axiom,(
% 1.76/0.95    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.76/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.95  
% 1.76/0.95  fof(f33,plain,(
% 1.76/0.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.76/0.95    inference(cnf_transformation,[],[f9])).
% 1.76/0.95  
% 1.76/0.95  fof(f39,plain,(
% 1.76/0.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.76/0.95    inference(definition_unfolding,[],[f33,f38])).
% 1.76/0.95  
% 1.76/0.95  fof(f5,axiom,(
% 1.76/0.95    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.76/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.95  
% 1.76/0.95  fof(f27,plain,(
% 1.76/0.95    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.76/0.95    inference(cnf_transformation,[],[f5])).
% 1.76/0.95  
% 1.76/0.95  fof(f6,axiom,(
% 1.76/0.95    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.76/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.95  
% 1.76/0.95  fof(f28,plain,(
% 1.76/0.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.76/0.95    inference(cnf_transformation,[],[f6])).
% 1.76/0.95  
% 1.76/0.95  fof(f7,axiom,(
% 1.76/0.95    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.76/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.95  
% 1.76/0.95  fof(f29,plain,(
% 1.76/0.95    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.76/0.95    inference(cnf_transformation,[],[f7])).
% 1.76/0.95  
% 1.76/0.95  fof(f38,plain,(
% 1.76/0.95    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.76/0.95    inference(definition_unfolding,[],[f28,f29])).
% 1.76/0.95  
% 1.76/0.95  fof(f40,plain,(
% 1.76/0.95    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.76/0.95    inference(definition_unfolding,[],[f27,f38])).
% 1.76/0.95  
% 1.76/0.95  fof(f50,plain,(
% 1.76/0.95    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.76/0.95    inference(definition_unfolding,[],[f34,f39,f40])).
% 1.76/0.95  
% 1.76/0.95  fof(f2,axiom,(
% 1.76/0.95    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.76/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.95  
% 1.76/0.95  fof(f12,plain,(
% 1.76/0.95    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.76/0.95    inference(ennf_transformation,[],[f2])).
% 1.76/0.95  
% 1.76/0.95  fof(f24,plain,(
% 1.76/0.95    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.76/0.95    inference(cnf_transformation,[],[f12])).
% 1.76/0.95  
% 1.76/0.95  fof(f41,plain,(
% 1.76/0.95    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 1.76/0.95    inference(definition_unfolding,[],[f24,f39])).
% 1.76/0.95  
% 1.76/0.95  fof(f8,axiom,(
% 1.76/0.95    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.76/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.95  
% 1.76/0.95  fof(f17,plain,(
% 1.76/0.95    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.76/0.95    inference(nnf_transformation,[],[f8])).
% 1.76/0.95  
% 1.76/0.95  fof(f18,plain,(
% 1.76/0.95    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.76/0.95    inference(flattening,[],[f17])).
% 1.76/0.95  
% 1.76/0.95  fof(f30,plain,(
% 1.76/0.95    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.76/0.95    inference(cnf_transformation,[],[f18])).
% 1.76/0.95  
% 1.76/0.95  fof(f46,plain,(
% 1.76/0.95    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.76/0.95    inference(definition_unfolding,[],[f30,f40,f40])).
% 1.76/0.95  
% 1.76/0.95  fof(f4,axiom,(
% 1.76/0.95    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.76/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.95  
% 1.76/0.95  fof(f26,plain,(
% 1.76/0.95    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.76/0.95    inference(cnf_transformation,[],[f4])).
% 1.76/0.95  
% 1.76/0.95  fof(f43,plain,(
% 1.76/0.95    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.76/0.95    inference(definition_unfolding,[],[f26,f39])).
% 1.76/0.95  
% 1.76/0.95  fof(f35,plain,(
% 1.76/0.95    k1_tarski(sK0) != sK2 | k1_tarski(sK0) != sK1),
% 1.76/0.95    inference(cnf_transformation,[],[f20])).
% 1.76/0.95  
% 1.76/0.95  fof(f49,plain,(
% 1.76/0.95    k2_enumset1(sK0,sK0,sK0,sK0) != sK2 | k2_enumset1(sK0,sK0,sK0,sK0) != sK1),
% 1.76/0.95    inference(definition_unfolding,[],[f35,f40,f40])).
% 1.76/0.95  
% 1.76/0.95  fof(f36,plain,(
% 1.76/0.95    k1_tarski(sK0) != sK2 | k1_xboole_0 != sK1),
% 1.76/0.95    inference(cnf_transformation,[],[f20])).
% 1.76/0.95  
% 1.76/0.95  fof(f48,plain,(
% 1.76/0.95    k2_enumset1(sK0,sK0,sK0,sK0) != sK2 | k1_xboole_0 != sK1),
% 1.76/0.95    inference(definition_unfolding,[],[f36,f40])).
% 1.76/0.95  
% 1.76/0.95  fof(f3,axiom,(
% 1.76/0.95    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.76/0.95    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.76/0.95  
% 1.76/0.95  fof(f13,plain,(
% 1.76/0.95    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.76/0.95    inference(ennf_transformation,[],[f3])).
% 1.76/0.95  
% 1.76/0.95  fof(f25,plain,(
% 1.76/0.95    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.76/0.95    inference(cnf_transformation,[],[f13])).
% 1.76/0.95  
% 1.76/0.95  fof(f42,plain,(
% 1.76/0.95    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.76/0.95    inference(definition_unfolding,[],[f25,f39])).
% 1.76/0.95  
% 1.76/0.95  fof(f37,plain,(
% 1.76/0.95    k1_xboole_0 != sK2 | k1_tarski(sK0) != sK1),
% 1.76/0.95    inference(cnf_transformation,[],[f20])).
% 1.76/0.95  
% 1.76/0.95  fof(f47,plain,(
% 1.76/0.95    k1_xboole_0 != sK2 | k2_enumset1(sK0,sK0,sK0,sK0) != sK1),
% 1.76/0.95    inference(definition_unfolding,[],[f37,f40])).
% 1.76/0.95  
% 1.76/0.95  cnf(c_2,plain,
% 1.76/0.95      ( r1_tarski(X0,X0) ),
% 1.76/0.95      inference(cnf_transformation,[],[f52]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_305,plain,
% 1.76/0.95      ( r1_tarski(X0,X0) = iProver_top ),
% 1.76/0.95      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_12,negated_conjecture,
% 1.76/0.95      ( k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
% 1.76/0.95      inference(cnf_transformation,[],[f50]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_3,plain,
% 1.76/0.95      ( ~ r1_tarski(X0,X1)
% 1.76/0.95      | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) ),
% 1.76/0.95      inference(cnf_transformation,[],[f41]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_304,plain,
% 1.76/0.95      ( r1_tarski(X0,X1) != iProver_top
% 1.76/0.95      | r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) = iProver_top ),
% 1.76/0.95      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_797,plain,
% 1.76/0.95      ( r1_tarski(X0,k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top
% 1.76/0.95      | r1_tarski(X0,sK2) != iProver_top ),
% 1.76/0.95      inference(superposition,[status(thm)],[c_12,c_304]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_8,plain,
% 1.76/0.95      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 1.76/0.95      | k2_enumset1(X1,X1,X1,X1) = X0
% 1.76/0.95      | k1_xboole_0 = X0 ),
% 1.76/0.95      inference(cnf_transformation,[],[f46]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_299,plain,
% 1.76/0.95      ( k2_enumset1(X0,X0,X0,X0) = X1
% 1.76/0.95      | k1_xboole_0 = X1
% 1.76/0.95      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 1.76/0.95      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_815,plain,
% 1.76/0.95      ( k2_enumset1(sK0,sK0,sK0,sK0) = X0
% 1.76/0.95      | k1_xboole_0 = X0
% 1.76/0.95      | r1_tarski(X0,sK2) != iProver_top ),
% 1.76/0.95      inference(superposition,[status(thm)],[c_797,c_299]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_1701,plain,
% 1.76/0.95      ( k2_enumset1(sK0,sK0,sK0,sK0) = sK2 | sK2 = k1_xboole_0 ),
% 1.76/0.95      inference(superposition,[status(thm)],[c_305,c_815]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_5,plain,
% 1.76/0.95      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
% 1.76/0.95      inference(cnf_transformation,[],[f43]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_302,plain,
% 1.76/0.95      ( r1_tarski(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) = iProver_top ),
% 1.76/0.95      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_588,plain,
% 1.76/0.95      ( r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 1.76/0.95      inference(superposition,[status(thm)],[c_12,c_302]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_693,plain,
% 1.76/0.95      ( k2_enumset1(sK0,sK0,sK0,sK0) = sK1 | sK1 = k1_xboole_0 ),
% 1.76/0.95      inference(superposition,[status(thm)],[c_588,c_299]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_11,negated_conjecture,
% 1.76/0.95      ( k2_enumset1(sK0,sK0,sK0,sK0) != sK1
% 1.76/0.95      | k2_enumset1(sK0,sK0,sK0,sK0) != sK2 ),
% 1.76/0.95      inference(cnf_transformation,[],[f49]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_1170,plain,
% 1.76/0.95      ( k2_enumset1(sK0,sK0,sK0,sK0) != sK2 | sK1 = k1_xboole_0 ),
% 1.76/0.95      inference(superposition,[status(thm)],[c_693,c_11]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_10,negated_conjecture,
% 1.76/0.95      ( k2_enumset1(sK0,sK0,sK0,sK0) != sK2 | k1_xboole_0 != sK1 ),
% 1.76/0.95      inference(cnf_transformation,[],[f48]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_589,plain,
% 1.76/0.95      ( r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 1.76/0.95      inference(predicate_to_equality_rev,[status(thm)],[c_588]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_1254,plain,
% 1.76/0.95      ( ~ r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
% 1.76/0.95      | k2_enumset1(sK0,sK0,sK0,sK0) = sK1
% 1.76/0.95      | k1_xboole_0 = sK1 ),
% 1.76/0.95      inference(instantiation,[status(thm)],[c_8]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_1345,plain,
% 1.76/0.95      ( k2_enumset1(sK0,sK0,sK0,sK0) != sK2 ),
% 1.76/0.95      inference(global_propositional_subsumption,
% 1.76/0.95                [status(thm)],
% 1.76/0.95                [c_1170,c_11,c_10,c_589,c_1254]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_2368,plain,
% 1.76/0.95      ( sK2 = k1_xboole_0 ),
% 1.76/0.95      inference(global_propositional_subsumption,
% 1.76/0.95                [status(thm)],
% 1.76/0.95                [c_1701,c_11,c_10,c_589,c_1254]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_4,plain,
% 1.76/0.95      ( ~ r1_tarski(X0,X1) | k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 ),
% 1.76/0.95      inference(cnf_transformation,[],[f42]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_303,plain,
% 1.76/0.95      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
% 1.76/0.95      | r1_tarski(X0,X1) != iProver_top ),
% 1.76/0.95      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_701,plain,
% 1.76/0.95      ( k3_tarski(k2_enumset1(X0,X0,X0,X0)) = X0 ),
% 1.76/0.95      inference(superposition,[status(thm)],[c_305,c_303]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_1423,plain,
% 1.76/0.95      ( k3_tarski(sK1) = sK0 | sK1 = k1_xboole_0 ),
% 1.76/0.95      inference(superposition,[status(thm)],[c_693,c_701]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_9,negated_conjecture,
% 1.76/0.95      ( k2_enumset1(sK0,sK0,sK0,sK0) != sK1 | k1_xboole_0 != sK2 ),
% 1.76/0.95      inference(cnf_transformation,[],[f47]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_1172,plain,
% 1.76/0.95      ( sK1 = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 1.76/0.95      inference(superposition,[status(thm)],[c_693,c_9]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_1939,plain,
% 1.76/0.95      ( sK1 = k1_xboole_0 ),
% 1.76/0.95      inference(global_propositional_subsumption,
% 1.76/0.95                [status(thm)],
% 1.76/0.95                [c_1423,c_11,c_10,c_589,c_1172,c_1254,c_1701]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_1950,plain,
% 1.76/0.95      ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 1.76/0.95      inference(demodulation,[status(thm)],[c_1939,c_12]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_2372,plain,
% 1.76/0.95      ( k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) = k2_enumset1(sK0,sK0,sK0,sK0) ),
% 1.76/0.95      inference(demodulation,[status(thm)],[c_2368,c_1950]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_2412,plain,
% 1.76/0.95      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_xboole_0 ),
% 1.76/0.95      inference(demodulation,[status(thm)],[c_2372,c_701]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(c_1949,plain,
% 1.76/0.95      ( k2_enumset1(sK0,sK0,sK0,sK0) != k1_xboole_0
% 1.76/0.95      | sK2 != k1_xboole_0 ),
% 1.76/0.95      inference(demodulation,[status(thm)],[c_1939,c_9]) ).
% 1.76/0.95  
% 1.76/0.95  cnf(contradiction,plain,
% 1.76/0.95      ( $false ),
% 1.76/0.95      inference(minisat,[status(thm)],[c_2412,c_1949,c_1701,c_1345]) ).
% 1.76/0.95  
% 1.76/0.95  
% 1.76/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 1.76/0.95  
% 1.76/0.95  ------                               Statistics
% 1.76/0.95  
% 1.76/0.95  ------ General
% 1.76/0.95  
% 1.76/0.95  abstr_ref_over_cycles:                  0
% 1.76/0.95  abstr_ref_under_cycles:                 0
% 1.76/0.95  gc_basic_clause_elim:                   0
% 1.76/0.95  forced_gc_time:                         0
% 1.76/0.95  parsing_time:                           0.009
% 1.76/0.95  unif_index_cands_time:                  0.
% 1.76/0.95  unif_index_add_time:                    0.
% 1.76/0.95  orderings_time:                         0.
% 1.76/0.95  out_proof_time:                         0.009
% 1.76/0.95  total_time:                             0.113
% 1.76/0.95  num_of_symbols:                         35
% 1.76/0.95  num_of_terms:                           1761
% 1.76/0.95  
% 1.76/0.95  ------ Preprocessing
% 1.76/0.95  
% 1.76/0.95  num_of_splits:                          0
% 1.76/0.95  num_of_split_atoms:                     0
% 1.76/0.95  num_of_reused_defs:                     0
% 1.76/0.95  num_eq_ax_congr_red:                    0
% 1.76/0.95  num_of_sem_filtered_clauses:            1
% 1.76/0.95  num_of_subtypes:                        0
% 1.76/0.95  monotx_restored_types:                  0
% 1.76/0.95  sat_num_of_epr_types:                   0
% 1.76/0.95  sat_num_of_non_cyclic_types:            0
% 1.76/0.95  sat_guarded_non_collapsed_types:        0
% 1.76/0.95  num_pure_diseq_elim:                    0
% 1.76/0.95  simp_replaced_by:                       0
% 1.76/0.95  res_preprocessed:                       59
% 1.76/0.95  prep_upred:                             0
% 1.76/0.95  prep_unflattend:                        0
% 1.76/0.95  smt_new_axioms:                         0
% 1.76/0.95  pred_elim_cands:                        1
% 1.76/0.95  pred_elim:                              0
% 1.76/0.95  pred_elim_cl:                           0
% 1.76/0.95  pred_elim_cycles:                       2
% 1.76/0.95  merged_defs:                            0
% 1.76/0.95  merged_defs_ncl:                        0
% 1.76/0.95  bin_hyper_res:                          0
% 1.76/0.95  prep_cycles:                            4
% 1.76/0.95  pred_elim_time:                         0.
% 1.76/0.95  splitting_time:                         0.
% 1.76/0.95  sem_filter_time:                        0.
% 1.76/0.95  monotx_time:                            0.001
% 1.76/0.95  subtype_inf_time:                       0.
% 1.76/0.95  
% 1.76/0.95  ------ Problem properties
% 1.76/0.95  
% 1.76/0.95  clauses:                                12
% 1.76/0.95  conjectures:                            4
% 1.76/0.95  epr:                                    2
% 1.76/0.95  horn:                                   11
% 1.76/0.95  ground:                                 4
% 1.76/0.95  unary:                                  5
% 1.76/0.95  binary:                                 5
% 1.76/0.95  lits:                                   21
% 1.76/0.95  lits_eq:                                11
% 1.76/0.95  fd_pure:                                0
% 1.76/0.95  fd_pseudo:                              0
% 1.76/0.95  fd_cond:                                0
% 1.76/0.95  fd_pseudo_cond:                         2
% 1.76/0.95  ac_symbols:                             0
% 1.76/0.95  
% 1.76/0.95  ------ Propositional Solver
% 1.76/0.95  
% 1.76/0.95  prop_solver_calls:                      29
% 1.76/0.95  prop_fast_solver_calls:                 304
% 1.76/0.95  smt_solver_calls:                       0
% 1.76/0.95  smt_fast_solver_calls:                  0
% 1.76/0.95  prop_num_of_clauses:                    844
% 1.76/0.95  prop_preprocess_simplified:             2537
% 1.76/0.95  prop_fo_subsumed:                       4
% 1.76/0.95  prop_solver_time:                       0.
% 1.76/0.95  smt_solver_time:                        0.
% 1.76/0.95  smt_fast_solver_time:                   0.
% 1.76/0.95  prop_fast_solver_time:                  0.
% 1.76/0.95  prop_unsat_core_time:                   0.
% 1.76/0.95  
% 1.76/0.95  ------ QBF
% 1.76/0.95  
% 1.76/0.95  qbf_q_res:                              0
% 1.76/0.95  qbf_num_tautologies:                    0
% 1.76/0.95  qbf_prep_cycles:                        0
% 1.76/0.95  
% 1.76/0.95  ------ BMC1
% 1.76/0.95  
% 1.76/0.95  bmc1_current_bound:                     -1
% 1.76/0.95  bmc1_last_solved_bound:                 -1
% 1.76/0.95  bmc1_unsat_core_size:                   -1
% 1.76/0.95  bmc1_unsat_core_parents_size:           -1
% 1.76/0.95  bmc1_merge_next_fun:                    0
% 1.76/0.95  bmc1_unsat_core_clauses_time:           0.
% 1.76/0.95  
% 1.76/0.95  ------ Instantiation
% 1.76/0.95  
% 1.76/0.95  inst_num_of_clauses:                    309
% 1.76/0.95  inst_num_in_passive:                    114
% 1.76/0.95  inst_num_in_active:                     181
% 1.76/0.95  inst_num_in_unprocessed:                14
% 1.76/0.95  inst_num_of_loops:                      190
% 1.76/0.95  inst_num_of_learning_restarts:          0
% 1.76/0.95  inst_num_moves_active_passive:          5
% 1.76/0.95  inst_lit_activity:                      0
% 1.76/0.95  inst_lit_activity_moves:                0
% 1.76/0.95  inst_num_tautologies:                   0
% 1.76/0.95  inst_num_prop_implied:                  0
% 1.76/0.95  inst_num_existing_simplified:           0
% 1.76/0.95  inst_num_eq_res_simplified:             0
% 1.76/0.95  inst_num_child_elim:                    0
% 1.76/0.95  inst_num_of_dismatching_blockings:      120
% 1.76/0.95  inst_num_of_non_proper_insts:           458
% 1.76/0.95  inst_num_of_duplicates:                 0
% 1.76/0.95  inst_inst_num_from_inst_to_res:         0
% 1.76/0.95  inst_dismatching_checking_time:         0.
% 1.76/0.95  
% 1.76/0.95  ------ Resolution
% 1.76/0.95  
% 1.76/0.95  res_num_of_clauses:                     0
% 1.76/0.95  res_num_in_passive:                     0
% 1.76/0.95  res_num_in_active:                      0
% 1.76/0.95  res_num_of_loops:                       63
% 1.76/0.95  res_forward_subset_subsumed:            47
% 1.76/0.95  res_backward_subset_subsumed:           0
% 1.76/0.95  res_forward_subsumed:                   0
% 1.76/0.95  res_backward_subsumed:                  0
% 1.76/0.95  res_forward_subsumption_resolution:     0
% 1.76/0.95  res_backward_subsumption_resolution:    0
% 1.76/0.95  res_clause_to_clause_subsumption:       223
% 1.76/0.95  res_orphan_elimination:                 0
% 1.76/0.95  res_tautology_del:                      37
% 1.76/0.95  res_num_eq_res_simplified:              0
% 1.76/0.95  res_num_sel_changes:                    0
% 1.76/0.95  res_moves_from_active_to_pass:          0
% 1.76/0.95  
% 1.76/0.95  ------ Superposition
% 1.76/0.95  
% 1.76/0.95  sup_time_total:                         0.
% 1.76/0.95  sup_time_generating:                    0.
% 1.76/0.95  sup_time_sim_full:                      0.
% 1.76/0.95  sup_time_sim_immed:                     0.
% 1.76/0.95  
% 1.76/0.95  sup_num_of_clauses:                     29
% 1.76/0.95  sup_num_in_active:                      11
% 1.76/0.95  sup_num_in_passive:                     18
% 1.76/0.95  sup_num_of_loops:                       36
% 1.76/0.95  sup_fw_superposition:                   36
% 1.76/0.95  sup_bw_superposition:                   37
% 1.76/0.95  sup_immediate_simplified:               25
% 1.76/0.95  sup_given_eliminated:                   0
% 1.76/0.95  comparisons_done:                       0
% 1.76/0.95  comparisons_avoided:                    0
% 1.76/0.95  
% 1.76/0.95  ------ Simplifications
% 1.76/0.95  
% 1.76/0.95  
% 1.76/0.95  sim_fw_subset_subsumed:                 6
% 1.76/0.95  sim_bw_subset_subsumed:                 9
% 1.76/0.95  sim_fw_subsumed:                        6
% 1.76/0.95  sim_bw_subsumed:                        0
% 1.76/0.95  sim_fw_subsumption_res:                 0
% 1.76/0.95  sim_bw_subsumption_res:                 0
% 1.76/0.95  sim_tautology_del:                      7
% 1.76/0.95  sim_eq_tautology_del:                   10
% 1.76/0.95  sim_eq_res_simp:                        0
% 1.76/0.95  sim_fw_demodulated:                     7
% 1.76/0.95  sim_bw_demodulated:                     25
% 1.76/0.95  sim_light_normalised:                   1
% 1.76/0.95  sim_joinable_taut:                      0
% 1.76/0.95  sim_joinable_simp:                      0
% 1.76/0.95  sim_ac_normalised:                      0
% 1.76/0.95  sim_smt_subsumption:                    0
% 1.76/0.95  
%------------------------------------------------------------------------------
