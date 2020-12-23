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
% DateTime   : Thu Dec  3 11:31:19 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1461)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f14])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f24,f32])).

fof(f44,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f16])).

fof(f29,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f29,f32,f32])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f32])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X1,X1,X1,X2) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f23,f32,f33,f33,f32])).

fof(f31,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f17])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f28,f33,f32])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f25,f32,f33])).

fof(f43,plain,(
    ! [X2,X1] : r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f36])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f26,f32,f33])).

fof(f42,plain,(
    ! [X2,X1] : r1_tarski(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f35])).

fof(f30,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f17])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_421,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_425,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_745,plain,
    ( k2_xboole_0(k1_xboole_0,k2_enumset1(X0,X0,X0,X1)) = k2_enumset1(X0,X0,X0,X1) ),
    inference(superposition,[status(thm)],[c_421,c_425])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f18])).

cnf(c_10,negated_conjecture,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_418,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_420,plain,
    ( k2_enumset1(X0,X0,X0,X1) = X2
    | k2_enumset1(X1,X1,X1,X1) = X2
    | k2_enumset1(X0,X0,X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1092,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK2,sK2,sK2,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_418,c_420])).

cnf(c_1300,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = X0
    | k2_enumset1(sK2,sK2,sK2,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k2_enumset1(sK0,sK0,sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1092,c_420])).

cnf(c_8,negated_conjecture,
    ( sK0 != sK3 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_7,plain,
    ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))
    | X1 = X0
    | X2 = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_13,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_4,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_22,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_284,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_485,plain,
    ( sK3 != X0
    | sK0 != X0
    | sK0 = sK3 ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_486,plain,
    ( sK3 != sK0
    | sK0 = sK3
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_1293,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1294,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1293])).

cnf(c_3,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_423,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1305,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
    | r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(X0,X0,X0,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1092,c_423])).

cnf(c_9,negated_conjecture,
    ( sK0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_487,plain,
    ( sK2 != X0
    | sK0 != X0
    | sK0 = sK2 ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_488,plain,
    ( sK2 != sK0
    | sK0 = sK2
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_487])).

cnf(c_419,plain,
    ( X0 = X1
    | X2 = X1
    | r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1309,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
    | sK2 = X0
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK0,sK0,sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1092,c_419])).

cnf(c_1390,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
    | sK2 = sK0
    | r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1309])).

cnf(c_1393,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
    | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK2,sK2,sK2,sK3) = k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1305,c_9,c_13,c_22,c_488,c_1294,c_1390])).

cnf(c_1394,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1393])).

cnf(c_746,plain,
    ( k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) = k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_418,c_425])).

cnf(c_1404,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
    | k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1)) = k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(superposition,[status(thm)],[c_1394,c_746])).

cnf(c_1406,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
    | sK2 = X0
    | sK3 = X0
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK0,sK0,sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1394,c_419])).

cnf(c_1460,plain,
    ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK0,sK0,sK0,sK1))
    | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
    | sK2 = X0
    | sK3 = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1406])).

cnf(c_1462,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1))
    | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
    | sK2 = sK0
    | sK3 = sK0 ),
    inference(instantiation,[status(thm)],[c_1460])).

cnf(c_1532,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
    | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1404,c_9,c_8,c_13,c_22,c_486,c_488,c_1294,c_1461])).

cnf(c_1533,plain,
    ( k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1532])).

cnf(c_1545,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
    | sK3 = X0
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK0,sK0,sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1533,c_419])).

cnf(c_1598,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
    | sK3 = sK0
    | r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1545])).

cnf(c_1601,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1300,c_8,c_13,c_22,c_486,c_1294,c_1598])).

cnf(c_1617,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1601,c_423])).

cnf(c_1950,plain,
    ( k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1617,c_425])).

cnf(c_2854,plain,
    ( k2_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_1950])).

cnf(c_2954,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_745,c_2854])).

cnf(c_3127,plain,
    ( sK1 = X0
    | sK1 = X1
    | r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2954,c_419])).

cnf(c_3154,plain,
    ( sK1 = sK0
    | r1_tarski(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3127])).

cnf(c_2039,plain,
    ( X0 != X1
    | X0 = sK1
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_2040,plain,
    ( sK1 != sK0
    | sK0 = sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2039])).

cnf(c_572,plain,
    ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK2,sK2,sK2,X1))
    | X1 = X0
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_938,plain,
    ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK2,sK2,sK2,sK3))
    | sK2 = X0
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_572])).

cnf(c_940,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK2,sK2,sK2,sK3))
    | sK2 = sK0
    | sK3 = sK0 ),
    inference(instantiation,[status(thm)],[c_938])).

cnf(c_286,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
    theory(equality)).

cnf(c_778,plain,
    ( X0 != sK1
    | X1 != sK0
    | X2 != sK0
    | X3 != sK0
    | k2_enumset1(X1,X2,X3,X0) = k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_286])).

cnf(c_783,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK0,sK0,sK0,sK1)
    | sK0 != sK1
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_285,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_516,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))
    | X1 != k2_enumset1(sK2,sK2,sK2,sK3)
    | X0 != k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_285])).

cnf(c_599,plain,
    ( r1_tarski(X0,k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))
    | X0 != k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK2,sK2,sK2,sK3) != k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_777,plain,
    ( r1_tarski(k2_enumset1(X0,X1,X2,X3),k2_enumset1(sK2,sK2,sK2,sK3))
    | ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))
    | k2_enumset1(X0,X1,X2,X3) != k2_enumset1(sK0,sK0,sK0,sK1)
    | k2_enumset1(sK2,sK2,sK2,sK3) != k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_599])).

cnf(c_780,plain,
    ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))
    | r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK2,sK2,sK2,sK3))
    | k2_enumset1(sK2,sK2,sK2,sK3) != k2_enumset1(sK2,sK2,sK2,sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_283,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_600,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK3) = k2_enumset1(sK2,sK2,sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_283])).

cnf(c_18,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_20,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3154,c_2040,c_940,c_783,c_780,c_600,c_488,c_486,c_22,c_20,c_13,c_8,c_9,c_10])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.31  % Computer   : n020.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % WCLimit    : 600
% 0.12/0.31  % DateTime   : Tue Dec  1 19:02:07 EST 2020
% 0.17/0.31  % CPUTime    : 
% 0.17/0.32  % Running in FOF mode
% 1.79/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/0.93  
% 1.79/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.79/0.93  
% 1.79/0.93  ------  iProver source info
% 1.79/0.93  
% 1.79/0.93  git: date: 2020-06-30 10:37:57 +0100
% 1.79/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.79/0.93  git: non_committed_changes: false
% 1.79/0.93  git: last_make_outside_of_git: false
% 1.79/0.93  
% 1.79/0.93  ------ 
% 1.79/0.93  
% 1.79/0.93  ------ Input Options
% 1.79/0.93  
% 1.79/0.93  --out_options                           all
% 1.79/0.93  --tptp_safe_out                         true
% 1.79/0.93  --problem_path                          ""
% 1.79/0.93  --include_path                          ""
% 1.79/0.93  --clausifier                            res/vclausify_rel
% 1.79/0.93  --clausifier_options                    --mode clausify
% 1.79/0.93  --stdin                                 false
% 1.79/0.93  --stats_out                             all
% 1.79/0.93  
% 1.79/0.93  ------ General Options
% 1.79/0.93  
% 1.79/0.93  --fof                                   false
% 1.79/0.93  --time_out_real                         305.
% 1.79/0.93  --time_out_virtual                      -1.
% 1.79/0.93  --symbol_type_check                     false
% 1.79/0.93  --clausify_out                          false
% 1.79/0.93  --sig_cnt_out                           false
% 1.79/0.93  --trig_cnt_out                          false
% 1.79/0.93  --trig_cnt_out_tolerance                1.
% 1.79/0.93  --trig_cnt_out_sk_spl                   false
% 1.79/0.93  --abstr_cl_out                          false
% 1.79/0.93  
% 1.79/0.93  ------ Global Options
% 1.79/0.93  
% 1.79/0.93  --schedule                              default
% 1.79/0.93  --add_important_lit                     false
% 1.79/0.93  --prop_solver_per_cl                    1000
% 1.79/0.93  --min_unsat_core                        false
% 1.79/0.93  --soft_assumptions                      false
% 1.79/0.93  --soft_lemma_size                       3
% 1.79/0.93  --prop_impl_unit_size                   0
% 1.79/0.93  --prop_impl_unit                        []
% 1.79/0.93  --share_sel_clauses                     true
% 1.79/0.93  --reset_solvers                         false
% 1.79/0.93  --bc_imp_inh                            [conj_cone]
% 1.79/0.93  --conj_cone_tolerance                   3.
% 1.79/0.93  --extra_neg_conj                        none
% 1.79/0.93  --large_theory_mode                     true
% 1.79/0.93  --prolific_symb_bound                   200
% 1.79/0.93  --lt_threshold                          2000
% 1.79/0.93  --clause_weak_htbl                      true
% 1.79/0.93  --gc_record_bc_elim                     false
% 1.79/0.93  
% 1.79/0.93  ------ Preprocessing Options
% 1.79/0.93  
% 1.79/0.93  --preprocessing_flag                    true
% 1.79/0.93  --time_out_prep_mult                    0.1
% 1.79/0.93  --splitting_mode                        input
% 1.79/0.93  --splitting_grd                         true
% 1.79/0.93  --splitting_cvd                         false
% 1.79/0.93  --splitting_cvd_svl                     false
% 1.79/0.93  --splitting_nvd                         32
% 1.79/0.93  --sub_typing                            true
% 1.79/0.93  --prep_gs_sim                           true
% 1.79/0.93  --prep_unflatten                        true
% 1.79/0.93  --prep_res_sim                          true
% 1.79/0.93  --prep_upred                            true
% 1.79/0.93  --prep_sem_filter                       exhaustive
% 1.79/0.93  --prep_sem_filter_out                   false
% 1.79/0.93  --pred_elim                             true
% 1.79/0.93  --res_sim_input                         true
% 1.79/0.93  --eq_ax_congr_red                       true
% 1.79/0.93  --pure_diseq_elim                       true
% 1.79/0.93  --brand_transform                       false
% 1.79/0.93  --non_eq_to_eq                          false
% 1.79/0.93  --prep_def_merge                        true
% 1.79/0.93  --prep_def_merge_prop_impl              false
% 1.79/0.93  --prep_def_merge_mbd                    true
% 1.79/0.93  --prep_def_merge_tr_red                 false
% 1.79/0.93  --prep_def_merge_tr_cl                  false
% 1.79/0.93  --smt_preprocessing                     true
% 1.79/0.93  --smt_ac_axioms                         fast
% 1.79/0.93  --preprocessed_out                      false
% 1.79/0.93  --preprocessed_stats                    false
% 1.79/0.93  
% 1.79/0.93  ------ Abstraction refinement Options
% 1.79/0.93  
% 1.79/0.93  --abstr_ref                             []
% 1.79/0.93  --abstr_ref_prep                        false
% 1.79/0.93  --abstr_ref_until_sat                   false
% 1.79/0.93  --abstr_ref_sig_restrict                funpre
% 1.79/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 1.79/0.93  --abstr_ref_under                       []
% 1.79/0.93  
% 1.79/0.93  ------ SAT Options
% 1.79/0.93  
% 1.79/0.93  --sat_mode                              false
% 1.79/0.93  --sat_fm_restart_options                ""
% 1.79/0.93  --sat_gr_def                            false
% 1.79/0.93  --sat_epr_types                         true
% 1.79/0.93  --sat_non_cyclic_types                  false
% 1.79/0.93  --sat_finite_models                     false
% 1.79/0.93  --sat_fm_lemmas                         false
% 1.79/0.93  --sat_fm_prep                           false
% 1.79/0.93  --sat_fm_uc_incr                        true
% 1.79/0.93  --sat_out_model                         small
% 1.79/0.93  --sat_out_clauses                       false
% 1.79/0.93  
% 1.79/0.93  ------ QBF Options
% 1.79/0.93  
% 1.79/0.93  --qbf_mode                              false
% 1.79/0.93  --qbf_elim_univ                         false
% 1.79/0.93  --qbf_dom_inst                          none
% 1.79/0.93  --qbf_dom_pre_inst                      false
% 1.79/0.93  --qbf_sk_in                             false
% 1.79/0.93  --qbf_pred_elim                         true
% 1.79/0.93  --qbf_split                             512
% 1.79/0.93  
% 1.79/0.93  ------ BMC1 Options
% 1.79/0.93  
% 1.79/0.93  --bmc1_incremental                      false
% 1.79/0.93  --bmc1_axioms                           reachable_all
% 1.79/0.93  --bmc1_min_bound                        0
% 1.79/0.93  --bmc1_max_bound                        -1
% 1.79/0.93  --bmc1_max_bound_default                -1
% 1.79/0.93  --bmc1_symbol_reachability              true
% 1.79/0.93  --bmc1_property_lemmas                  false
% 1.79/0.93  --bmc1_k_induction                      false
% 1.79/0.93  --bmc1_non_equiv_states                 false
% 1.79/0.93  --bmc1_deadlock                         false
% 1.79/0.93  --bmc1_ucm                              false
% 1.79/0.93  --bmc1_add_unsat_core                   none
% 1.79/0.93  --bmc1_unsat_core_children              false
% 1.79/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 1.79/0.93  --bmc1_out_stat                         full
% 1.79/0.93  --bmc1_ground_init                      false
% 1.79/0.93  --bmc1_pre_inst_next_state              false
% 1.79/0.93  --bmc1_pre_inst_state                   false
% 1.79/0.93  --bmc1_pre_inst_reach_state             false
% 1.79/0.93  --bmc1_out_unsat_core                   false
% 1.79/0.93  --bmc1_aig_witness_out                  false
% 1.79/0.93  --bmc1_verbose                          false
% 1.79/0.93  --bmc1_dump_clauses_tptp                false
% 1.79/0.93  --bmc1_dump_unsat_core_tptp             false
% 1.79/0.93  --bmc1_dump_file                        -
% 1.79/0.93  --bmc1_ucm_expand_uc_limit              128
% 1.79/0.93  --bmc1_ucm_n_expand_iterations          6
% 1.79/0.93  --bmc1_ucm_extend_mode                  1
% 1.79/0.93  --bmc1_ucm_init_mode                    2
% 1.79/0.93  --bmc1_ucm_cone_mode                    none
% 1.79/0.93  --bmc1_ucm_reduced_relation_type        0
% 1.79/0.93  --bmc1_ucm_relax_model                  4
% 1.79/0.93  --bmc1_ucm_full_tr_after_sat            true
% 1.79/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 1.79/0.93  --bmc1_ucm_layered_model                none
% 1.79/0.93  --bmc1_ucm_max_lemma_size               10
% 1.79/0.93  
% 1.79/0.93  ------ AIG Options
% 1.79/0.93  
% 1.79/0.93  --aig_mode                              false
% 1.79/0.93  
% 1.79/0.93  ------ Instantiation Options
% 1.79/0.93  
% 1.79/0.93  --instantiation_flag                    true
% 1.79/0.93  --inst_sos_flag                         false
% 1.79/0.93  --inst_sos_phase                        true
% 1.79/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.79/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.79/0.93  --inst_lit_sel_side                     num_symb
% 1.79/0.93  --inst_solver_per_active                1400
% 1.79/0.93  --inst_solver_calls_frac                1.
% 1.79/0.93  --inst_passive_queue_type               priority_queues
% 1.79/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.79/0.93  --inst_passive_queues_freq              [25;2]
% 1.79/0.93  --inst_dismatching                      true
% 1.79/0.93  --inst_eager_unprocessed_to_passive     true
% 1.79/0.93  --inst_prop_sim_given                   true
% 1.79/0.93  --inst_prop_sim_new                     false
% 1.79/0.93  --inst_subs_new                         false
% 1.79/0.93  --inst_eq_res_simp                      false
% 1.79/0.93  --inst_subs_given                       false
% 1.79/0.93  --inst_orphan_elimination               true
% 1.79/0.93  --inst_learning_loop_flag               true
% 1.79/0.93  --inst_learning_start                   3000
% 1.79/0.93  --inst_learning_factor                  2
% 1.79/0.93  --inst_start_prop_sim_after_learn       3
% 1.79/0.93  --inst_sel_renew                        solver
% 1.79/0.93  --inst_lit_activity_flag                true
% 1.79/0.93  --inst_restr_to_given                   false
% 1.79/0.93  --inst_activity_threshold               500
% 1.79/0.93  --inst_out_proof                        true
% 1.79/0.93  
% 1.79/0.93  ------ Resolution Options
% 1.79/0.93  
% 1.79/0.93  --resolution_flag                       true
% 1.79/0.93  --res_lit_sel                           adaptive
% 1.79/0.93  --res_lit_sel_side                      none
% 1.79/0.93  --res_ordering                          kbo
% 1.79/0.93  --res_to_prop_solver                    active
% 1.79/0.93  --res_prop_simpl_new                    false
% 1.79/0.93  --res_prop_simpl_given                  true
% 1.79/0.93  --res_passive_queue_type                priority_queues
% 1.79/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.79/0.93  --res_passive_queues_freq               [15;5]
% 1.79/0.93  --res_forward_subs                      full
% 1.79/0.93  --res_backward_subs                     full
% 1.79/0.93  --res_forward_subs_resolution           true
% 1.79/0.93  --res_backward_subs_resolution          true
% 1.79/0.93  --res_orphan_elimination                true
% 1.79/0.93  --res_time_limit                        2.
% 1.79/0.93  --res_out_proof                         true
% 1.79/0.93  
% 1.79/0.93  ------ Superposition Options
% 1.79/0.93  
% 1.79/0.93  --superposition_flag                    true
% 1.79/0.93  --sup_passive_queue_type                priority_queues
% 1.79/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.79/0.93  --sup_passive_queues_freq               [8;1;4]
% 1.79/0.93  --demod_completeness_check              fast
% 1.79/0.93  --demod_use_ground                      true
% 1.79/0.93  --sup_to_prop_solver                    passive
% 1.79/0.93  --sup_prop_simpl_new                    true
% 1.79/0.93  --sup_prop_simpl_given                  true
% 1.79/0.93  --sup_fun_splitting                     false
% 1.79/0.93  --sup_smt_interval                      50000
% 1.79/0.93  
% 1.79/0.93  ------ Superposition Simplification Setup
% 1.79/0.93  
% 1.79/0.93  --sup_indices_passive                   []
% 1.79/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 1.79/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/0.93  --sup_full_bw                           [BwDemod]
% 1.79/0.93  --sup_immed_triv                        [TrivRules]
% 1.79/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.79/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/0.93  --sup_immed_bw_main                     []
% 1.79/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 1.79/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/0.93  
% 1.79/0.93  ------ Combination Options
% 1.79/0.93  
% 1.79/0.93  --comb_res_mult                         3
% 1.79/0.93  --comb_sup_mult                         2
% 1.79/0.93  --comb_inst_mult                        10
% 1.79/0.93  
% 1.79/0.93  ------ Debug Options
% 1.79/0.93  
% 1.79/0.93  --dbg_backtrace                         false
% 1.79/0.93  --dbg_dump_prop_clauses                 false
% 1.79/0.93  --dbg_dump_prop_clauses_file            -
% 1.79/0.93  --dbg_out_stat                          false
% 1.79/0.93  ------ Parsing...
% 1.79/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.79/0.93  
% 1.79/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 1.79/0.93  
% 1.79/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.79/0.93  
% 1.79/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.79/0.93  ------ Proving...
% 1.79/0.93  ------ Problem Properties 
% 1.79/0.93  
% 1.79/0.93  
% 1.79/0.93  clauses                                 11
% 1.79/0.93  conjectures                             3
% 1.79/0.93  EPR                                     2
% 1.79/0.93  Horn                                    9
% 1.79/0.93  unary                                   8
% 1.79/0.93  binary                                  1
% 1.79/0.93  lits                                    18
% 1.79/0.93  lits eq                                 10
% 1.79/0.93  fd_pure                                 0
% 1.79/0.93  fd_pseudo                               0
% 1.79/0.93  fd_cond                                 0
% 1.79/0.93  fd_pseudo_cond                          2
% 1.79/0.93  AC symbols                              0
% 1.79/0.93  
% 1.79/0.93  ------ Schedule dynamic 5 is on 
% 1.79/0.93  
% 1.79/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.79/0.93  
% 1.79/0.93  
% 1.79/0.93  ------ 
% 1.79/0.93  Current options:
% 1.79/0.93  ------ 
% 1.79/0.93  
% 1.79/0.93  ------ Input Options
% 1.79/0.93  
% 1.79/0.93  --out_options                           all
% 1.79/0.93  --tptp_safe_out                         true
% 1.79/0.93  --problem_path                          ""
% 1.79/0.93  --include_path                          ""
% 1.79/0.93  --clausifier                            res/vclausify_rel
% 1.79/0.93  --clausifier_options                    --mode clausify
% 1.79/0.93  --stdin                                 false
% 1.79/0.93  --stats_out                             all
% 1.79/0.93  
% 1.79/0.93  ------ General Options
% 1.79/0.93  
% 1.79/0.93  --fof                                   false
% 1.79/0.93  --time_out_real                         305.
% 1.79/0.93  --time_out_virtual                      -1.
% 1.79/0.93  --symbol_type_check                     false
% 1.79/0.93  --clausify_out                          false
% 1.79/0.93  --sig_cnt_out                           false
% 1.79/0.93  --trig_cnt_out                          false
% 1.79/0.93  --trig_cnt_out_tolerance                1.
% 1.79/0.93  --trig_cnt_out_sk_spl                   false
% 1.79/0.93  --abstr_cl_out                          false
% 1.79/0.93  
% 1.79/0.93  ------ Global Options
% 1.79/0.93  
% 1.79/0.93  --schedule                              default
% 1.79/0.93  --add_important_lit                     false
% 1.79/0.93  --prop_solver_per_cl                    1000
% 1.79/0.93  --min_unsat_core                        false
% 1.79/0.93  --soft_assumptions                      false
% 1.79/0.93  --soft_lemma_size                       3
% 1.79/0.93  --prop_impl_unit_size                   0
% 1.79/0.93  --prop_impl_unit                        []
% 1.79/0.93  --share_sel_clauses                     true
% 1.79/0.93  --reset_solvers                         false
% 1.79/0.93  --bc_imp_inh                            [conj_cone]
% 1.79/0.93  --conj_cone_tolerance                   3.
% 1.79/0.93  --extra_neg_conj                        none
% 1.79/0.93  --large_theory_mode                     true
% 1.79/0.93  --prolific_symb_bound                   200
% 1.79/0.93  --lt_threshold                          2000
% 1.79/0.93  --clause_weak_htbl                      true
% 1.79/0.93  --gc_record_bc_elim                     false
% 1.79/0.93  
% 1.79/0.93  ------ Preprocessing Options
% 1.79/0.93  
% 1.79/0.93  --preprocessing_flag                    true
% 1.79/0.93  --time_out_prep_mult                    0.1
% 1.79/0.93  --splitting_mode                        input
% 1.79/0.93  --splitting_grd                         true
% 1.79/0.93  --splitting_cvd                         false
% 1.79/0.93  --splitting_cvd_svl                     false
% 1.79/0.93  --splitting_nvd                         32
% 1.79/0.93  --sub_typing                            true
% 1.79/0.93  --prep_gs_sim                           true
% 1.79/0.93  --prep_unflatten                        true
% 1.79/0.93  --prep_res_sim                          true
% 1.79/0.93  --prep_upred                            true
% 1.79/0.93  --prep_sem_filter                       exhaustive
% 1.79/0.93  --prep_sem_filter_out                   false
% 1.79/0.93  --pred_elim                             true
% 1.79/0.93  --res_sim_input                         true
% 1.79/0.93  --eq_ax_congr_red                       true
% 1.79/0.93  --pure_diseq_elim                       true
% 1.79/0.93  --brand_transform                       false
% 1.79/0.93  --non_eq_to_eq                          false
% 1.79/0.93  --prep_def_merge                        true
% 1.79/0.93  --prep_def_merge_prop_impl              false
% 1.79/0.93  --prep_def_merge_mbd                    true
% 1.79/0.93  --prep_def_merge_tr_red                 false
% 1.79/0.93  --prep_def_merge_tr_cl                  false
% 1.79/0.93  --smt_preprocessing                     true
% 1.79/0.93  --smt_ac_axioms                         fast
% 1.79/0.93  --preprocessed_out                      false
% 1.79/0.93  --preprocessed_stats                    false
% 1.79/0.93  
% 1.79/0.93  ------ Abstraction refinement Options
% 1.79/0.93  
% 1.79/0.93  --abstr_ref                             []
% 1.79/0.93  --abstr_ref_prep                        false
% 1.79/0.93  --abstr_ref_until_sat                   false
% 1.79/0.93  --abstr_ref_sig_restrict                funpre
% 1.79/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 1.79/0.93  --abstr_ref_under                       []
% 1.79/0.93  
% 1.79/0.93  ------ SAT Options
% 1.79/0.93  
% 1.79/0.93  --sat_mode                              false
% 1.79/0.93  --sat_fm_restart_options                ""
% 1.79/0.93  --sat_gr_def                            false
% 1.79/0.93  --sat_epr_types                         true
% 1.79/0.93  --sat_non_cyclic_types                  false
% 1.79/0.93  --sat_finite_models                     false
% 1.79/0.93  --sat_fm_lemmas                         false
% 1.79/0.93  --sat_fm_prep                           false
% 1.79/0.93  --sat_fm_uc_incr                        true
% 1.79/0.93  --sat_out_model                         small
% 1.79/0.93  --sat_out_clauses                       false
% 1.79/0.93  
% 1.79/0.93  ------ QBF Options
% 1.79/0.93  
% 1.79/0.93  --qbf_mode                              false
% 1.79/0.93  --qbf_elim_univ                         false
% 1.79/0.93  --qbf_dom_inst                          none
% 1.79/0.93  --qbf_dom_pre_inst                      false
% 1.79/0.93  --qbf_sk_in                             false
% 1.79/0.93  --qbf_pred_elim                         true
% 1.79/0.93  --qbf_split                             512
% 1.79/0.93  
% 1.79/0.93  ------ BMC1 Options
% 1.79/0.93  
% 1.79/0.93  --bmc1_incremental                      false
% 1.79/0.93  --bmc1_axioms                           reachable_all
% 1.79/0.93  --bmc1_min_bound                        0
% 1.79/0.93  --bmc1_max_bound                        -1
% 1.79/0.93  --bmc1_max_bound_default                -1
% 1.79/0.93  --bmc1_symbol_reachability              true
% 1.79/0.93  --bmc1_property_lemmas                  false
% 1.79/0.93  --bmc1_k_induction                      false
% 1.79/0.93  --bmc1_non_equiv_states                 false
% 1.79/0.93  --bmc1_deadlock                         false
% 1.79/0.93  --bmc1_ucm                              false
% 1.79/0.93  --bmc1_add_unsat_core                   none
% 1.79/0.93  --bmc1_unsat_core_children              false
% 1.79/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 1.79/0.93  --bmc1_out_stat                         full
% 1.79/0.93  --bmc1_ground_init                      false
% 1.79/0.93  --bmc1_pre_inst_next_state              false
% 1.79/0.93  --bmc1_pre_inst_state                   false
% 1.79/0.93  --bmc1_pre_inst_reach_state             false
% 1.79/0.93  --bmc1_out_unsat_core                   false
% 1.79/0.93  --bmc1_aig_witness_out                  false
% 1.79/0.93  --bmc1_verbose                          false
% 1.79/0.93  --bmc1_dump_clauses_tptp                false
% 1.79/0.93  --bmc1_dump_unsat_core_tptp             false
% 1.79/0.93  --bmc1_dump_file                        -
% 1.79/0.93  --bmc1_ucm_expand_uc_limit              128
% 1.79/0.93  --bmc1_ucm_n_expand_iterations          6
% 1.79/0.93  --bmc1_ucm_extend_mode                  1
% 1.79/0.93  --bmc1_ucm_init_mode                    2
% 1.79/0.93  --bmc1_ucm_cone_mode                    none
% 1.79/0.93  --bmc1_ucm_reduced_relation_type        0
% 1.79/0.93  --bmc1_ucm_relax_model                  4
% 1.79/0.93  --bmc1_ucm_full_tr_after_sat            true
% 1.79/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 1.79/0.93  --bmc1_ucm_layered_model                none
% 1.79/0.93  --bmc1_ucm_max_lemma_size               10
% 1.79/0.93  
% 1.79/0.93  ------ AIG Options
% 1.79/0.93  
% 1.79/0.93  --aig_mode                              false
% 1.79/0.93  
% 1.79/0.93  ------ Instantiation Options
% 1.79/0.93  
% 1.79/0.93  --instantiation_flag                    true
% 1.79/0.93  --inst_sos_flag                         false
% 1.79/0.93  --inst_sos_phase                        true
% 1.79/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.79/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.79/0.93  --inst_lit_sel_side                     none
% 1.79/0.93  --inst_solver_per_active                1400
% 1.79/0.93  --inst_solver_calls_frac                1.
% 1.79/0.93  --inst_passive_queue_type               priority_queues
% 1.79/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.79/0.93  --inst_passive_queues_freq              [25;2]
% 1.79/0.93  --inst_dismatching                      true
% 1.79/0.93  --inst_eager_unprocessed_to_passive     true
% 1.79/0.93  --inst_prop_sim_given                   true
% 1.79/0.93  --inst_prop_sim_new                     false
% 1.79/0.93  --inst_subs_new                         false
% 1.79/0.93  --inst_eq_res_simp                      false
% 1.79/0.93  --inst_subs_given                       false
% 1.79/0.93  --inst_orphan_elimination               true
% 1.79/0.93  --inst_learning_loop_flag               true
% 1.79/0.93  --inst_learning_start                   3000
% 1.79/0.93  --inst_learning_factor                  2
% 1.79/0.93  --inst_start_prop_sim_after_learn       3
% 1.79/0.93  --inst_sel_renew                        solver
% 1.79/0.93  --inst_lit_activity_flag                true
% 1.79/0.93  --inst_restr_to_given                   false
% 1.79/0.93  --inst_activity_threshold               500
% 1.79/0.93  --inst_out_proof                        true
% 1.79/0.93  
% 1.79/0.93  ------ Resolution Options
% 1.79/0.93  
% 1.79/0.93  --resolution_flag                       false
% 1.79/0.93  --res_lit_sel                           adaptive
% 1.79/0.93  --res_lit_sel_side                      none
% 1.79/0.93  --res_ordering                          kbo
% 1.79/0.93  --res_to_prop_solver                    active
% 1.79/0.93  --res_prop_simpl_new                    false
% 1.79/0.93  --res_prop_simpl_given                  true
% 1.79/0.93  --res_passive_queue_type                priority_queues
% 1.79/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.79/0.93  --res_passive_queues_freq               [15;5]
% 1.79/0.93  --res_forward_subs                      full
% 1.79/0.93  --res_backward_subs                     full
% 1.79/0.93  --res_forward_subs_resolution           true
% 1.79/0.93  --res_backward_subs_resolution          true
% 1.79/0.93  --res_orphan_elimination                true
% 1.79/0.93  --res_time_limit                        2.
% 1.79/0.93  --res_out_proof                         true
% 1.79/0.93  
% 1.79/0.93  ------ Superposition Options
% 1.79/0.93  
% 1.79/0.93  --superposition_flag                    true
% 1.79/0.93  --sup_passive_queue_type                priority_queues
% 1.79/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.79/0.93  --sup_passive_queues_freq               [8;1;4]
% 1.79/0.93  --demod_completeness_check              fast
% 1.79/0.93  --demod_use_ground                      true
% 1.79/0.93  --sup_to_prop_solver                    passive
% 1.79/0.93  --sup_prop_simpl_new                    true
% 1.79/0.93  --sup_prop_simpl_given                  true
% 1.79/0.93  --sup_fun_splitting                     false
% 1.79/0.93  --sup_smt_interval                      50000
% 1.79/0.93  
% 1.79/0.93  ------ Superposition Simplification Setup
% 1.79/0.93  
% 1.79/0.93  --sup_indices_passive                   []
% 1.79/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.79/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 1.79/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/0.93  --sup_full_bw                           [BwDemod]
% 1.79/0.93  --sup_immed_triv                        [TrivRules]
% 1.79/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.79/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/0.93  --sup_immed_bw_main                     []
% 1.79/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 1.79/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.79/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.79/0.93  
% 1.79/0.93  ------ Combination Options
% 1.79/0.93  
% 1.79/0.93  --comb_res_mult                         3
% 1.79/0.93  --comb_sup_mult                         2
% 1.79/0.93  --comb_inst_mult                        10
% 1.79/0.93  
% 1.79/0.93  ------ Debug Options
% 1.79/0.93  
% 1.79/0.93  --dbg_backtrace                         false
% 1.79/0.93  --dbg_dump_prop_clauses                 false
% 1.79/0.93  --dbg_dump_prop_clauses_file            -
% 1.79/0.93  --dbg_out_stat                          false
% 1.79/0.93  
% 1.79/0.93  
% 1.79/0.93  
% 1.79/0.93  
% 1.79/0.93  ------ Proving...
% 1.79/0.93  
% 1.79/0.93  
% 1.79/0.93  % SZS status Theorem for theBenchmark.p
% 1.79/0.93  
% 1.79/0.93  % SZS output start CNFRefutation for theBenchmark.p
% 1.79/0.93  
% 1.79/0.93  fof(f6,axiom,(
% 1.79/0.93    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.93  
% 1.79/0.93  fof(f11,plain,(
% 1.79/0.93    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.79/0.93    inference(ennf_transformation,[],[f6])).
% 1.79/0.93  
% 1.79/0.93  fof(f14,plain,(
% 1.79/0.93    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.79/0.93    inference(nnf_transformation,[],[f11])).
% 1.79/0.93  
% 1.79/0.93  fof(f15,plain,(
% 1.79/0.93    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.79/0.93    inference(flattening,[],[f14])).
% 1.79/0.93  
% 1.79/0.93  fof(f24,plain,(
% 1.79/0.93    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_xboole_0 != X0) )),
% 1.79/0.93    inference(cnf_transformation,[],[f15])).
% 1.79/0.93  
% 1.79/0.93  fof(f4,axiom,(
% 1.79/0.93    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.93  
% 1.79/0.93  fof(f21,plain,(
% 1.79/0.93    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.79/0.93    inference(cnf_transformation,[],[f4])).
% 1.79/0.93  
% 1.79/0.93  fof(f5,axiom,(
% 1.79/0.93    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.93  
% 1.79/0.93  fof(f22,plain,(
% 1.79/0.93    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.79/0.93    inference(cnf_transformation,[],[f5])).
% 1.79/0.93  
% 1.79/0.93  fof(f32,plain,(
% 1.79/0.93    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.79/0.93    inference(definition_unfolding,[],[f21,f22])).
% 1.79/0.93  
% 1.79/0.93  fof(f37,plain,(
% 1.79/0.93    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k1_xboole_0 != X0) )),
% 1.79/0.93    inference(definition_unfolding,[],[f24,f32])).
% 1.79/0.93  
% 1.79/0.93  fof(f44,plain,(
% 1.79/0.93    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X1,X1,X1,X2))) )),
% 1.79/0.93    inference(equality_resolution,[],[f37])).
% 1.79/0.93  
% 1.79/0.93  fof(f2,axiom,(
% 1.79/0.93    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.93  
% 1.79/0.93  fof(f10,plain,(
% 1.79/0.93    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.79/0.93    inference(ennf_transformation,[],[f2])).
% 1.79/0.93  
% 1.79/0.93  fof(f19,plain,(
% 1.79/0.93    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.79/0.93    inference(cnf_transformation,[],[f10])).
% 1.79/0.93  
% 1.79/0.93  fof(f1,axiom,(
% 1.79/0.93    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.93  
% 1.79/0.93  fof(f18,plain,(
% 1.79/0.93    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.79/0.93    inference(cnf_transformation,[],[f1])).
% 1.79/0.93  
% 1.79/0.93  fof(f8,conjecture,(
% 1.79/0.93    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.93  
% 1.79/0.93  fof(f9,negated_conjecture,(
% 1.79/0.93    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.79/0.93    inference(negated_conjecture,[],[f8])).
% 1.79/0.93  
% 1.79/0.93  fof(f13,plain,(
% 1.79/0.93    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.79/0.93    inference(ennf_transformation,[],[f9])).
% 1.79/0.93  
% 1.79/0.93  fof(f16,plain,(
% 1.79/0.93    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 1.79/0.93    introduced(choice_axiom,[])).
% 1.79/0.93  
% 1.79/0.93  fof(f17,plain,(
% 1.79/0.93    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.79/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f16])).
% 1.79/0.93  
% 1.79/0.93  fof(f29,plain,(
% 1.79/0.93    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.79/0.93    inference(cnf_transformation,[],[f17])).
% 1.79/0.93  
% 1.79/0.93  fof(f40,plain,(
% 1.79/0.93    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))),
% 1.79/0.93    inference(definition_unfolding,[],[f29,f32,f32])).
% 1.79/0.93  
% 1.79/0.93  fof(f23,plain,(
% 1.79/0.93    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.79/0.93    inference(cnf_transformation,[],[f15])).
% 1.79/0.93  
% 1.79/0.93  fof(f3,axiom,(
% 1.79/0.93    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.93  
% 1.79/0.93  fof(f20,plain,(
% 1.79/0.93    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.79/0.93    inference(cnf_transformation,[],[f3])).
% 1.79/0.93  
% 1.79/0.93  fof(f33,plain,(
% 1.79/0.93    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.79/0.93    inference(definition_unfolding,[],[f20,f32])).
% 1.79/0.93  
% 1.79/0.93  fof(f38,plain,(
% 1.79/0.93    ( ! [X2,X0,X1] : (k2_enumset1(X1,X1,X1,X2) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 1.79/0.93    inference(definition_unfolding,[],[f23,f32,f33,f33,f32])).
% 1.79/0.93  
% 1.79/0.93  fof(f31,plain,(
% 1.79/0.93    sK0 != sK3),
% 1.79/0.93    inference(cnf_transformation,[],[f17])).
% 1.79/0.93  
% 1.79/0.93  fof(f7,axiom,(
% 1.79/0.93    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.79/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.79/0.93  
% 1.79/0.93  fof(f12,plain,(
% 1.79/0.93    ! [X0,X1,X2] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.79/0.93    inference(ennf_transformation,[],[f7])).
% 1.79/0.93  
% 1.79/0.93  fof(f28,plain,(
% 1.79/0.93    ( ! [X2,X0,X1] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.79/0.93    inference(cnf_transformation,[],[f12])).
% 1.79/0.93  
% 1.79/0.93  fof(f39,plain,(
% 1.79/0.93    ( ! [X2,X0,X1] : (X0 = X2 | X0 = X1 | ~r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))) )),
% 1.79/0.93    inference(definition_unfolding,[],[f28,f33,f32])).
% 1.79/0.93  
% 1.79/0.93  fof(f25,plain,(
% 1.79/0.93    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 1.79/0.93    inference(cnf_transformation,[],[f15])).
% 1.79/0.93  
% 1.79/0.93  fof(f36,plain,(
% 1.79/0.93    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X1,X1,X1,X1) != X0) )),
% 1.79/0.93    inference(definition_unfolding,[],[f25,f32,f33])).
% 1.79/0.93  
% 1.79/0.93  fof(f43,plain,(
% 1.79/0.93    ( ! [X2,X1] : (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))) )),
% 1.79/0.93    inference(equality_resolution,[],[f36])).
% 1.79/0.93  
% 1.79/0.93  fof(f26,plain,(
% 1.79/0.93    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 1.79/0.93    inference(cnf_transformation,[],[f15])).
% 1.79/0.93  
% 1.79/0.93  fof(f35,plain,(
% 1.79/0.93    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X2,X2,X2,X2) != X0) )),
% 1.79/0.93    inference(definition_unfolding,[],[f26,f32,f33])).
% 1.79/0.93  
% 1.79/0.93  fof(f42,plain,(
% 1.79/0.93    ( ! [X2,X1] : (r1_tarski(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X2))) )),
% 1.79/0.93    inference(equality_resolution,[],[f35])).
% 1.79/0.93  
% 1.79/0.93  fof(f30,plain,(
% 1.79/0.93    sK0 != sK2),
% 1.79/0.93    inference(cnf_transformation,[],[f17])).
% 1.79/0.93  
% 1.79/0.93  cnf(c_5,plain,
% 1.79/0.93      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X1)) ),
% 1.79/0.93      inference(cnf_transformation,[],[f44]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_421,plain,
% 1.79/0.93      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 1.79/0.93      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1,plain,
% 1.79/0.93      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 1.79/0.93      inference(cnf_transformation,[],[f19]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_425,plain,
% 1.79/0.93      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 1.79/0.93      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_745,plain,
% 1.79/0.93      ( k2_xboole_0(k1_xboole_0,k2_enumset1(X0,X0,X0,X1)) = k2_enumset1(X0,X0,X0,X1) ),
% 1.79/0.93      inference(superposition,[status(thm)],[c_421,c_425]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_0,plain,
% 1.79/0.93      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 1.79/0.93      inference(cnf_transformation,[],[f18]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_10,negated_conjecture,
% 1.79/0.93      ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) ),
% 1.79/0.93      inference(cnf_transformation,[],[f40]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_418,plain,
% 1.79/0.93      ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) = iProver_top ),
% 1.79/0.93      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_6,plain,
% 1.79/0.93      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
% 1.79/0.93      | k2_enumset1(X1,X1,X1,X2) = X0
% 1.79/0.93      | k2_enumset1(X2,X2,X2,X2) = X0
% 1.79/0.93      | k2_enumset1(X1,X1,X1,X1) = X0
% 1.79/0.93      | k1_xboole_0 = X0 ),
% 1.79/0.93      inference(cnf_transformation,[],[f38]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_420,plain,
% 1.79/0.93      ( k2_enumset1(X0,X0,X0,X1) = X2
% 1.79/0.93      | k2_enumset1(X1,X1,X1,X1) = X2
% 1.79/0.93      | k2_enumset1(X0,X0,X0,X0) = X2
% 1.79/0.93      | k1_xboole_0 = X2
% 1.79/0.93      | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 1.79/0.93      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1092,plain,
% 1.79/0.93      ( k2_enumset1(sK2,sK2,sK2,sK2) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK2,sK2,sK2,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0 ),
% 1.79/0.93      inference(superposition,[status(thm)],[c_418,c_420]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1300,plain,
% 1.79/0.93      ( k2_enumset1(sK2,sK2,sK2,sK2) = X0
% 1.79/0.93      | k2_enumset1(sK2,sK2,sK2,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
% 1.79/0.93      | k1_xboole_0 = X0
% 1.79/0.93      | r1_tarski(X0,k2_enumset1(sK0,sK0,sK0,sK1)) != iProver_top ),
% 1.79/0.93      inference(superposition,[status(thm)],[c_1092,c_420]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_8,negated_conjecture,
% 1.79/0.93      ( sK0 != sK3 ),
% 1.79/0.93      inference(cnf_transformation,[],[f31]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_7,plain,
% 1.79/0.93      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X2))
% 1.79/0.93      | X1 = X0
% 1.79/0.93      | X2 = X0 ),
% 1.79/0.93      inference(cnf_transformation,[],[f39]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_13,plain,
% 1.79/0.93      ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
% 1.79/0.93      | sK0 = sK0 ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_7]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_4,plain,
% 1.79/0.93      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) ),
% 1.79/0.93      inference(cnf_transformation,[],[f43]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_22,plain,
% 1.79/0.93      ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_4]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_284,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_485,plain,
% 1.79/0.93      ( sK3 != X0 | sK0 != X0 | sK0 = sK3 ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_284]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_486,plain,
% 1.79/0.93      ( sK3 != sK0 | sK0 = sK3 | sK0 != sK0 ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_485]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1293,plain,
% 1.79/0.93      ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_4]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1294,plain,
% 1.79/0.93      ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) = iProver_top ),
% 1.79/0.93      inference(predicate_to_equality,[status(thm)],[c_1293]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_3,plain,
% 1.79/0.93      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X0)) ),
% 1.79/0.93      inference(cnf_transformation,[],[f42]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_423,plain,
% 1.79/0.93      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 1.79/0.93      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1305,plain,
% 1.79/0.93      ( k2_enumset1(sK2,sK2,sK2,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
% 1.79/0.93      | r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(X0,X0,X0,sK2)) = iProver_top ),
% 1.79/0.93      inference(superposition,[status(thm)],[c_1092,c_423]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_9,negated_conjecture,
% 1.79/0.93      ( sK0 != sK2 ),
% 1.79/0.93      inference(cnf_transformation,[],[f30]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_487,plain,
% 1.79/0.93      ( sK2 != X0 | sK0 != X0 | sK0 = sK2 ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_284]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_488,plain,
% 1.79/0.93      ( sK2 != sK0 | sK0 = sK2 | sK0 != sK0 ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_487]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_419,plain,
% 1.79/0.93      ( X0 = X1
% 1.79/0.93      | X2 = X1
% 1.79/0.93      | r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X0,X0,X0,X2)) != iProver_top ),
% 1.79/0.93      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1309,plain,
% 1.79/0.93      ( k2_enumset1(sK2,sK2,sK2,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
% 1.79/0.93      | sK2 = X0
% 1.79/0.93      | r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK0,sK0,sK0,sK1)) != iProver_top ),
% 1.79/0.93      inference(superposition,[status(thm)],[c_1092,c_419]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1390,plain,
% 1.79/0.93      ( k2_enumset1(sK2,sK2,sK2,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
% 1.79/0.93      | sK2 = sK0
% 1.79/0.93      | r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) != iProver_top ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_1309]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1393,plain,
% 1.79/0.93      ( k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
% 1.79/0.93      | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK2,sK2,sK2,sK3) = k2_enumset1(sK0,sK0,sK0,sK1) ),
% 1.79/0.93      inference(global_propositional_subsumption,
% 1.79/0.93                [status(thm)],
% 1.79/0.93                [c_1305,c_9,c_13,c_22,c_488,c_1294,c_1390]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1394,plain,
% 1.79/0.93      ( k2_enumset1(sK2,sK2,sK2,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0 ),
% 1.79/0.93      inference(renaming,[status(thm)],[c_1393]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_746,plain,
% 1.79/0.93      ( k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3)) = k2_enumset1(sK2,sK2,sK2,sK3) ),
% 1.79/0.93      inference(superposition,[status(thm)],[c_418,c_425]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1404,plain,
% 1.79/0.93      ( k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
% 1.79/0.93      | k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK0,sK0,sK0,sK1)) = k2_enumset1(sK2,sK2,sK2,sK3) ),
% 1.79/0.93      inference(superposition,[status(thm)],[c_1394,c_746]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1406,plain,
% 1.79/0.93      ( k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
% 1.79/0.93      | sK2 = X0
% 1.79/0.93      | sK3 = X0
% 1.79/0.93      | r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK0,sK0,sK0,sK1)) != iProver_top ),
% 1.79/0.93      inference(superposition,[status(thm)],[c_1394,c_419]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1460,plain,
% 1.79/0.93      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK0,sK0,sK0,sK1))
% 1.79/0.93      | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
% 1.79/0.93      | sK2 = X0
% 1.79/0.93      | sK3 = X0 ),
% 1.79/0.93      inference(predicate_to_equality_rev,[status(thm)],[c_1406]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1462,plain,
% 1.79/0.93      ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1))
% 1.79/0.93      | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
% 1.79/0.93      | sK2 = sK0
% 1.79/0.93      | sK3 = sK0 ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_1460]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1532,plain,
% 1.79/0.93      ( k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
% 1.79/0.93      | k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1) ),
% 1.79/0.93      inference(global_propositional_subsumption,
% 1.79/0.93                [status(thm)],
% 1.79/0.93                [c_1404,c_9,c_8,c_13,c_22,c_486,c_488,c_1294,c_1461]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1533,plain,
% 1.79/0.93      ( k2_enumset1(sK3,sK3,sK3,sK3) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0 ),
% 1.79/0.93      inference(renaming,[status(thm)],[c_1532]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1545,plain,
% 1.79/0.93      ( k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
% 1.79/0.93      | sK3 = X0
% 1.79/0.93      | r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK0,sK0,sK0,sK1)) != iProver_top ),
% 1.79/0.93      inference(superposition,[status(thm)],[c_1533,c_419]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1598,plain,
% 1.79/0.93      ( k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0
% 1.79/0.93      | sK3 = sK0
% 1.79/0.93      | r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK1)) != iProver_top ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_1545]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1601,plain,
% 1.79/0.93      ( k2_enumset1(sK0,sK0,sK0,sK1) = k1_xboole_0 ),
% 1.79/0.93      inference(global_propositional_subsumption,
% 1.79/0.93                [status(thm)],
% 1.79/0.93                [c_1300,c_8,c_13,c_22,c_486,c_1294,c_1598]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1617,plain,
% 1.79/0.93      ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) = iProver_top ),
% 1.79/0.93      inference(superposition,[status(thm)],[c_1601,c_423]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_1950,plain,
% 1.79/0.93      ( k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) = k1_xboole_0 ),
% 1.79/0.93      inference(superposition,[status(thm)],[c_1617,c_425]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_2854,plain,
% 1.79/0.93      ( k2_xboole_0(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1)) = k1_xboole_0 ),
% 1.79/0.93      inference(superposition,[status(thm)],[c_0,c_1950]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_2954,plain,
% 1.79/0.93      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0 ),
% 1.79/0.93      inference(superposition,[status(thm)],[c_745,c_2854]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_3127,plain,
% 1.79/0.93      ( sK1 = X0
% 1.79/0.93      | sK1 = X1
% 1.79/0.93      | r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 1.79/0.93      inference(superposition,[status(thm)],[c_2954,c_419]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_3154,plain,
% 1.79/0.93      ( sK1 = sK0
% 1.79/0.93      | r1_tarski(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) != iProver_top ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_3127]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_2039,plain,
% 1.79/0.93      ( X0 != X1 | X0 = sK1 | sK1 != X1 ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_284]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_2040,plain,
% 1.79/0.93      ( sK1 != sK0 | sK0 = sK1 | sK0 != sK0 ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_2039]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_572,plain,
% 1.79/0.93      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK2,sK2,sK2,X1))
% 1.79/0.93      | X1 = X0
% 1.79/0.93      | sK2 = X0 ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_7]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_938,plain,
% 1.79/0.93      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k2_enumset1(sK2,sK2,sK2,sK3))
% 1.79/0.93      | sK2 = X0
% 1.79/0.93      | sK3 = X0 ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_572]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_940,plain,
% 1.79/0.93      ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK2,sK2,sK2,sK3))
% 1.79/0.93      | sK2 = sK0
% 1.79/0.93      | sK3 = sK0 ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_938]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_286,plain,
% 1.79/0.93      ( X0 != X1
% 1.79/0.93      | X2 != X3
% 1.79/0.93      | X4 != X5
% 1.79/0.93      | X6 != X7
% 1.79/0.93      | k2_enumset1(X0,X2,X4,X6) = k2_enumset1(X1,X3,X5,X7) ),
% 1.79/0.93      theory(equality) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_778,plain,
% 1.79/0.93      ( X0 != sK1
% 1.79/0.93      | X1 != sK0
% 1.79/0.93      | X2 != sK0
% 1.79/0.93      | X3 != sK0
% 1.79/0.93      | k2_enumset1(X1,X2,X3,X0) = k2_enumset1(sK0,sK0,sK0,sK1) ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_286]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_783,plain,
% 1.79/0.93      ( k2_enumset1(sK0,sK0,sK0,sK0) = k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | sK0 != sK1
% 1.79/0.93      | sK0 != sK0 ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_778]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_285,plain,
% 1.79/0.93      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.79/0.93      theory(equality) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_516,plain,
% 1.79/0.93      ( r1_tarski(X0,X1)
% 1.79/0.93      | ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))
% 1.79/0.93      | X1 != k2_enumset1(sK2,sK2,sK2,sK3)
% 1.79/0.93      | X0 != k2_enumset1(sK0,sK0,sK0,sK1) ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_285]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_599,plain,
% 1.79/0.93      ( r1_tarski(X0,k2_enumset1(sK2,sK2,sK2,sK3))
% 1.79/0.93      | ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))
% 1.79/0.93      | X0 != k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK2,sK2,sK2,sK3) != k2_enumset1(sK2,sK2,sK2,sK3) ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_516]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_777,plain,
% 1.79/0.93      ( r1_tarski(k2_enumset1(X0,X1,X2,X3),k2_enumset1(sK2,sK2,sK2,sK3))
% 1.79/0.93      | ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))
% 1.79/0.93      | k2_enumset1(X0,X1,X2,X3) != k2_enumset1(sK0,sK0,sK0,sK1)
% 1.79/0.93      | k2_enumset1(sK2,sK2,sK2,sK3) != k2_enumset1(sK2,sK2,sK2,sK3) ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_599]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_780,plain,
% 1.79/0.93      ( ~ r1_tarski(k2_enumset1(sK0,sK0,sK0,sK1),k2_enumset1(sK2,sK2,sK2,sK3))
% 1.79/0.93      | r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK2,sK2,sK2,sK3))
% 1.79/0.93      | k2_enumset1(sK2,sK2,sK2,sK3) != k2_enumset1(sK2,sK2,sK2,sK3)
% 1.79/0.93      | k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK1) ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_777]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_283,plain,( X0 = X0 ),theory(equality) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_600,plain,
% 1.79/0.93      ( k2_enumset1(sK2,sK2,sK2,sK3) = k2_enumset1(sK2,sK2,sK2,sK3) ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_283]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_18,plain,
% 1.79/0.93      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X0,X1)) = iProver_top ),
% 1.79/0.93      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(c_20,plain,
% 1.79/0.93      ( r1_tarski(k1_xboole_0,k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 1.79/0.93      inference(instantiation,[status(thm)],[c_18]) ).
% 1.79/0.93  
% 1.79/0.93  cnf(contradiction,plain,
% 1.79/0.93      ( $false ),
% 1.79/0.93      inference(minisat,
% 1.79/0.93                [status(thm)],
% 1.79/0.93                [c_3154,c_2040,c_940,c_783,c_780,c_600,c_488,c_486,c_22,
% 1.79/0.93                 c_20,c_13,c_8,c_9,c_10]) ).
% 1.79/0.93  
% 1.79/0.93  
% 1.79/0.93  % SZS output end CNFRefutation for theBenchmark.p
% 1.79/0.93  
% 1.79/0.93  ------                               Statistics
% 1.79/0.93  
% 1.79/0.93  ------ General
% 1.79/0.93  
% 1.79/0.93  abstr_ref_over_cycles:                  0
% 1.79/0.93  abstr_ref_under_cycles:                 0
% 1.79/0.93  gc_basic_clause_elim:                   0
% 1.79/0.93  forced_gc_time:                         0
% 1.79/0.93  parsing_time:                           0.013
% 1.79/0.93  unif_index_cands_time:                  0.
% 1.79/0.93  unif_index_add_time:                    0.
% 1.79/0.93  orderings_time:                         0.
% 1.79/0.93  out_proof_time:                         0.008
% 1.79/0.93  total_time:                             0.147
% 1.79/0.93  num_of_symbols:                         39
% 1.79/0.93  num_of_terms:                           3193
% 1.79/0.93  
% 1.79/0.93  ------ Preprocessing
% 1.79/0.93  
% 1.79/0.93  num_of_splits:                          0
% 1.79/0.93  num_of_split_atoms:                     0
% 1.79/0.93  num_of_reused_defs:                     0
% 1.79/0.93  num_eq_ax_congr_red:                    4
% 1.79/0.93  num_of_sem_filtered_clauses:            1
% 1.79/0.93  num_of_subtypes:                        0
% 1.79/0.93  monotx_restored_types:                  0
% 1.79/0.93  sat_num_of_epr_types:                   0
% 1.79/0.93  sat_num_of_non_cyclic_types:            0
% 1.79/0.93  sat_guarded_non_collapsed_types:        0
% 1.79/0.93  num_pure_diseq_elim:                    0
% 1.79/0.93  simp_replaced_by:                       0
% 1.79/0.93  res_preprocessed:                       42
% 1.79/0.93  prep_upred:                             0
% 1.79/0.93  prep_unflattend:                        15
% 1.79/0.93  smt_new_axioms:                         0
% 1.79/0.93  pred_elim_cands:                        1
% 1.79/0.93  pred_elim:                              0
% 1.79/0.93  pred_elim_cl:                           0
% 1.79/0.93  pred_elim_cycles:                       1
% 1.79/0.93  merged_defs:                            0
% 1.79/0.93  merged_defs_ncl:                        0
% 1.79/0.93  bin_hyper_res:                          0
% 1.79/0.93  prep_cycles:                            3
% 1.79/0.93  pred_elim_time:                         0.003
% 1.79/0.93  splitting_time:                         0.
% 1.79/0.93  sem_filter_time:                        0.
% 1.79/0.93  monotx_time:                            0.
% 1.79/0.93  subtype_inf_time:                       0.
% 1.79/0.93  
% 1.79/0.93  ------ Problem properties
% 1.79/0.93  
% 1.79/0.93  clauses:                                11
% 1.79/0.93  conjectures:                            3
% 1.79/0.93  epr:                                    2
% 1.79/0.93  horn:                                   9
% 1.79/0.93  ground:                                 3
% 1.79/0.93  unary:                                  8
% 1.79/0.93  binary:                                 1
% 1.79/0.93  lits:                                   18
% 1.79/0.93  lits_eq:                                10
% 1.79/0.93  fd_pure:                                0
% 1.79/0.93  fd_pseudo:                              0
% 1.79/0.93  fd_cond:                                0
% 1.79/0.93  fd_pseudo_cond:                         2
% 1.79/0.93  ac_symbols:                             0
% 1.79/0.93  
% 1.79/0.93  ------ Propositional Solver
% 1.79/0.93  
% 1.79/0.93  prop_solver_calls:                      22
% 1.79/0.93  prop_fast_solver_calls:                 285
% 1.79/0.93  smt_solver_calls:                       0
% 1.79/0.93  smt_fast_solver_calls:                  0
% 1.79/0.93  prop_num_of_clauses:                    1006
% 1.79/0.93  prop_preprocess_simplified:             3263
% 1.79/0.93  prop_fo_subsumed:                       17
% 1.79/0.93  prop_solver_time:                       0.
% 1.79/0.93  smt_solver_time:                        0.
% 1.79/0.93  smt_fast_solver_time:                   0.
% 1.79/0.93  prop_fast_solver_time:                  0.
% 1.79/0.93  prop_unsat_core_time:                   0.
% 1.79/0.93  
% 1.79/0.93  ------ QBF
% 1.79/0.93  
% 1.79/0.93  qbf_q_res:                              0
% 1.79/0.93  qbf_num_tautologies:                    0
% 1.79/0.93  qbf_prep_cycles:                        0
% 1.79/0.93  
% 1.79/0.93  ------ BMC1
% 1.79/0.93  
% 1.79/0.93  bmc1_current_bound:                     -1
% 1.79/0.93  bmc1_last_solved_bound:                 -1
% 1.79/0.93  bmc1_unsat_core_size:                   -1
% 1.79/0.93  bmc1_unsat_core_parents_size:           -1
% 1.79/0.93  bmc1_merge_next_fun:                    0
% 1.79/0.93  bmc1_unsat_core_clauses_time:           0.
% 1.79/0.93  
% 1.79/0.93  ------ Instantiation
% 1.79/0.93  
% 1.79/0.93  inst_num_of_clauses:                    342
% 1.79/0.93  inst_num_in_passive:                    154
% 1.79/0.93  inst_num_in_active:                     158
% 1.79/0.93  inst_num_in_unprocessed:                30
% 1.79/0.93  inst_num_of_loops:                      170
% 1.79/0.93  inst_num_of_learning_restarts:          0
% 1.79/0.93  inst_num_moves_active_passive:          12
% 1.79/0.93  inst_lit_activity:                      0
% 1.79/0.93  inst_lit_activity_moves:                0
% 1.79/0.93  inst_num_tautologies:                   0
% 1.79/0.93  inst_num_prop_implied:                  0
% 1.79/0.93  inst_num_existing_simplified:           0
% 1.79/0.93  inst_num_eq_res_simplified:             0
% 1.79/0.93  inst_num_child_elim:                    0
% 1.79/0.94  inst_num_of_dismatching_blockings:      320
% 1.79/0.94  inst_num_of_non_proper_insts:           445
% 1.79/0.94  inst_num_of_duplicates:                 0
% 1.79/0.94  inst_inst_num_from_inst_to_res:         0
% 1.79/0.94  inst_dismatching_checking_time:         0.
% 1.79/0.94  
% 1.79/0.94  ------ Resolution
% 1.79/0.94  
% 1.79/0.94  res_num_of_clauses:                     0
% 1.79/0.94  res_num_in_passive:                     0
% 1.79/0.94  res_num_in_active:                      0
% 1.79/0.94  res_num_of_loops:                       45
% 1.79/0.94  res_forward_subset_subsumed:            109
% 1.79/0.94  res_backward_subset_subsumed:           0
% 1.79/0.94  res_forward_subsumed:                   0
% 1.79/0.94  res_backward_subsumed:                  0
% 1.79/0.94  res_forward_subsumption_resolution:     0
% 1.79/0.94  res_backward_subsumption_resolution:    0
% 1.79/0.94  res_clause_to_clause_subsumption:       215
% 1.79/0.94  res_orphan_elimination:                 0
% 1.79/0.94  res_tautology_del:                      20
% 1.79/0.94  res_num_eq_res_simplified:              0
% 1.79/0.94  res_num_sel_changes:                    0
% 1.79/0.94  res_moves_from_active_to_pass:          0
% 1.79/0.94  
% 1.79/0.94  ------ Superposition
% 1.79/0.94  
% 1.79/0.94  sup_time_total:                         0.
% 1.79/0.94  sup_time_generating:                    0.
% 1.79/0.94  sup_time_sim_full:                      0.
% 1.79/0.94  sup_time_sim_immed:                     0.
% 1.79/0.94  
% 1.79/0.94  sup_num_of_clauses:                     32
% 1.79/0.94  sup_num_in_active:                      22
% 1.79/0.94  sup_num_in_passive:                     10
% 1.79/0.94  sup_num_of_loops:                       33
% 1.79/0.94  sup_fw_superposition:                   36
% 1.79/0.94  sup_bw_superposition:                   94
% 1.79/0.94  sup_immediate_simplified:               30
% 1.79/0.94  sup_given_eliminated:                   0
% 1.79/0.94  comparisons_done:                       0
% 1.79/0.94  comparisons_avoided:                    0
% 1.79/0.94  
% 1.79/0.94  ------ Simplifications
% 1.79/0.94  
% 1.79/0.94  
% 1.79/0.94  sim_fw_subset_subsumed:                 0
% 1.79/0.94  sim_bw_subset_subsumed:                 12
% 1.79/0.94  sim_fw_subsumed:                        17
% 1.79/0.94  sim_bw_subsumed:                        0
% 1.79/0.94  sim_fw_subsumption_res:                 0
% 1.79/0.94  sim_bw_subsumption_res:                 0
% 1.79/0.94  sim_tautology_del:                      0
% 1.79/0.94  sim_eq_tautology_del:                   21
% 1.79/0.94  sim_eq_res_simp:                        0
% 1.79/0.94  sim_fw_demodulated:                     2
% 1.79/0.94  sim_bw_demodulated:                     12
% 1.79/0.94  sim_light_normalised:                   11
% 1.79/0.94  sim_joinable_taut:                      0
% 1.79/0.94  sim_joinable_simp:                      0
% 1.79/0.94  sim_ac_normalised:                      0
% 1.79/0.94  sim_smt_subsumption:                    0
% 1.79/0.94  
%------------------------------------------------------------------------------
