%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:33 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 353 expanded)
%              Number of clauses        :   51 (  89 expanded)
%              Number of leaves         :   14 (  85 expanded)
%              Depth                    :   14
%              Number of atoms          :  254 ( 824 expanded)
%              Number of equality atoms :  127 ( 409 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f16])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f31])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f36])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f22])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f47])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))
      | X0 = X2
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f36,f48])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) ) ),
    inference(definition_unfolding,[],[f43,f36,f48])).

fof(f60,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) ),
    inference(equality_resolution,[],[f54])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK2,sK1)
        | k4_xboole_0(sK1,k1_tarski(sK2)) != sK1 )
      & ( ~ r2_hidden(sK2,sK1)
        | k4_xboole_0(sK1,k1_tarski(sK2)) = sK1 ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ( r2_hidden(sK2,sK1)
      | k4_xboole_0(sK1,k1_tarski(sK2)) != sK1 )
    & ( ~ r2_hidden(sK2,sK1)
      | k4_xboole_0(sK1,k1_tarski(sK2)) = sK1 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f25])).

fof(f46,plain,
    ( r2_hidden(sK2,sK1)
    | k4_xboole_0(sK1,k1_tarski(sK2)) != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,
    ( r2_hidden(sK2,sK1)
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != sK1 ),
    inference(definition_unfolding,[],[f46,f36,f48])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,
    ( ~ r2_hidden(sK2,sK1)
    | k4_xboole_0(sK1,k1_tarski(sK2)) = sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,
    ( ~ r2_hidden(sK2,sK1)
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = sK1 ),
    inference(definition_unfolding,[],[f45,f36,f48])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_871,plain,
    ( r2_hidden(sK0(X0,X1),X1) = iProver_top
    | r1_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_868,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_867,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1208,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_868,c_867])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))
    | X2 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_863,plain,
    ( X0 = X1
    | r2_hidden(X1,X2) != iProver_top
    | r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X0,X0,X0,X0)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1593,plain,
    ( X0 = X1
    | r2_hidden(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top
    | r2_hidden(X1,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1208,c_863])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_862,plain,
    ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1279,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1208,c_862])).

cnf(c_2284,plain,
    ( X0 = X1
    | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1593,c_1279])).

cnf(c_2286,plain,
    ( sK0(X0,k2_enumset1(X1,X1,X1,X1)) = X1
    | r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_871,c_2284])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_864,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2319,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0
    | sK0(X0,k2_enumset1(X1,X1,X1,X1)) = X1 ),
    inference(superposition,[status(thm)],[c_2286,c_864])).

cnf(c_3367,plain,
    ( sK0(X0,k2_enumset1(X1,X1,X1,X1)) = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2319,c_862])).

cnf(c_14,negated_conjecture,
    ( r2_hidden(sK2,sK1)
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != sK1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_860,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != sK1
    | r2_hidden(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3368,plain,
    ( sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = sK2
    | r2_hidden(sK2,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2319,c_860])).

cnf(c_3422,plain,
    ( sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = sK2 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_3367,c_3368])).

cnf(c_511,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1186,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK1)
    | X0 != sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | X1 != sK1 ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_2365,plain,
    ( r2_hidden(X0,sK1)
    | ~ r2_hidden(sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK1)
    | X0 != sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1186])).

cnf(c_2367,plain,
    ( ~ r2_hidden(sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK1)
    | r2_hidden(sK2,sK1)
    | sK1 != sK1
    | sK2 != sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_2365])).

cnf(c_509,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2252,plain,
    ( X0 != X1
    | X0 = sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_509])).

cnf(c_2253,plain,
    ( sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != sK2
    | sK2 = sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2252])).

cnf(c_1491,plain,
    ( ~ r2_hidden(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(X0,X0,X0,X0)))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1496,plain,
    ( r2_hidden(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(X0,X0,X0,X0)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1491])).

cnf(c_1498,plain,
    ( r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1496])).

cnf(c_1048,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK2,sK1)
    | X1 != sK1
    | X0 != sK2 ),
    inference(instantiation,[status(thm)],[c_511])).

cnf(c_1090,plain,
    ( r2_hidden(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X1)))
    | ~ r2_hidden(sK2,sK1)
    | X0 != sK2
    | k5_xboole_0(sK1,k3_xboole_0(sK1,X1)) != sK1 ),
    inference(instantiation,[status(thm)],[c_1048])).

cnf(c_1490,plain,
    ( r2_hidden(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(X0,X0,X0,X0))))
    | ~ r2_hidden(sK2,sK1)
    | X0 != sK2
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(X0,X0,X0,X0))) != sK1 ),
    inference(instantiation,[status(thm)],[c_1090])).

cnf(c_1492,plain,
    ( X0 != sK2
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(X0,X0,X0,X0))) != sK1
    | r2_hidden(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(X0,X0,X0,X0)))) = iProver_top
    | r2_hidden(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1490])).

cnf(c_1494,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != sK1
    | sK2 != sK2
    | r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
    | r2_hidden(sK2,sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1492])).

cnf(c_1014,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f33])).

cnf(c_996,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1013,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_996])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_988,plain,
    ( r2_hidden(sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK1)
    | r1_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_971,plain,
    ( ~ r1_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = sK1 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_44,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_40,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_17,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != sK1
    | r2_hidden(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_15,negated_conjecture,
    ( ~ r2_hidden(sK2,sK1)
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = sK1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_16,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = sK1
    | r2_hidden(sK2,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3422,c_2367,c_2253,c_1498,c_1494,c_1014,c_1013,c_988,c_971,c_44,c_40,c_17,c_16,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:56:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.23/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.01  
% 3.23/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.23/1.01  
% 3.23/1.01  ------  iProver source info
% 3.23/1.01  
% 3.23/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.23/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.23/1.01  git: non_committed_changes: false
% 3.23/1.01  git: last_make_outside_of_git: false
% 3.23/1.01  
% 3.23/1.01  ------ 
% 3.23/1.01  
% 3.23/1.01  ------ Input Options
% 3.23/1.01  
% 3.23/1.01  --out_options                           all
% 3.23/1.01  --tptp_safe_out                         true
% 3.23/1.01  --problem_path                          ""
% 3.23/1.01  --include_path                          ""
% 3.23/1.01  --clausifier                            res/vclausify_rel
% 3.23/1.01  --clausifier_options                    --mode clausify
% 3.23/1.01  --stdin                                 false
% 3.23/1.01  --stats_out                             all
% 3.23/1.01  
% 3.23/1.01  ------ General Options
% 3.23/1.01  
% 3.23/1.01  --fof                                   false
% 3.23/1.01  --time_out_real                         305.
% 3.23/1.01  --time_out_virtual                      -1.
% 3.23/1.01  --symbol_type_check                     false
% 3.23/1.01  --clausify_out                          false
% 3.23/1.01  --sig_cnt_out                           false
% 3.23/1.01  --trig_cnt_out                          false
% 3.23/1.01  --trig_cnt_out_tolerance                1.
% 3.23/1.01  --trig_cnt_out_sk_spl                   false
% 3.23/1.01  --abstr_cl_out                          false
% 3.23/1.01  
% 3.23/1.01  ------ Global Options
% 3.23/1.01  
% 3.23/1.01  --schedule                              default
% 3.23/1.01  --add_important_lit                     false
% 3.23/1.01  --prop_solver_per_cl                    1000
% 3.23/1.01  --min_unsat_core                        false
% 3.23/1.01  --soft_assumptions                      false
% 3.23/1.01  --soft_lemma_size                       3
% 3.23/1.01  --prop_impl_unit_size                   0
% 3.23/1.01  --prop_impl_unit                        []
% 3.23/1.01  --share_sel_clauses                     true
% 3.23/1.01  --reset_solvers                         false
% 3.23/1.01  --bc_imp_inh                            [conj_cone]
% 3.23/1.01  --conj_cone_tolerance                   3.
% 3.23/1.01  --extra_neg_conj                        none
% 3.23/1.01  --large_theory_mode                     true
% 3.23/1.01  --prolific_symb_bound                   200
% 3.23/1.01  --lt_threshold                          2000
% 3.23/1.01  --clause_weak_htbl                      true
% 3.23/1.01  --gc_record_bc_elim                     false
% 3.23/1.01  
% 3.23/1.01  ------ Preprocessing Options
% 3.23/1.01  
% 3.23/1.01  --preprocessing_flag                    true
% 3.23/1.01  --time_out_prep_mult                    0.1
% 3.23/1.01  --splitting_mode                        input
% 3.23/1.01  --splitting_grd                         true
% 3.23/1.01  --splitting_cvd                         false
% 3.23/1.01  --splitting_cvd_svl                     false
% 3.23/1.01  --splitting_nvd                         32
% 3.23/1.01  --sub_typing                            true
% 3.23/1.01  --prep_gs_sim                           true
% 3.23/1.01  --prep_unflatten                        true
% 3.23/1.01  --prep_res_sim                          true
% 3.23/1.01  --prep_upred                            true
% 3.23/1.01  --prep_sem_filter                       exhaustive
% 3.23/1.01  --prep_sem_filter_out                   false
% 3.23/1.01  --pred_elim                             true
% 3.23/1.01  --res_sim_input                         true
% 3.23/1.01  --eq_ax_congr_red                       true
% 3.23/1.01  --pure_diseq_elim                       true
% 3.23/1.01  --brand_transform                       false
% 3.23/1.01  --non_eq_to_eq                          false
% 3.23/1.01  --prep_def_merge                        true
% 3.23/1.01  --prep_def_merge_prop_impl              false
% 3.23/1.01  --prep_def_merge_mbd                    true
% 3.23/1.01  --prep_def_merge_tr_red                 false
% 3.23/1.01  --prep_def_merge_tr_cl                  false
% 3.23/1.01  --smt_preprocessing                     true
% 3.23/1.01  --smt_ac_axioms                         fast
% 3.23/1.01  --preprocessed_out                      false
% 3.23/1.01  --preprocessed_stats                    false
% 3.23/1.01  
% 3.23/1.01  ------ Abstraction refinement Options
% 3.23/1.01  
% 3.23/1.01  --abstr_ref                             []
% 3.23/1.01  --abstr_ref_prep                        false
% 3.23/1.01  --abstr_ref_until_sat                   false
% 3.23/1.01  --abstr_ref_sig_restrict                funpre
% 3.23/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/1.01  --abstr_ref_under                       []
% 3.23/1.01  
% 3.23/1.01  ------ SAT Options
% 3.23/1.01  
% 3.23/1.01  --sat_mode                              false
% 3.23/1.01  --sat_fm_restart_options                ""
% 3.23/1.01  --sat_gr_def                            false
% 3.23/1.01  --sat_epr_types                         true
% 3.23/1.01  --sat_non_cyclic_types                  false
% 3.23/1.01  --sat_finite_models                     false
% 3.23/1.01  --sat_fm_lemmas                         false
% 3.23/1.01  --sat_fm_prep                           false
% 3.23/1.01  --sat_fm_uc_incr                        true
% 3.23/1.01  --sat_out_model                         small
% 3.23/1.01  --sat_out_clauses                       false
% 3.23/1.01  
% 3.23/1.01  ------ QBF Options
% 3.23/1.01  
% 3.23/1.01  --qbf_mode                              false
% 3.23/1.01  --qbf_elim_univ                         false
% 3.23/1.01  --qbf_dom_inst                          none
% 3.23/1.01  --qbf_dom_pre_inst                      false
% 3.23/1.01  --qbf_sk_in                             false
% 3.23/1.01  --qbf_pred_elim                         true
% 3.23/1.01  --qbf_split                             512
% 3.23/1.01  
% 3.23/1.01  ------ BMC1 Options
% 3.23/1.01  
% 3.23/1.01  --bmc1_incremental                      false
% 3.23/1.01  --bmc1_axioms                           reachable_all
% 3.23/1.01  --bmc1_min_bound                        0
% 3.23/1.01  --bmc1_max_bound                        -1
% 3.23/1.01  --bmc1_max_bound_default                -1
% 3.23/1.01  --bmc1_symbol_reachability              true
% 3.23/1.01  --bmc1_property_lemmas                  false
% 3.23/1.01  --bmc1_k_induction                      false
% 3.23/1.01  --bmc1_non_equiv_states                 false
% 3.23/1.01  --bmc1_deadlock                         false
% 3.23/1.01  --bmc1_ucm                              false
% 3.23/1.01  --bmc1_add_unsat_core                   none
% 3.23/1.01  --bmc1_unsat_core_children              false
% 3.23/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/1.01  --bmc1_out_stat                         full
% 3.23/1.01  --bmc1_ground_init                      false
% 3.23/1.01  --bmc1_pre_inst_next_state              false
% 3.23/1.01  --bmc1_pre_inst_state                   false
% 3.23/1.01  --bmc1_pre_inst_reach_state             false
% 3.23/1.01  --bmc1_out_unsat_core                   false
% 3.23/1.01  --bmc1_aig_witness_out                  false
% 3.23/1.01  --bmc1_verbose                          false
% 3.23/1.01  --bmc1_dump_clauses_tptp                false
% 3.23/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.23/1.01  --bmc1_dump_file                        -
% 3.23/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.23/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.23/1.01  --bmc1_ucm_extend_mode                  1
% 3.23/1.01  --bmc1_ucm_init_mode                    2
% 3.23/1.01  --bmc1_ucm_cone_mode                    none
% 3.23/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.23/1.01  --bmc1_ucm_relax_model                  4
% 3.23/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.23/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/1.01  --bmc1_ucm_layered_model                none
% 3.23/1.01  --bmc1_ucm_max_lemma_size               10
% 3.23/1.01  
% 3.23/1.01  ------ AIG Options
% 3.23/1.01  
% 3.23/1.01  --aig_mode                              false
% 3.23/1.01  
% 3.23/1.01  ------ Instantiation Options
% 3.23/1.01  
% 3.23/1.01  --instantiation_flag                    true
% 3.23/1.01  --inst_sos_flag                         false
% 3.23/1.01  --inst_sos_phase                        true
% 3.23/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/1.01  --inst_lit_sel_side                     num_symb
% 3.23/1.01  --inst_solver_per_active                1400
% 3.23/1.01  --inst_solver_calls_frac                1.
% 3.23/1.01  --inst_passive_queue_type               priority_queues
% 3.23/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/1.01  --inst_passive_queues_freq              [25;2]
% 3.23/1.01  --inst_dismatching                      true
% 3.23/1.01  --inst_eager_unprocessed_to_passive     true
% 3.23/1.01  --inst_prop_sim_given                   true
% 3.23/1.01  --inst_prop_sim_new                     false
% 3.23/1.01  --inst_subs_new                         false
% 3.23/1.01  --inst_eq_res_simp                      false
% 3.23/1.01  --inst_subs_given                       false
% 3.23/1.01  --inst_orphan_elimination               true
% 3.23/1.01  --inst_learning_loop_flag               true
% 3.23/1.01  --inst_learning_start                   3000
% 3.23/1.01  --inst_learning_factor                  2
% 3.23/1.01  --inst_start_prop_sim_after_learn       3
% 3.23/1.01  --inst_sel_renew                        solver
% 3.23/1.01  --inst_lit_activity_flag                true
% 3.23/1.01  --inst_restr_to_given                   false
% 3.23/1.01  --inst_activity_threshold               500
% 3.23/1.01  --inst_out_proof                        true
% 3.23/1.01  
% 3.23/1.01  ------ Resolution Options
% 3.23/1.01  
% 3.23/1.01  --resolution_flag                       true
% 3.23/1.01  --res_lit_sel                           adaptive
% 3.23/1.01  --res_lit_sel_side                      none
% 3.23/1.01  --res_ordering                          kbo
% 3.23/1.01  --res_to_prop_solver                    active
% 3.23/1.01  --res_prop_simpl_new                    false
% 3.23/1.01  --res_prop_simpl_given                  true
% 3.23/1.01  --res_passive_queue_type                priority_queues
% 3.23/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/1.01  --res_passive_queues_freq               [15;5]
% 3.23/1.01  --res_forward_subs                      full
% 3.23/1.01  --res_backward_subs                     full
% 3.23/1.01  --res_forward_subs_resolution           true
% 3.23/1.01  --res_backward_subs_resolution          true
% 3.23/1.01  --res_orphan_elimination                true
% 3.23/1.01  --res_time_limit                        2.
% 3.23/1.01  --res_out_proof                         true
% 3.23/1.01  
% 3.23/1.01  ------ Superposition Options
% 3.23/1.01  
% 3.23/1.01  --superposition_flag                    true
% 3.23/1.01  --sup_passive_queue_type                priority_queues
% 3.23/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.23/1.01  --demod_completeness_check              fast
% 3.23/1.01  --demod_use_ground                      true
% 3.23/1.01  --sup_to_prop_solver                    passive
% 3.23/1.01  --sup_prop_simpl_new                    true
% 3.23/1.01  --sup_prop_simpl_given                  true
% 3.23/1.01  --sup_fun_splitting                     false
% 3.23/1.01  --sup_smt_interval                      50000
% 3.23/1.01  
% 3.23/1.01  ------ Superposition Simplification Setup
% 3.23/1.01  
% 3.23/1.01  --sup_indices_passive                   []
% 3.23/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.01  --sup_full_bw                           [BwDemod]
% 3.23/1.01  --sup_immed_triv                        [TrivRules]
% 3.23/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.01  --sup_immed_bw_main                     []
% 3.23/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.01  
% 3.23/1.01  ------ Combination Options
% 3.23/1.01  
% 3.23/1.01  --comb_res_mult                         3
% 3.23/1.01  --comb_sup_mult                         2
% 3.23/1.01  --comb_inst_mult                        10
% 3.23/1.01  
% 3.23/1.01  ------ Debug Options
% 3.23/1.01  
% 3.23/1.01  --dbg_backtrace                         false
% 3.23/1.01  --dbg_dump_prop_clauses                 false
% 3.23/1.01  --dbg_dump_prop_clauses_file            -
% 3.23/1.01  --dbg_out_stat                          false
% 3.23/1.01  ------ Parsing...
% 3.23/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.23/1.01  
% 3.23/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.23/1.01  
% 3.23/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.23/1.01  
% 3.23/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.23/1.01  ------ Proving...
% 3.23/1.01  ------ Problem Properties 
% 3.23/1.01  
% 3.23/1.01  
% 3.23/1.01  clauses                                 15
% 3.23/1.01  conjectures                             2
% 3.23/1.01  EPR                                     3
% 3.23/1.01  Horn                                    12
% 3.23/1.01  unary                                   3
% 3.23/1.01  binary                                  9
% 3.23/1.01  lits                                    30
% 3.23/1.01  lits eq                                 9
% 3.23/1.01  fd_pure                                 0
% 3.23/1.01  fd_pseudo                               0
% 3.23/1.01  fd_cond                                 0
% 3.23/1.01  fd_pseudo_cond                          2
% 3.23/1.01  AC symbols                              0
% 3.23/1.01  
% 3.23/1.01  ------ Schedule dynamic 5 is on 
% 3.23/1.01  
% 3.23/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.23/1.01  
% 3.23/1.01  
% 3.23/1.01  ------ 
% 3.23/1.01  Current options:
% 3.23/1.01  ------ 
% 3.23/1.01  
% 3.23/1.01  ------ Input Options
% 3.23/1.01  
% 3.23/1.01  --out_options                           all
% 3.23/1.01  --tptp_safe_out                         true
% 3.23/1.01  --problem_path                          ""
% 3.23/1.01  --include_path                          ""
% 3.23/1.01  --clausifier                            res/vclausify_rel
% 3.23/1.01  --clausifier_options                    --mode clausify
% 3.23/1.01  --stdin                                 false
% 3.23/1.01  --stats_out                             all
% 3.23/1.01  
% 3.23/1.01  ------ General Options
% 3.23/1.01  
% 3.23/1.01  --fof                                   false
% 3.23/1.01  --time_out_real                         305.
% 3.23/1.01  --time_out_virtual                      -1.
% 3.23/1.01  --symbol_type_check                     false
% 3.23/1.01  --clausify_out                          false
% 3.23/1.01  --sig_cnt_out                           false
% 3.23/1.01  --trig_cnt_out                          false
% 3.23/1.01  --trig_cnt_out_tolerance                1.
% 3.23/1.01  --trig_cnt_out_sk_spl                   false
% 3.23/1.01  --abstr_cl_out                          false
% 3.23/1.01  
% 3.23/1.01  ------ Global Options
% 3.23/1.01  
% 3.23/1.01  --schedule                              default
% 3.23/1.01  --add_important_lit                     false
% 3.23/1.01  --prop_solver_per_cl                    1000
% 3.23/1.01  --min_unsat_core                        false
% 3.23/1.01  --soft_assumptions                      false
% 3.23/1.01  --soft_lemma_size                       3
% 3.23/1.01  --prop_impl_unit_size                   0
% 3.23/1.01  --prop_impl_unit                        []
% 3.23/1.01  --share_sel_clauses                     true
% 3.23/1.01  --reset_solvers                         false
% 3.23/1.01  --bc_imp_inh                            [conj_cone]
% 3.23/1.01  --conj_cone_tolerance                   3.
% 3.23/1.01  --extra_neg_conj                        none
% 3.23/1.01  --large_theory_mode                     true
% 3.23/1.01  --prolific_symb_bound                   200
% 3.23/1.01  --lt_threshold                          2000
% 3.23/1.01  --clause_weak_htbl                      true
% 3.23/1.01  --gc_record_bc_elim                     false
% 3.23/1.01  
% 3.23/1.01  ------ Preprocessing Options
% 3.23/1.01  
% 3.23/1.01  --preprocessing_flag                    true
% 3.23/1.01  --time_out_prep_mult                    0.1
% 3.23/1.01  --splitting_mode                        input
% 3.23/1.01  --splitting_grd                         true
% 3.23/1.01  --splitting_cvd                         false
% 3.23/1.01  --splitting_cvd_svl                     false
% 3.23/1.01  --splitting_nvd                         32
% 3.23/1.01  --sub_typing                            true
% 3.23/1.01  --prep_gs_sim                           true
% 3.23/1.01  --prep_unflatten                        true
% 3.23/1.01  --prep_res_sim                          true
% 3.23/1.01  --prep_upred                            true
% 3.23/1.01  --prep_sem_filter                       exhaustive
% 3.23/1.01  --prep_sem_filter_out                   false
% 3.23/1.01  --pred_elim                             true
% 3.23/1.01  --res_sim_input                         true
% 3.23/1.01  --eq_ax_congr_red                       true
% 3.23/1.01  --pure_diseq_elim                       true
% 3.23/1.01  --brand_transform                       false
% 3.23/1.01  --non_eq_to_eq                          false
% 3.23/1.01  --prep_def_merge                        true
% 3.23/1.01  --prep_def_merge_prop_impl              false
% 3.23/1.01  --prep_def_merge_mbd                    true
% 3.23/1.01  --prep_def_merge_tr_red                 false
% 3.23/1.01  --prep_def_merge_tr_cl                  false
% 3.23/1.01  --smt_preprocessing                     true
% 3.23/1.01  --smt_ac_axioms                         fast
% 3.23/1.01  --preprocessed_out                      false
% 3.23/1.01  --preprocessed_stats                    false
% 3.23/1.01  
% 3.23/1.01  ------ Abstraction refinement Options
% 3.23/1.01  
% 3.23/1.01  --abstr_ref                             []
% 3.23/1.01  --abstr_ref_prep                        false
% 3.23/1.01  --abstr_ref_until_sat                   false
% 3.23/1.01  --abstr_ref_sig_restrict                funpre
% 3.23/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/1.01  --abstr_ref_under                       []
% 3.23/1.01  
% 3.23/1.01  ------ SAT Options
% 3.23/1.01  
% 3.23/1.01  --sat_mode                              false
% 3.23/1.01  --sat_fm_restart_options                ""
% 3.23/1.01  --sat_gr_def                            false
% 3.23/1.01  --sat_epr_types                         true
% 3.23/1.01  --sat_non_cyclic_types                  false
% 3.23/1.01  --sat_finite_models                     false
% 3.23/1.01  --sat_fm_lemmas                         false
% 3.23/1.01  --sat_fm_prep                           false
% 3.23/1.01  --sat_fm_uc_incr                        true
% 3.23/1.01  --sat_out_model                         small
% 3.23/1.01  --sat_out_clauses                       false
% 3.23/1.01  
% 3.23/1.01  ------ QBF Options
% 3.23/1.01  
% 3.23/1.01  --qbf_mode                              false
% 3.23/1.01  --qbf_elim_univ                         false
% 3.23/1.01  --qbf_dom_inst                          none
% 3.23/1.01  --qbf_dom_pre_inst                      false
% 3.23/1.01  --qbf_sk_in                             false
% 3.23/1.01  --qbf_pred_elim                         true
% 3.23/1.01  --qbf_split                             512
% 3.23/1.01  
% 3.23/1.01  ------ BMC1 Options
% 3.23/1.01  
% 3.23/1.01  --bmc1_incremental                      false
% 3.23/1.01  --bmc1_axioms                           reachable_all
% 3.23/1.01  --bmc1_min_bound                        0
% 3.23/1.01  --bmc1_max_bound                        -1
% 3.23/1.01  --bmc1_max_bound_default                -1
% 3.23/1.01  --bmc1_symbol_reachability              true
% 3.23/1.01  --bmc1_property_lemmas                  false
% 3.23/1.01  --bmc1_k_induction                      false
% 3.23/1.01  --bmc1_non_equiv_states                 false
% 3.23/1.01  --bmc1_deadlock                         false
% 3.23/1.01  --bmc1_ucm                              false
% 3.23/1.01  --bmc1_add_unsat_core                   none
% 3.23/1.01  --bmc1_unsat_core_children              false
% 3.23/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/1.01  --bmc1_out_stat                         full
% 3.23/1.01  --bmc1_ground_init                      false
% 3.23/1.01  --bmc1_pre_inst_next_state              false
% 3.23/1.01  --bmc1_pre_inst_state                   false
% 3.23/1.01  --bmc1_pre_inst_reach_state             false
% 3.23/1.01  --bmc1_out_unsat_core                   false
% 3.23/1.01  --bmc1_aig_witness_out                  false
% 3.23/1.01  --bmc1_verbose                          false
% 3.23/1.01  --bmc1_dump_clauses_tptp                false
% 3.23/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.23/1.01  --bmc1_dump_file                        -
% 3.23/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.23/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.23/1.01  --bmc1_ucm_extend_mode                  1
% 3.23/1.01  --bmc1_ucm_init_mode                    2
% 3.23/1.01  --bmc1_ucm_cone_mode                    none
% 3.23/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.23/1.01  --bmc1_ucm_relax_model                  4
% 3.23/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.23/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/1.01  --bmc1_ucm_layered_model                none
% 3.23/1.01  --bmc1_ucm_max_lemma_size               10
% 3.23/1.01  
% 3.23/1.01  ------ AIG Options
% 3.23/1.01  
% 3.23/1.01  --aig_mode                              false
% 3.23/1.01  
% 3.23/1.01  ------ Instantiation Options
% 3.23/1.01  
% 3.23/1.01  --instantiation_flag                    true
% 3.23/1.01  --inst_sos_flag                         false
% 3.23/1.01  --inst_sos_phase                        true
% 3.23/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/1.01  --inst_lit_sel_side                     none
% 3.23/1.01  --inst_solver_per_active                1400
% 3.23/1.01  --inst_solver_calls_frac                1.
% 3.23/1.01  --inst_passive_queue_type               priority_queues
% 3.23/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/1.01  --inst_passive_queues_freq              [25;2]
% 3.23/1.01  --inst_dismatching                      true
% 3.23/1.01  --inst_eager_unprocessed_to_passive     true
% 3.23/1.01  --inst_prop_sim_given                   true
% 3.23/1.01  --inst_prop_sim_new                     false
% 3.23/1.01  --inst_subs_new                         false
% 3.23/1.01  --inst_eq_res_simp                      false
% 3.23/1.01  --inst_subs_given                       false
% 3.23/1.01  --inst_orphan_elimination               true
% 3.23/1.01  --inst_learning_loop_flag               true
% 3.23/1.01  --inst_learning_start                   3000
% 3.23/1.01  --inst_learning_factor                  2
% 3.23/1.01  --inst_start_prop_sim_after_learn       3
% 3.23/1.01  --inst_sel_renew                        solver
% 3.23/1.01  --inst_lit_activity_flag                true
% 3.23/1.01  --inst_restr_to_given                   false
% 3.23/1.01  --inst_activity_threshold               500
% 3.23/1.01  --inst_out_proof                        true
% 3.23/1.01  
% 3.23/1.01  ------ Resolution Options
% 3.23/1.01  
% 3.23/1.01  --resolution_flag                       false
% 3.23/1.01  --res_lit_sel                           adaptive
% 3.23/1.01  --res_lit_sel_side                      none
% 3.23/1.01  --res_ordering                          kbo
% 3.23/1.01  --res_to_prop_solver                    active
% 3.23/1.01  --res_prop_simpl_new                    false
% 3.23/1.01  --res_prop_simpl_given                  true
% 3.23/1.01  --res_passive_queue_type                priority_queues
% 3.23/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/1.01  --res_passive_queues_freq               [15;5]
% 3.23/1.01  --res_forward_subs                      full
% 3.23/1.01  --res_backward_subs                     full
% 3.23/1.01  --res_forward_subs_resolution           true
% 3.23/1.01  --res_backward_subs_resolution          true
% 3.23/1.01  --res_orphan_elimination                true
% 3.23/1.01  --res_time_limit                        2.
% 3.23/1.01  --res_out_proof                         true
% 3.23/1.01  
% 3.23/1.01  ------ Superposition Options
% 3.23/1.01  
% 3.23/1.01  --superposition_flag                    true
% 3.23/1.01  --sup_passive_queue_type                priority_queues
% 3.23/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.23/1.01  --demod_completeness_check              fast
% 3.23/1.01  --demod_use_ground                      true
% 3.23/1.01  --sup_to_prop_solver                    passive
% 3.23/1.01  --sup_prop_simpl_new                    true
% 3.23/1.01  --sup_prop_simpl_given                  true
% 3.23/1.01  --sup_fun_splitting                     false
% 3.23/1.01  --sup_smt_interval                      50000
% 3.23/1.01  
% 3.23/1.01  ------ Superposition Simplification Setup
% 3.23/1.01  
% 3.23/1.01  --sup_indices_passive                   []
% 3.23/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.01  --sup_full_bw                           [BwDemod]
% 3.23/1.01  --sup_immed_triv                        [TrivRules]
% 3.23/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.01  --sup_immed_bw_main                     []
% 3.23/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/1.01  
% 3.23/1.01  ------ Combination Options
% 3.23/1.01  
% 3.23/1.01  --comb_res_mult                         3
% 3.23/1.01  --comb_sup_mult                         2
% 3.23/1.01  --comb_inst_mult                        10
% 3.23/1.01  
% 3.23/1.01  ------ Debug Options
% 3.23/1.01  
% 3.23/1.01  --dbg_backtrace                         false
% 3.23/1.01  --dbg_dump_prop_clauses                 false
% 3.23/1.01  --dbg_dump_prop_clauses_file            -
% 3.23/1.01  --dbg_out_stat                          false
% 3.23/1.01  
% 3.23/1.01  
% 3.23/1.01  
% 3.23/1.01  
% 3.23/1.01  ------ Proving...
% 3.23/1.01  
% 3.23/1.01  
% 3.23/1.01  % SZS status Theorem for theBenchmark.p
% 3.23/1.01  
% 3.23/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.23/1.01  
% 3.23/1.01  fof(f2,axiom,(
% 3.23/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.23/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f13,plain,(
% 3.23/1.01    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.23/1.01    inference(rectify,[],[f2])).
% 3.23/1.01  
% 3.23/1.01  fof(f14,plain,(
% 3.23/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.23/1.01    inference(ennf_transformation,[],[f13])).
% 3.23/1.01  
% 3.23/1.01  fof(f16,plain,(
% 3.23/1.01    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.23/1.01    introduced(choice_axiom,[])).
% 3.23/1.01  
% 3.23/1.01  fof(f17,plain,(
% 3.23/1.01    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.23/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f16])).
% 3.23/1.01  
% 3.23/1.01  fof(f29,plain,(
% 3.23/1.01    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.23/1.01    inference(cnf_transformation,[],[f17])).
% 3.23/1.01  
% 3.23/1.01  fof(f3,axiom,(
% 3.23/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.23/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f18,plain,(
% 3.23/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.23/1.01    inference(nnf_transformation,[],[f3])).
% 3.23/1.01  
% 3.23/1.01  fof(f19,plain,(
% 3.23/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.23/1.01    inference(flattening,[],[f18])).
% 3.23/1.01  
% 3.23/1.01  fof(f31,plain,(
% 3.23/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.23/1.01    inference(cnf_transformation,[],[f19])).
% 3.23/1.01  
% 3.23/1.01  fof(f59,plain,(
% 3.23/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.23/1.01    inference(equality_resolution,[],[f31])).
% 3.23/1.01  
% 3.23/1.01  fof(f4,axiom,(
% 3.23/1.01    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.23/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f20,plain,(
% 3.23/1.01    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.23/1.01    inference(nnf_transformation,[],[f4])).
% 3.23/1.01  
% 3.23/1.01  fof(f35,plain,(
% 3.23/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.23/1.01    inference(cnf_transformation,[],[f20])).
% 3.23/1.01  
% 3.23/1.01  fof(f5,axiom,(
% 3.23/1.01    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.23/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f36,plain,(
% 3.23/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.23/1.01    inference(cnf_transformation,[],[f5])).
% 3.23/1.01  
% 3.23/1.01  fof(f49,plain,(
% 3.23/1.01    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 3.23/1.01    inference(definition_unfolding,[],[f35,f36])).
% 3.23/1.01  
% 3.23/1.01  fof(f10,axiom,(
% 3.23/1.01    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.23/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f22,plain,(
% 3.23/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.23/1.01    inference(nnf_transformation,[],[f10])).
% 3.23/1.01  
% 3.23/1.01  fof(f23,plain,(
% 3.23/1.01    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.23/1.01    inference(flattening,[],[f22])).
% 3.23/1.01  
% 3.23/1.01  fof(f44,plain,(
% 3.23/1.01    ( ! [X2,X0,X1] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 3.23/1.01    inference(cnf_transformation,[],[f23])).
% 3.23/1.01  
% 3.23/1.01  fof(f7,axiom,(
% 3.23/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.23/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f39,plain,(
% 3.23/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.23/1.01    inference(cnf_transformation,[],[f7])).
% 3.23/1.01  
% 3.23/1.01  fof(f8,axiom,(
% 3.23/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.23/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f40,plain,(
% 3.23/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.23/1.01    inference(cnf_transformation,[],[f8])).
% 3.23/1.01  
% 3.23/1.01  fof(f9,axiom,(
% 3.23/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.23/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f41,plain,(
% 3.23/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.23/1.01    inference(cnf_transformation,[],[f9])).
% 3.23/1.01  
% 3.23/1.01  fof(f47,plain,(
% 3.23/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.23/1.01    inference(definition_unfolding,[],[f40,f41])).
% 3.23/1.01  
% 3.23/1.01  fof(f48,plain,(
% 3.23/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.23/1.01    inference(definition_unfolding,[],[f39,f47])).
% 3.23/1.01  
% 3.23/1.01  fof(f53,plain,(
% 3.23/1.01    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2)))) | X0 = X2 | ~r2_hidden(X0,X1)) )),
% 3.23/1.01    inference(definition_unfolding,[],[f44,f36,f48])).
% 3.23/1.01  
% 3.23/1.01  fof(f43,plain,(
% 3.23/1.01    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 3.23/1.01    inference(cnf_transformation,[],[f23])).
% 3.23/1.01  
% 3.23/1.01  fof(f54,plain,(
% 3.23/1.01    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))) )),
% 3.23/1.01    inference(definition_unfolding,[],[f43,f36,f48])).
% 3.23/1.01  
% 3.23/1.01  fof(f60,plain,(
% 3.23/1.01    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))) )),
% 3.23/1.01    inference(equality_resolution,[],[f54])).
% 3.23/1.01  
% 3.23/1.01  fof(f6,axiom,(
% 3.23/1.01    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.23/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f21,plain,(
% 3.23/1.01    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.23/1.01    inference(nnf_transformation,[],[f6])).
% 3.23/1.01  
% 3.23/1.01  fof(f37,plain,(
% 3.23/1.01    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.23/1.01    inference(cnf_transformation,[],[f21])).
% 3.23/1.01  
% 3.23/1.01  fof(f52,plain,(
% 3.23/1.01    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.23/1.01    inference(definition_unfolding,[],[f37,f36])).
% 3.23/1.01  
% 3.23/1.01  fof(f11,conjecture,(
% 3.23/1.01    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.23/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.23/1.01  
% 3.23/1.01  fof(f12,negated_conjecture,(
% 3.23/1.01    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.23/1.01    inference(negated_conjecture,[],[f11])).
% 3.23/1.01  
% 3.23/1.01  fof(f15,plain,(
% 3.23/1.01    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 3.23/1.01    inference(ennf_transformation,[],[f12])).
% 3.23/1.01  
% 3.23/1.01  fof(f24,plain,(
% 3.23/1.01    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 3.23/1.01    inference(nnf_transformation,[],[f15])).
% 3.23/1.01  
% 3.23/1.01  fof(f25,plain,(
% 3.23/1.01    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK2,sK1) | k4_xboole_0(sK1,k1_tarski(sK2)) != sK1) & (~r2_hidden(sK2,sK1) | k4_xboole_0(sK1,k1_tarski(sK2)) = sK1))),
% 3.23/1.01    introduced(choice_axiom,[])).
% 3.23/1.01  
% 3.23/1.01  fof(f26,plain,(
% 3.23/1.01    (r2_hidden(sK2,sK1) | k4_xboole_0(sK1,k1_tarski(sK2)) != sK1) & (~r2_hidden(sK2,sK1) | k4_xboole_0(sK1,k1_tarski(sK2)) = sK1)),
% 3.23/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f24,f25])).
% 3.23/1.01  
% 3.23/1.01  fof(f46,plain,(
% 3.23/1.01    r2_hidden(sK2,sK1) | k4_xboole_0(sK1,k1_tarski(sK2)) != sK1),
% 3.23/1.01    inference(cnf_transformation,[],[f26])).
% 3.23/1.01  
% 3.23/1.01  fof(f56,plain,(
% 3.23/1.01    r2_hidden(sK2,sK1) | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != sK1),
% 3.23/1.01    inference(definition_unfolding,[],[f46,f36,f48])).
% 3.23/1.01  
% 3.23/1.01  fof(f33,plain,(
% 3.23/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.23/1.01    inference(cnf_transformation,[],[f19])).
% 3.23/1.01  
% 3.23/1.01  fof(f28,plain,(
% 3.23/1.01    ( ! [X0,X1] : (r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.23/1.01    inference(cnf_transformation,[],[f17])).
% 3.23/1.01  
% 3.23/1.01  fof(f45,plain,(
% 3.23/1.01    ~r2_hidden(sK2,sK1) | k4_xboole_0(sK1,k1_tarski(sK2)) = sK1),
% 3.23/1.01    inference(cnf_transformation,[],[f26])).
% 3.23/1.01  
% 3.23/1.01  fof(f57,plain,(
% 3.23/1.01    ~r2_hidden(sK2,sK1) | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = sK1),
% 3.23/1.01    inference(definition_unfolding,[],[f45,f36,f48])).
% 3.23/1.01  
% 3.23/1.01  cnf(c_2,plain,
% 3.23/1.01      ( r2_hidden(sK0(X0,X1),X1) | r1_xboole_0(X0,X1) ),
% 3.23/1.01      inference(cnf_transformation,[],[f29]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_871,plain,
% 3.23/1.01      ( r2_hidden(sK0(X0,X1),X1) = iProver_top
% 3.23/1.01      | r1_xboole_0(X0,X1) = iProver_top ),
% 3.23/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_6,plain,
% 3.23/1.01      ( r1_tarski(X0,X0) ),
% 3.23/1.01      inference(cnf_transformation,[],[f59]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_868,plain,
% 3.23/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.23/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_7,plain,
% 3.23/1.01      ( ~ r1_tarski(X0,X1)
% 3.23/1.01      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 3.23/1.01      inference(cnf_transformation,[],[f49]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_867,plain,
% 3.23/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 3.23/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 3.23/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_1208,plain,
% 3.23/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X0)) = k1_xboole_0 ),
% 3.23/1.01      inference(superposition,[status(thm)],[c_868,c_867]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_11,plain,
% 3.23/1.01      ( ~ r2_hidden(X0,X1)
% 3.23/1.01      | r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X2,X2,X2,X2))))
% 3.23/1.01      | X2 = X0 ),
% 3.23/1.01      inference(cnf_transformation,[],[f53]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_863,plain,
% 3.23/1.01      ( X0 = X1
% 3.23/1.01      | r2_hidden(X1,X2) != iProver_top
% 3.23/1.01      | r2_hidden(X1,k5_xboole_0(X2,k3_xboole_0(X2,k2_enumset1(X0,X0,X0,X0)))) = iProver_top ),
% 3.23/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_1593,plain,
% 3.23/1.01      ( X0 = X1
% 3.23/1.01      | r2_hidden(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top
% 3.23/1.01      | r2_hidden(X1,k1_xboole_0) = iProver_top ),
% 3.23/1.01      inference(superposition,[status(thm)],[c_1208,c_863]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_12,plain,
% 3.23/1.01      ( ~ r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) ),
% 3.23/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_862,plain,
% 3.23/1.01      ( r2_hidden(X0,k5_xboole_0(X1,k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)))) != iProver_top ),
% 3.23/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_1279,plain,
% 3.23/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.23/1.01      inference(superposition,[status(thm)],[c_1208,c_862]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_2284,plain,
% 3.23/1.01      ( X0 = X1 | r2_hidden(X0,k2_enumset1(X1,X1,X1,X1)) != iProver_top ),
% 3.23/1.01      inference(forward_subsumption_resolution,
% 3.23/1.01                [status(thm)],
% 3.23/1.01                [c_1593,c_1279]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_2286,plain,
% 3.23/1.01      ( sK0(X0,k2_enumset1(X1,X1,X1,X1)) = X1
% 3.23/1.01      | r1_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = iProver_top ),
% 3.23/1.01      inference(superposition,[status(thm)],[c_871,c_2284]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_10,plain,
% 3.23/1.01      ( ~ r1_xboole_0(X0,X1) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
% 3.23/1.01      inference(cnf_transformation,[],[f52]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_864,plain,
% 3.23/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
% 3.23/1.01      | r1_xboole_0(X0,X1) != iProver_top ),
% 3.23/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_2319,plain,
% 3.23/1.01      ( k5_xboole_0(X0,k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) = X0
% 3.23/1.01      | sK0(X0,k2_enumset1(X1,X1,X1,X1)) = X1 ),
% 3.23/1.01      inference(superposition,[status(thm)],[c_2286,c_864]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_3367,plain,
% 3.23/1.01      ( sK0(X0,k2_enumset1(X1,X1,X1,X1)) = X1
% 3.23/1.01      | r2_hidden(X1,X0) != iProver_top ),
% 3.23/1.01      inference(superposition,[status(thm)],[c_2319,c_862]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_14,negated_conjecture,
% 3.23/1.01      ( r2_hidden(sK2,sK1)
% 3.23/1.01      | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != sK1 ),
% 3.23/1.01      inference(cnf_transformation,[],[f56]) ).
% 3.23/1.01  
% 3.23/1.01  cnf(c_860,plain,
% 3.23/1.01      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != sK1
% 3.23/1.02      | r2_hidden(sK2,sK1) = iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_3368,plain,
% 3.23/1.02      ( sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = sK2
% 3.23/1.02      | r2_hidden(sK2,sK1) = iProver_top ),
% 3.23/1.02      inference(superposition,[status(thm)],[c_2319,c_860]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_3422,plain,
% 3.23/1.02      ( sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) = sK2 ),
% 3.23/1.02      inference(backward_subsumption_resolution,
% 3.23/1.02                [status(thm)],
% 3.23/1.02                [c_3367,c_3368]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_511,plain,
% 3.23/1.02      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.23/1.02      theory(equality) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_1186,plain,
% 3.23/1.02      ( r2_hidden(X0,X1)
% 3.23/1.02      | ~ r2_hidden(sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK1)
% 3.23/1.02      | X0 != sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
% 3.23/1.02      | X1 != sK1 ),
% 3.23/1.02      inference(instantiation,[status(thm)],[c_511]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_2365,plain,
% 3.23/1.02      ( r2_hidden(X0,sK1)
% 3.23/1.02      | ~ r2_hidden(sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK1)
% 3.23/1.02      | X0 != sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
% 3.23/1.02      | sK1 != sK1 ),
% 3.23/1.02      inference(instantiation,[status(thm)],[c_1186]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_2367,plain,
% 3.23/1.02      ( ~ r2_hidden(sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK1)
% 3.23/1.02      | r2_hidden(sK2,sK1)
% 3.23/1.02      | sK1 != sK1
% 3.23/1.02      | sK2 != sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.23/1.02      inference(instantiation,[status(thm)],[c_2365]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_509,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_2252,plain,
% 3.23/1.02      ( X0 != X1
% 3.23/1.02      | X0 = sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
% 3.23/1.02      | sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != X1 ),
% 3.23/1.02      inference(instantiation,[status(thm)],[c_509]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_2253,plain,
% 3.23/1.02      ( sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) != sK2
% 3.23/1.02      | sK2 = sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
% 3.23/1.02      | sK2 != sK2 ),
% 3.23/1.02      inference(instantiation,[status(thm)],[c_2252]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_1491,plain,
% 3.23/1.02      ( ~ r2_hidden(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(X0,X0,X0,X0)))) ),
% 3.23/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_1496,plain,
% 3.23/1.02      ( r2_hidden(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(X0,X0,X0,X0)))) != iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_1491]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_1498,plain,
% 3.23/1.02      ( r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) != iProver_top ),
% 3.23/1.02      inference(instantiation,[status(thm)],[c_1496]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_1048,plain,
% 3.23/1.02      ( r2_hidden(X0,X1) | ~ r2_hidden(sK2,sK1) | X1 != sK1 | X0 != sK2 ),
% 3.23/1.02      inference(instantiation,[status(thm)],[c_511]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_1090,plain,
% 3.23/1.02      ( r2_hidden(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,X1)))
% 3.23/1.02      | ~ r2_hidden(sK2,sK1)
% 3.23/1.02      | X0 != sK2
% 3.23/1.02      | k5_xboole_0(sK1,k3_xboole_0(sK1,X1)) != sK1 ),
% 3.23/1.02      inference(instantiation,[status(thm)],[c_1048]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_1490,plain,
% 3.23/1.02      ( r2_hidden(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(X0,X0,X0,X0))))
% 3.23/1.02      | ~ r2_hidden(sK2,sK1)
% 3.23/1.02      | X0 != sK2
% 3.23/1.02      | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(X0,X0,X0,X0))) != sK1 ),
% 3.23/1.02      inference(instantiation,[status(thm)],[c_1090]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_1492,plain,
% 3.23/1.02      ( X0 != sK2
% 3.23/1.02      | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(X0,X0,X0,X0))) != sK1
% 3.23/1.02      | r2_hidden(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(X0,X0,X0,X0)))) = iProver_top
% 3.23/1.02      | r2_hidden(sK2,sK1) != iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_1490]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_1494,plain,
% 3.23/1.02      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != sK1
% 3.23/1.02      | sK2 != sK2
% 3.23/1.02      | r2_hidden(sK2,k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)))) = iProver_top
% 3.23/1.02      | r2_hidden(sK2,sK1) != iProver_top ),
% 3.23/1.02      inference(instantiation,[status(thm)],[c_1492]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_1014,plain,
% 3.23/1.02      ( r1_tarski(sK1,sK1) ),
% 3.23/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_4,plain,
% 3.23/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.23/1.02      inference(cnf_transformation,[],[f33]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_996,plain,
% 3.23/1.02      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | sK1 = X0 ),
% 3.23/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_1013,plain,
% 3.23/1.02      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 3.23/1.02      inference(instantiation,[status(thm)],[c_996]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_3,plain,
% 3.23/1.02      ( r2_hidden(sK0(X0,X1),X0) | r1_xboole_0(X0,X1) ),
% 3.23/1.02      inference(cnf_transformation,[],[f28]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_988,plain,
% 3.23/1.02      ( r2_hidden(sK0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)),sK1)
% 3.23/1.02      | r1_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2)) ),
% 3.23/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_971,plain,
% 3.23/1.02      ( ~ r1_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))
% 3.23/1.02      | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = sK1 ),
% 3.23/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_44,plain,
% 3.23/1.02      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 3.23/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_40,plain,
% 3.23/1.02      ( r1_tarski(sK2,sK2) ),
% 3.23/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_17,plain,
% 3.23/1.02      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) != sK1
% 3.23/1.02      | r2_hidden(sK2,sK1) = iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_15,negated_conjecture,
% 3.23/1.02      ( ~ r2_hidden(sK2,sK1)
% 3.23/1.02      | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = sK1 ),
% 3.23/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(c_16,plain,
% 3.23/1.02      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_enumset1(sK2,sK2,sK2,sK2))) = sK1
% 3.23/1.02      | r2_hidden(sK2,sK1) != iProver_top ),
% 3.23/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.23/1.02  
% 3.23/1.02  cnf(contradiction,plain,
% 3.23/1.02      ( $false ),
% 3.23/1.02      inference(minisat,
% 3.23/1.02                [status(thm)],
% 3.23/1.02                [c_3422,c_2367,c_2253,c_1498,c_1494,c_1014,c_1013,c_988,
% 3.23/1.02                 c_971,c_44,c_40,c_17,c_16,c_15]) ).
% 3.23/1.02  
% 3.23/1.02  
% 3.23/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.23/1.02  
% 3.23/1.02  ------                               Statistics
% 3.23/1.02  
% 3.23/1.02  ------ General
% 3.23/1.02  
% 3.23/1.02  abstr_ref_over_cycles:                  0
% 3.23/1.02  abstr_ref_under_cycles:                 0
% 3.23/1.02  gc_basic_clause_elim:                   0
% 3.23/1.02  forced_gc_time:                         0
% 3.23/1.02  parsing_time:                           0.009
% 3.23/1.02  unif_index_cands_time:                  0.
% 3.23/1.02  unif_index_add_time:                    0.
% 3.23/1.02  orderings_time:                         0.
% 3.23/1.02  out_proof_time:                         0.009
% 3.23/1.02  total_time:                             0.158
% 3.23/1.02  num_of_symbols:                         41
% 3.23/1.02  num_of_terms:                           3365
% 3.23/1.02  
% 3.23/1.02  ------ Preprocessing
% 3.23/1.02  
% 3.23/1.02  num_of_splits:                          0
% 3.23/1.02  num_of_split_atoms:                     0
% 3.23/1.02  num_of_reused_defs:                     0
% 3.23/1.02  num_eq_ax_congr_red:                    18
% 3.23/1.02  num_of_sem_filtered_clauses:            1
% 3.23/1.02  num_of_subtypes:                        0
% 3.23/1.02  monotx_restored_types:                  0
% 3.23/1.02  sat_num_of_epr_types:                   0
% 3.23/1.02  sat_num_of_non_cyclic_types:            0
% 3.23/1.02  sat_guarded_non_collapsed_types:        0
% 3.23/1.02  num_pure_diseq_elim:                    0
% 3.23/1.02  simp_replaced_by:                       0
% 3.23/1.02  res_preprocessed:                       73
% 3.23/1.02  prep_upred:                             0
% 3.23/1.02  prep_unflattend:                        12
% 3.23/1.02  smt_new_axioms:                         0
% 3.23/1.02  pred_elim_cands:                        3
% 3.23/1.02  pred_elim:                              0
% 3.23/1.02  pred_elim_cl:                           0
% 3.23/1.02  pred_elim_cycles:                       2
% 3.23/1.02  merged_defs:                            24
% 3.23/1.02  merged_defs_ncl:                        0
% 3.23/1.02  bin_hyper_res:                          24
% 3.23/1.02  prep_cycles:                            4
% 3.23/1.02  pred_elim_time:                         0.002
% 3.23/1.02  splitting_time:                         0.
% 3.23/1.02  sem_filter_time:                        0.
% 3.23/1.02  monotx_time:                            0.
% 3.23/1.02  subtype_inf_time:                       0.
% 3.23/1.02  
% 3.23/1.02  ------ Problem properties
% 3.23/1.02  
% 3.23/1.02  clauses:                                15
% 3.23/1.02  conjectures:                            2
% 3.23/1.02  epr:                                    3
% 3.23/1.02  horn:                                   12
% 3.23/1.02  ground:                                 2
% 3.23/1.02  unary:                                  3
% 3.23/1.02  binary:                                 9
% 3.23/1.02  lits:                                   30
% 3.23/1.02  lits_eq:                                9
% 3.23/1.02  fd_pure:                                0
% 3.23/1.02  fd_pseudo:                              0
% 3.23/1.02  fd_cond:                                0
% 3.23/1.02  fd_pseudo_cond:                         2
% 3.23/1.02  ac_symbols:                             0
% 3.23/1.02  
% 3.23/1.02  ------ Propositional Solver
% 3.23/1.02  
% 3.23/1.02  prop_solver_calls:                      30
% 3.23/1.02  prop_fast_solver_calls:                 441
% 3.23/1.02  smt_solver_calls:                       0
% 3.23/1.02  smt_fast_solver_calls:                  0
% 3.23/1.02  prop_num_of_clauses:                    1252
% 3.23/1.02  prop_preprocess_simplified:             3236
% 3.23/1.02  prop_fo_subsumed:                       0
% 3.23/1.02  prop_solver_time:                       0.
% 3.23/1.02  smt_solver_time:                        0.
% 3.23/1.02  smt_fast_solver_time:                   0.
% 3.23/1.02  prop_fast_solver_time:                  0.
% 3.23/1.02  prop_unsat_core_time:                   0.
% 3.23/1.02  
% 3.23/1.02  ------ QBF
% 3.23/1.02  
% 3.23/1.02  qbf_q_res:                              0
% 3.23/1.02  qbf_num_tautologies:                    0
% 3.23/1.02  qbf_prep_cycles:                        0
% 3.23/1.02  
% 3.23/1.02  ------ BMC1
% 3.23/1.02  
% 3.23/1.02  bmc1_current_bound:                     -1
% 3.23/1.02  bmc1_last_solved_bound:                 -1
% 3.23/1.02  bmc1_unsat_core_size:                   -1
% 3.23/1.02  bmc1_unsat_core_parents_size:           -1
% 3.23/1.02  bmc1_merge_next_fun:                    0
% 3.23/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.23/1.02  
% 3.23/1.02  ------ Instantiation
% 3.23/1.02  
% 3.23/1.02  inst_num_of_clauses:                    352
% 3.23/1.02  inst_num_in_passive:                    166
% 3.23/1.02  inst_num_in_active:                     185
% 3.23/1.02  inst_num_in_unprocessed:                0
% 3.23/1.02  inst_num_of_loops:                      256
% 3.23/1.02  inst_num_of_learning_restarts:          0
% 3.23/1.02  inst_num_moves_active_passive:          64
% 3.23/1.02  inst_lit_activity:                      0
% 3.23/1.02  inst_lit_activity_moves:                0
% 3.23/1.02  inst_num_tautologies:                   0
% 3.23/1.02  inst_num_prop_implied:                  0
% 3.23/1.02  inst_num_existing_simplified:           0
% 3.23/1.02  inst_num_eq_res_simplified:             0
% 3.23/1.02  inst_num_child_elim:                    0
% 3.23/1.02  inst_num_of_dismatching_blockings:      114
% 3.23/1.02  inst_num_of_non_proper_insts:           325
% 3.23/1.02  inst_num_of_duplicates:                 0
% 3.23/1.02  inst_inst_num_from_inst_to_res:         0
% 3.23/1.02  inst_dismatching_checking_time:         0.
% 3.23/1.02  
% 3.23/1.02  ------ Resolution
% 3.23/1.02  
% 3.23/1.02  res_num_of_clauses:                     0
% 3.23/1.02  res_num_in_passive:                     0
% 3.23/1.02  res_num_in_active:                      0
% 3.23/1.02  res_num_of_loops:                       77
% 3.23/1.02  res_forward_subset_subsumed:            14
% 3.23/1.02  res_backward_subset_subsumed:           0
% 3.23/1.02  res_forward_subsumed:                   0
% 3.23/1.02  res_backward_subsumed:                  0
% 3.23/1.02  res_forward_subsumption_resolution:     0
% 3.23/1.02  res_backward_subsumption_resolution:    0
% 3.23/1.02  res_clause_to_clause_subsumption:       489
% 3.23/1.02  res_orphan_elimination:                 0
% 3.23/1.02  res_tautology_del:                      74
% 3.23/1.02  res_num_eq_res_simplified:              0
% 3.23/1.02  res_num_sel_changes:                    0
% 3.23/1.02  res_moves_from_active_to_pass:          0
% 3.23/1.02  
% 3.23/1.02  ------ Superposition
% 3.23/1.02  
% 3.23/1.02  sup_time_total:                         0.
% 3.23/1.02  sup_time_generating:                    0.
% 3.23/1.02  sup_time_sim_full:                      0.
% 3.23/1.02  sup_time_sim_immed:                     0.
% 3.23/1.02  
% 3.23/1.02  sup_num_of_clauses:                     102
% 3.23/1.02  sup_num_in_active:                      50
% 3.23/1.02  sup_num_in_passive:                     52
% 3.23/1.02  sup_num_of_loops:                       50
% 3.23/1.02  sup_fw_superposition:                   124
% 3.23/1.02  sup_bw_superposition:                   93
% 3.23/1.02  sup_immediate_simplified:               25
% 3.23/1.02  sup_given_eliminated:                   0
% 3.23/1.02  comparisons_done:                       0
% 3.23/1.02  comparisons_avoided:                    3
% 3.23/1.02  
% 3.23/1.02  ------ Simplifications
% 3.23/1.02  
% 3.23/1.02  
% 3.23/1.02  sim_fw_subset_subsumed:                 6
% 3.23/1.02  sim_bw_subset_subsumed:                 0
% 3.23/1.02  sim_fw_subsumed:                        13
% 3.23/1.02  sim_bw_subsumed:                        1
% 3.23/1.02  sim_fw_subsumption_res:                 2
% 3.23/1.02  sim_bw_subsumption_res:                 1
% 3.23/1.02  sim_tautology_del:                      17
% 3.23/1.02  sim_eq_tautology_del:                   7
% 3.23/1.02  sim_eq_res_simp:                        0
% 3.23/1.02  sim_fw_demodulated:                     9
% 3.23/1.02  sim_bw_demodulated:                     0
% 3.23/1.02  sim_light_normalised:                   0
% 3.23/1.02  sim_joinable_taut:                      0
% 3.23/1.02  sim_joinable_simp:                      0
% 3.23/1.02  sim_ac_normalised:                      0
% 3.23/1.02  sim_smt_subsumption:                    0
% 3.23/1.02  
%------------------------------------------------------------------------------
