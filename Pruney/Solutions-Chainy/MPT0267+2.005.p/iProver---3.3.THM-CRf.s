%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:35:30 EST 2020

% Result     : Theorem 19.92s
% Output     : CNFRefutation 19.92s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 479 expanded)
%              Number of clauses        :   50 (  94 expanded)
%              Number of leaves         :   21 ( 132 expanded)
%              Depth                    :   13
%              Number of atoms          :  309 (1185 expanded)
%              Number of equality atoms :  156 ( 551 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f31,f40,f40])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f21])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
      <=> ( X0 != X2
          & r2_hidden(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <~> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( X0 = X2
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( ( X0 = X2
          | ~ r2_hidden(X0,X1)
          | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) )
        & ( ( X0 != X2
            & r2_hidden(X0,X1) )
          | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) )
   => ( ( sK2 = sK4
        | ~ r2_hidden(sK2,sK3)
        | ~ r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) )
      & ( ( sK2 != sK4
          & r2_hidden(sK2,sK3) )
        | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( sK2 = sK4
      | ~ r2_hidden(sK2,sK3)
      | ~ r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) )
    & ( ( sK2 != sK4
        & r2_hidden(sK2,sK3) )
      | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f29])).

fof(f54,plain,
    ( sK2 = sK4
    | ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f49,f55])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f56])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f57])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f58])).

fof(f66,plain,
    ( sK2 = sK4
    | ~ r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f52,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,
    ( r2_hidden(sK2,sK3)
    | r2_hidden(sK2,k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(definition_unfolding,[],[f52,f59])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f71,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f53,plain,
    ( sK2 != sK4
    | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,
    ( sK2 != sK4
    | r2_hidden(sK2,k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))) ),
    inference(definition_unfolding,[],[f53,f59])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f43,f59])).

fof(f69,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k5_enumset1(X3,X3,X3,X3,X3,X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f64])).

fof(f70,plain,(
    ! [X3] : r2_hidden(X3,k5_enumset1(X3,X3,X3,X3,X3,X3,X3)) ),
    inference(equality_resolution,[],[f69])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_397,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2508,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_397])).

cnf(c_1,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_395,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2312,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_395])).

cnf(c_9,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_391,plain,
    ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_594,plain,
    ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_391])).

cnf(c_6,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ r2_hidden(X2,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_394,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2266,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_594,c_394])).

cnf(c_586,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_1,c_0])).

cnf(c_2314,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_586,c_395])).

cnf(c_4288,plain,
    ( r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2312,c_2266,c_2314])).

cnf(c_4289,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4288])).

cnf(c_4300,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_4289])).

cnf(c_5250,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2508,c_4300])).

cnf(c_14,negated_conjecture,
    ( ~ r2_hidden(sK2,k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
    | ~ r2_hidden(sK2,sK3)
    | sK2 = sK4 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_386,plain,
    ( sK2 = sK4
    | r2_hidden(sK2,k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_80182,plain,
    ( sK4 = sK2
    | r2_hidden(sK2,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
    | r2_hidden(sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5250,c_386])).

cnf(c_145,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_827,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK2,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_145])).

cnf(c_6753,plain,
    ( ~ r2_hidden(X0,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(sK2,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_827])).

cnf(c_6756,plain,
    ( ~ r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(sK2,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK2 != sK4 ),
    inference(instantiation,[status(thm)],[c_6753])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK2,k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
    | r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_384,plain,
    ( r2_hidden(sK2,k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
    | r2_hidden(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4299,plain,
    ( r2_hidden(sK2,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_384,c_4289])).

cnf(c_781,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)
    | ~ r2_hidden(sK2,X0)
    | r2_hidden(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_6,c_16])).

cnf(c_1247,plain,
    ( ~ r2_hidden(sK2,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | r2_hidden(sK2,sK3) ),
    inference(resolution,[status(thm)],[c_781,c_9])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_626,plain,
    ( ~ r2_hidden(sK2,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK2,k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
    | sK2 != sK4 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_782,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)
    | ~ r2_hidden(sK2,X0)
    | sK2 != sK4 ),
    inference(resolution,[status(thm)],[c_6,c_15])).

cnf(c_1441,plain,
    ( ~ r2_hidden(sK2,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | sK2 != sK4 ),
    inference(resolution,[status(thm)],[c_782,c_9])).

cnf(c_1444,plain,
    ( ~ r2_hidden(sK2,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1247,c_626,c_1441])).

cnf(c_1446,plain,
    ( r2_hidden(sK2,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1444])).

cnf(c_141,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_851,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_141])).

cnf(c_142,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_629,plain,
    ( sK4 != X0
    | sK2 != X0
    | sK2 = sK4 ),
    inference(instantiation,[status(thm)],[c_142])).

cnf(c_850,plain,
    ( sK4 != sK2
    | sK2 = sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_147,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | X6 != X7
    | X8 != X9
    | X10 != X11
    | X12 != X13
    | k5_enumset1(X0,X2,X4,X6,X8,X10,X12) = k5_enumset1(X1,X3,X5,X7,X9,X11,X13) ),
    theory(equality)).

cnf(c_152,plain,
    ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_147])).

cnf(c_12,plain,
    ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_24,plain,
    ( r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_21,plain,
    ( ~ r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_80182,c_6756,c_4299,c_1446,c_1444,c_851,c_850,c_152,c_24,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.92/3.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 19.92/3.00  
% 19.92/3.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.92/3.00  
% 19.92/3.00  ------  iProver source info
% 19.92/3.00  
% 19.92/3.00  git: date: 2020-06-30 10:37:57 +0100
% 19.92/3.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.92/3.00  git: non_committed_changes: false
% 19.92/3.00  git: last_make_outside_of_git: false
% 19.92/3.00  
% 19.92/3.00  ------ 
% 19.92/3.00  
% 19.92/3.00  ------ Input Options
% 19.92/3.00  
% 19.92/3.00  --out_options                           all
% 19.92/3.00  --tptp_safe_out                         true
% 19.92/3.00  --problem_path                          ""
% 19.92/3.00  --include_path                          ""
% 19.92/3.00  --clausifier                            res/vclausify_rel
% 19.92/3.00  --clausifier_options                    --mode clausify
% 19.92/3.00  --stdin                                 false
% 19.92/3.00  --stats_out                             sel
% 19.92/3.00  
% 19.92/3.00  ------ General Options
% 19.92/3.00  
% 19.92/3.00  --fof                                   false
% 19.92/3.00  --time_out_real                         604.99
% 19.92/3.00  --time_out_virtual                      -1.
% 19.92/3.00  --symbol_type_check                     false
% 19.92/3.00  --clausify_out                          false
% 19.92/3.00  --sig_cnt_out                           false
% 19.92/3.00  --trig_cnt_out                          false
% 19.92/3.00  --trig_cnt_out_tolerance                1.
% 19.92/3.00  --trig_cnt_out_sk_spl                   false
% 19.92/3.00  --abstr_cl_out                          false
% 19.92/3.00  
% 19.92/3.00  ------ Global Options
% 19.92/3.00  
% 19.92/3.00  --schedule                              none
% 19.92/3.00  --add_important_lit                     false
% 19.92/3.00  --prop_solver_per_cl                    1000
% 19.92/3.00  --min_unsat_core                        false
% 19.92/3.00  --soft_assumptions                      false
% 19.92/3.00  --soft_lemma_size                       3
% 19.92/3.00  --prop_impl_unit_size                   0
% 19.92/3.00  --prop_impl_unit                        []
% 19.92/3.00  --share_sel_clauses                     true
% 19.92/3.00  --reset_solvers                         false
% 19.92/3.00  --bc_imp_inh                            [conj_cone]
% 19.92/3.00  --conj_cone_tolerance                   3.
% 19.92/3.00  --extra_neg_conj                        none
% 19.92/3.00  --large_theory_mode                     true
% 19.92/3.00  --prolific_symb_bound                   200
% 19.92/3.00  --lt_threshold                          2000
% 19.92/3.00  --clause_weak_htbl                      true
% 19.92/3.00  --gc_record_bc_elim                     false
% 19.92/3.00  
% 19.92/3.00  ------ Preprocessing Options
% 19.92/3.00  
% 19.92/3.00  --preprocessing_flag                    true
% 19.92/3.00  --time_out_prep_mult                    0.1
% 19.92/3.00  --splitting_mode                        input
% 19.92/3.00  --splitting_grd                         true
% 19.92/3.00  --splitting_cvd                         false
% 19.92/3.00  --splitting_cvd_svl                     false
% 19.92/3.00  --splitting_nvd                         32
% 19.92/3.00  --sub_typing                            true
% 19.92/3.00  --prep_gs_sim                           false
% 19.92/3.00  --prep_unflatten                        true
% 19.92/3.00  --prep_res_sim                          true
% 19.92/3.00  --prep_upred                            true
% 19.92/3.00  --prep_sem_filter                       exhaustive
% 19.92/3.00  --prep_sem_filter_out                   false
% 19.92/3.00  --pred_elim                             false
% 19.92/3.00  --res_sim_input                         true
% 19.92/3.00  --eq_ax_congr_red                       true
% 19.92/3.00  --pure_diseq_elim                       true
% 19.92/3.00  --brand_transform                       false
% 19.92/3.00  --non_eq_to_eq                          false
% 19.92/3.00  --prep_def_merge                        true
% 19.92/3.00  --prep_def_merge_prop_impl              false
% 19.92/3.00  --prep_def_merge_mbd                    true
% 19.92/3.00  --prep_def_merge_tr_red                 false
% 19.92/3.00  --prep_def_merge_tr_cl                  false
% 19.92/3.00  --smt_preprocessing                     true
% 19.92/3.00  --smt_ac_axioms                         fast
% 19.92/3.00  --preprocessed_out                      false
% 19.92/3.00  --preprocessed_stats                    false
% 19.92/3.00  
% 19.92/3.00  ------ Abstraction refinement Options
% 19.92/3.00  
% 19.92/3.00  --abstr_ref                             []
% 19.92/3.00  --abstr_ref_prep                        false
% 19.92/3.00  --abstr_ref_until_sat                   false
% 19.92/3.00  --abstr_ref_sig_restrict                funpre
% 19.92/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.92/3.00  --abstr_ref_under                       []
% 19.92/3.00  
% 19.92/3.00  ------ SAT Options
% 19.92/3.00  
% 19.92/3.00  --sat_mode                              false
% 19.92/3.00  --sat_fm_restart_options                ""
% 19.92/3.00  --sat_gr_def                            false
% 19.92/3.00  --sat_epr_types                         true
% 19.92/3.00  --sat_non_cyclic_types                  false
% 19.92/3.00  --sat_finite_models                     false
% 19.92/3.00  --sat_fm_lemmas                         false
% 19.92/3.00  --sat_fm_prep                           false
% 19.92/3.00  --sat_fm_uc_incr                        true
% 19.92/3.00  --sat_out_model                         small
% 19.92/3.00  --sat_out_clauses                       false
% 19.92/3.00  
% 19.92/3.00  ------ QBF Options
% 19.92/3.00  
% 19.92/3.00  --qbf_mode                              false
% 19.92/3.00  --qbf_elim_univ                         false
% 19.92/3.00  --qbf_dom_inst                          none
% 19.92/3.00  --qbf_dom_pre_inst                      false
% 19.92/3.00  --qbf_sk_in                             false
% 19.92/3.00  --qbf_pred_elim                         true
% 19.92/3.00  --qbf_split                             512
% 19.92/3.00  
% 19.92/3.00  ------ BMC1 Options
% 19.92/3.00  
% 19.92/3.00  --bmc1_incremental                      false
% 19.92/3.00  --bmc1_axioms                           reachable_all
% 19.92/3.00  --bmc1_min_bound                        0
% 19.92/3.00  --bmc1_max_bound                        -1
% 19.92/3.00  --bmc1_max_bound_default                -1
% 19.92/3.00  --bmc1_symbol_reachability              true
% 19.92/3.00  --bmc1_property_lemmas                  false
% 19.92/3.00  --bmc1_k_induction                      false
% 19.92/3.00  --bmc1_non_equiv_states                 false
% 19.92/3.00  --bmc1_deadlock                         false
% 19.92/3.00  --bmc1_ucm                              false
% 19.92/3.00  --bmc1_add_unsat_core                   none
% 19.92/3.00  --bmc1_unsat_core_children              false
% 19.92/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.92/3.00  --bmc1_out_stat                         full
% 19.92/3.00  --bmc1_ground_init                      false
% 19.92/3.00  --bmc1_pre_inst_next_state              false
% 19.92/3.00  --bmc1_pre_inst_state                   false
% 19.92/3.00  --bmc1_pre_inst_reach_state             false
% 19.92/3.00  --bmc1_out_unsat_core                   false
% 19.92/3.00  --bmc1_aig_witness_out                  false
% 19.92/3.00  --bmc1_verbose                          false
% 19.92/3.00  --bmc1_dump_clauses_tptp                false
% 19.92/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.92/3.00  --bmc1_dump_file                        -
% 19.92/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.92/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.92/3.00  --bmc1_ucm_extend_mode                  1
% 19.92/3.00  --bmc1_ucm_init_mode                    2
% 19.92/3.00  --bmc1_ucm_cone_mode                    none
% 19.92/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.92/3.00  --bmc1_ucm_relax_model                  4
% 19.92/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.92/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.92/3.00  --bmc1_ucm_layered_model                none
% 19.92/3.00  --bmc1_ucm_max_lemma_size               10
% 19.92/3.00  
% 19.92/3.00  ------ AIG Options
% 19.92/3.00  
% 19.92/3.00  --aig_mode                              false
% 19.92/3.00  
% 19.92/3.00  ------ Instantiation Options
% 19.92/3.00  
% 19.92/3.00  --instantiation_flag                    true
% 19.92/3.00  --inst_sos_flag                         false
% 19.92/3.00  --inst_sos_phase                        true
% 19.92/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.92/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.92/3.00  --inst_lit_sel_side                     num_symb
% 19.92/3.00  --inst_solver_per_active                1400
% 19.92/3.00  --inst_solver_calls_frac                1.
% 19.92/3.00  --inst_passive_queue_type               priority_queues
% 19.92/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.92/3.00  --inst_passive_queues_freq              [25;2]
% 19.92/3.00  --inst_dismatching                      true
% 19.92/3.00  --inst_eager_unprocessed_to_passive     true
% 19.92/3.00  --inst_prop_sim_given                   true
% 19.92/3.00  --inst_prop_sim_new                     false
% 19.92/3.00  --inst_subs_new                         false
% 19.92/3.00  --inst_eq_res_simp                      false
% 19.92/3.00  --inst_subs_given                       false
% 19.92/3.00  --inst_orphan_elimination               true
% 19.92/3.00  --inst_learning_loop_flag               true
% 19.92/3.00  --inst_learning_start                   3000
% 19.92/3.00  --inst_learning_factor                  2
% 19.92/3.00  --inst_start_prop_sim_after_learn       3
% 19.92/3.00  --inst_sel_renew                        solver
% 19.92/3.00  --inst_lit_activity_flag                true
% 19.92/3.00  --inst_restr_to_given                   false
% 19.92/3.00  --inst_activity_threshold               500
% 19.92/3.00  --inst_out_proof                        true
% 19.92/3.00  
% 19.92/3.00  ------ Resolution Options
% 19.92/3.00  
% 19.92/3.00  --resolution_flag                       true
% 19.92/3.00  --res_lit_sel                           adaptive
% 19.92/3.00  --res_lit_sel_side                      none
% 19.92/3.00  --res_ordering                          kbo
% 19.92/3.00  --res_to_prop_solver                    active
% 19.92/3.00  --res_prop_simpl_new                    false
% 19.92/3.00  --res_prop_simpl_given                  true
% 19.92/3.00  --res_passive_queue_type                priority_queues
% 19.92/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.92/3.00  --res_passive_queues_freq               [15;5]
% 19.92/3.00  --res_forward_subs                      full
% 19.92/3.00  --res_backward_subs                     full
% 19.92/3.00  --res_forward_subs_resolution           true
% 19.92/3.00  --res_backward_subs_resolution          true
% 19.92/3.00  --res_orphan_elimination                true
% 19.92/3.00  --res_time_limit                        2.
% 19.92/3.00  --res_out_proof                         true
% 19.92/3.00  
% 19.92/3.00  ------ Superposition Options
% 19.92/3.00  
% 19.92/3.00  --superposition_flag                    true
% 19.92/3.00  --sup_passive_queue_type                priority_queues
% 19.92/3.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.92/3.00  --sup_passive_queues_freq               [1;4]
% 19.92/3.00  --demod_completeness_check              fast
% 19.92/3.00  --demod_use_ground                      true
% 19.92/3.00  --sup_to_prop_solver                    passive
% 19.92/3.00  --sup_prop_simpl_new                    true
% 19.92/3.00  --sup_prop_simpl_given                  true
% 19.92/3.00  --sup_fun_splitting                     false
% 19.92/3.00  --sup_smt_interval                      50000
% 19.92/3.00  
% 19.92/3.00  ------ Superposition Simplification Setup
% 19.92/3.00  
% 19.92/3.00  --sup_indices_passive                   []
% 19.92/3.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.92/3.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.92/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.92/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.92/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.92/3.00  --sup_full_bw                           [BwDemod]
% 19.92/3.00  --sup_immed_triv                        [TrivRules]
% 19.92/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.92/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.92/3.00  --sup_immed_bw_main                     []
% 19.92/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.92/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.92/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.92/3.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.92/3.00  
% 19.92/3.00  ------ Combination Options
% 19.92/3.00  
% 19.92/3.00  --comb_res_mult                         3
% 19.92/3.00  --comb_sup_mult                         2
% 19.92/3.00  --comb_inst_mult                        10
% 19.92/3.00  
% 19.92/3.00  ------ Debug Options
% 19.92/3.00  
% 19.92/3.00  --dbg_backtrace                         false
% 19.92/3.00  --dbg_dump_prop_clauses                 false
% 19.92/3.00  --dbg_dump_prop_clauses_file            -
% 19.92/3.00  --dbg_out_stat                          false
% 19.92/3.00  ------ Parsing...
% 19.92/3.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.92/3.00  
% 19.92/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 19.92/3.00  
% 19.92/3.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.92/3.00  
% 19.92/3.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.92/3.00  ------ Proving...
% 19.92/3.00  ------ Problem Properties 
% 19.92/3.00  
% 19.92/3.00  
% 19.92/3.00  clauses                                 17
% 19.92/3.00  conjectures                             3
% 19.92/3.00  EPR                                     1
% 19.92/3.00  Horn                                    10
% 19.92/3.00  unary                                   4
% 19.92/3.00  binary                                  5
% 19.92/3.00  lits                                    38
% 19.92/3.00  lits eq                                 9
% 19.92/3.00  fd_pure                                 0
% 19.92/3.00  fd_pseudo                               0
% 19.92/3.00  fd_cond                                 0
% 19.92/3.00  fd_pseudo_cond                          2
% 19.92/3.00  AC symbols                              0
% 19.92/3.00  
% 19.92/3.00  ------ Input Options Time Limit: Unbounded
% 19.92/3.00  
% 19.92/3.00  
% 19.92/3.00  ------ 
% 19.92/3.00  Current options:
% 19.92/3.00  ------ 
% 19.92/3.00  
% 19.92/3.00  ------ Input Options
% 19.92/3.00  
% 19.92/3.00  --out_options                           all
% 19.92/3.00  --tptp_safe_out                         true
% 19.92/3.00  --problem_path                          ""
% 19.92/3.00  --include_path                          ""
% 19.92/3.00  --clausifier                            res/vclausify_rel
% 19.92/3.00  --clausifier_options                    --mode clausify
% 19.92/3.00  --stdin                                 false
% 19.92/3.00  --stats_out                             sel
% 19.92/3.00  
% 19.92/3.00  ------ General Options
% 19.92/3.00  
% 19.92/3.00  --fof                                   false
% 19.92/3.00  --time_out_real                         604.99
% 19.92/3.00  --time_out_virtual                      -1.
% 19.92/3.00  --symbol_type_check                     false
% 19.92/3.00  --clausify_out                          false
% 19.92/3.00  --sig_cnt_out                           false
% 19.92/3.00  --trig_cnt_out                          false
% 19.92/3.00  --trig_cnt_out_tolerance                1.
% 19.92/3.00  --trig_cnt_out_sk_spl                   false
% 19.92/3.00  --abstr_cl_out                          false
% 19.92/3.00  
% 19.92/3.00  ------ Global Options
% 19.92/3.00  
% 19.92/3.00  --schedule                              none
% 19.92/3.00  --add_important_lit                     false
% 19.92/3.00  --prop_solver_per_cl                    1000
% 19.92/3.00  --min_unsat_core                        false
% 19.92/3.00  --soft_assumptions                      false
% 19.92/3.00  --soft_lemma_size                       3
% 19.92/3.00  --prop_impl_unit_size                   0
% 19.92/3.00  --prop_impl_unit                        []
% 19.92/3.00  --share_sel_clauses                     true
% 19.92/3.00  --reset_solvers                         false
% 19.92/3.00  --bc_imp_inh                            [conj_cone]
% 19.92/3.00  --conj_cone_tolerance                   3.
% 19.92/3.00  --extra_neg_conj                        none
% 19.92/3.00  --large_theory_mode                     true
% 19.92/3.00  --prolific_symb_bound                   200
% 19.92/3.00  --lt_threshold                          2000
% 19.92/3.00  --clause_weak_htbl                      true
% 19.92/3.00  --gc_record_bc_elim                     false
% 19.92/3.00  
% 19.92/3.00  ------ Preprocessing Options
% 19.92/3.00  
% 19.92/3.00  --preprocessing_flag                    true
% 19.92/3.00  --time_out_prep_mult                    0.1
% 19.92/3.00  --splitting_mode                        input
% 19.92/3.00  --splitting_grd                         true
% 19.92/3.00  --splitting_cvd                         false
% 19.92/3.00  --splitting_cvd_svl                     false
% 19.92/3.00  --splitting_nvd                         32
% 19.92/3.00  --sub_typing                            true
% 19.92/3.00  --prep_gs_sim                           false
% 19.92/3.00  --prep_unflatten                        true
% 19.92/3.00  --prep_res_sim                          true
% 19.92/3.00  --prep_upred                            true
% 19.92/3.00  --prep_sem_filter                       exhaustive
% 19.92/3.00  --prep_sem_filter_out                   false
% 19.92/3.00  --pred_elim                             false
% 19.92/3.00  --res_sim_input                         true
% 19.92/3.00  --eq_ax_congr_red                       true
% 19.92/3.00  --pure_diseq_elim                       true
% 19.92/3.00  --brand_transform                       false
% 19.92/3.00  --non_eq_to_eq                          false
% 19.92/3.00  --prep_def_merge                        true
% 19.92/3.00  --prep_def_merge_prop_impl              false
% 19.92/3.00  --prep_def_merge_mbd                    true
% 19.92/3.00  --prep_def_merge_tr_red                 false
% 19.92/3.00  --prep_def_merge_tr_cl                  false
% 19.92/3.00  --smt_preprocessing                     true
% 19.92/3.00  --smt_ac_axioms                         fast
% 19.92/3.00  --preprocessed_out                      false
% 19.92/3.00  --preprocessed_stats                    false
% 19.92/3.00  
% 19.92/3.00  ------ Abstraction refinement Options
% 19.92/3.00  
% 19.92/3.00  --abstr_ref                             []
% 19.92/3.00  --abstr_ref_prep                        false
% 19.92/3.00  --abstr_ref_until_sat                   false
% 19.92/3.00  --abstr_ref_sig_restrict                funpre
% 19.92/3.00  --abstr_ref_af_restrict_to_split_sk     false
% 19.92/3.00  --abstr_ref_under                       []
% 19.92/3.00  
% 19.92/3.00  ------ SAT Options
% 19.92/3.00  
% 19.92/3.00  --sat_mode                              false
% 19.92/3.00  --sat_fm_restart_options                ""
% 19.92/3.00  --sat_gr_def                            false
% 19.92/3.00  --sat_epr_types                         true
% 19.92/3.00  --sat_non_cyclic_types                  false
% 19.92/3.00  --sat_finite_models                     false
% 19.92/3.00  --sat_fm_lemmas                         false
% 19.92/3.00  --sat_fm_prep                           false
% 19.92/3.00  --sat_fm_uc_incr                        true
% 19.92/3.00  --sat_out_model                         small
% 19.92/3.00  --sat_out_clauses                       false
% 19.92/3.00  
% 19.92/3.00  ------ QBF Options
% 19.92/3.00  
% 19.92/3.00  --qbf_mode                              false
% 19.92/3.00  --qbf_elim_univ                         false
% 19.92/3.00  --qbf_dom_inst                          none
% 19.92/3.00  --qbf_dom_pre_inst                      false
% 19.92/3.00  --qbf_sk_in                             false
% 19.92/3.00  --qbf_pred_elim                         true
% 19.92/3.00  --qbf_split                             512
% 19.92/3.00  
% 19.92/3.00  ------ BMC1 Options
% 19.92/3.00  
% 19.92/3.00  --bmc1_incremental                      false
% 19.92/3.00  --bmc1_axioms                           reachable_all
% 19.92/3.00  --bmc1_min_bound                        0
% 19.92/3.00  --bmc1_max_bound                        -1
% 19.92/3.00  --bmc1_max_bound_default                -1
% 19.92/3.00  --bmc1_symbol_reachability              true
% 19.92/3.00  --bmc1_property_lemmas                  false
% 19.92/3.00  --bmc1_k_induction                      false
% 19.92/3.00  --bmc1_non_equiv_states                 false
% 19.92/3.00  --bmc1_deadlock                         false
% 19.92/3.00  --bmc1_ucm                              false
% 19.92/3.00  --bmc1_add_unsat_core                   none
% 19.92/3.00  --bmc1_unsat_core_children              false
% 19.92/3.00  --bmc1_unsat_core_extrapolate_axioms    false
% 19.92/3.00  --bmc1_out_stat                         full
% 19.92/3.00  --bmc1_ground_init                      false
% 19.92/3.00  --bmc1_pre_inst_next_state              false
% 19.92/3.00  --bmc1_pre_inst_state                   false
% 19.92/3.00  --bmc1_pre_inst_reach_state             false
% 19.92/3.00  --bmc1_out_unsat_core                   false
% 19.92/3.00  --bmc1_aig_witness_out                  false
% 19.92/3.00  --bmc1_verbose                          false
% 19.92/3.00  --bmc1_dump_clauses_tptp                false
% 19.92/3.00  --bmc1_dump_unsat_core_tptp             false
% 19.92/3.00  --bmc1_dump_file                        -
% 19.92/3.00  --bmc1_ucm_expand_uc_limit              128
% 19.92/3.00  --bmc1_ucm_n_expand_iterations          6
% 19.92/3.00  --bmc1_ucm_extend_mode                  1
% 19.92/3.00  --bmc1_ucm_init_mode                    2
% 19.92/3.00  --bmc1_ucm_cone_mode                    none
% 19.92/3.00  --bmc1_ucm_reduced_relation_type        0
% 19.92/3.00  --bmc1_ucm_relax_model                  4
% 19.92/3.00  --bmc1_ucm_full_tr_after_sat            true
% 19.92/3.00  --bmc1_ucm_expand_neg_assumptions       false
% 19.92/3.00  --bmc1_ucm_layered_model                none
% 19.92/3.00  --bmc1_ucm_max_lemma_size               10
% 19.92/3.00  
% 19.92/3.00  ------ AIG Options
% 19.92/3.00  
% 19.92/3.00  --aig_mode                              false
% 19.92/3.00  
% 19.92/3.00  ------ Instantiation Options
% 19.92/3.00  
% 19.92/3.00  --instantiation_flag                    true
% 19.92/3.00  --inst_sos_flag                         false
% 19.92/3.00  --inst_sos_phase                        true
% 19.92/3.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.92/3.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.92/3.00  --inst_lit_sel_side                     num_symb
% 19.92/3.00  --inst_solver_per_active                1400
% 19.92/3.00  --inst_solver_calls_frac                1.
% 19.92/3.00  --inst_passive_queue_type               priority_queues
% 19.92/3.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.92/3.00  --inst_passive_queues_freq              [25;2]
% 19.92/3.00  --inst_dismatching                      true
% 19.92/3.00  --inst_eager_unprocessed_to_passive     true
% 19.92/3.00  --inst_prop_sim_given                   true
% 19.92/3.00  --inst_prop_sim_new                     false
% 19.92/3.00  --inst_subs_new                         false
% 19.92/3.00  --inst_eq_res_simp                      false
% 19.92/3.00  --inst_subs_given                       false
% 19.92/3.00  --inst_orphan_elimination               true
% 19.92/3.00  --inst_learning_loop_flag               true
% 19.92/3.00  --inst_learning_start                   3000
% 19.92/3.00  --inst_learning_factor                  2
% 19.92/3.00  --inst_start_prop_sim_after_learn       3
% 19.92/3.00  --inst_sel_renew                        solver
% 19.92/3.00  --inst_lit_activity_flag                true
% 19.92/3.00  --inst_restr_to_given                   false
% 19.92/3.00  --inst_activity_threshold               500
% 19.92/3.00  --inst_out_proof                        true
% 19.92/3.00  
% 19.92/3.00  ------ Resolution Options
% 19.92/3.00  
% 19.92/3.00  --resolution_flag                       true
% 19.92/3.00  --res_lit_sel                           adaptive
% 19.92/3.00  --res_lit_sel_side                      none
% 19.92/3.00  --res_ordering                          kbo
% 19.92/3.00  --res_to_prop_solver                    active
% 19.92/3.00  --res_prop_simpl_new                    false
% 19.92/3.00  --res_prop_simpl_given                  true
% 19.92/3.00  --res_passive_queue_type                priority_queues
% 19.92/3.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.92/3.00  --res_passive_queues_freq               [15;5]
% 19.92/3.00  --res_forward_subs                      full
% 19.92/3.00  --res_backward_subs                     full
% 19.92/3.00  --res_forward_subs_resolution           true
% 19.92/3.00  --res_backward_subs_resolution          true
% 19.92/3.00  --res_orphan_elimination                true
% 19.92/3.00  --res_time_limit                        2.
% 19.92/3.00  --res_out_proof                         true
% 19.92/3.00  
% 19.92/3.00  ------ Superposition Options
% 19.92/3.00  
% 19.92/3.00  --superposition_flag                    true
% 19.92/3.00  --sup_passive_queue_type                priority_queues
% 19.92/3.00  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.92/3.00  --sup_passive_queues_freq               [1;4]
% 19.92/3.00  --demod_completeness_check              fast
% 19.92/3.00  --demod_use_ground                      true
% 19.92/3.00  --sup_to_prop_solver                    passive
% 19.92/3.00  --sup_prop_simpl_new                    true
% 19.92/3.00  --sup_prop_simpl_given                  true
% 19.92/3.00  --sup_fun_splitting                     false
% 19.92/3.00  --sup_smt_interval                      50000
% 19.92/3.00  
% 19.92/3.00  ------ Superposition Simplification Setup
% 19.92/3.00  
% 19.92/3.00  --sup_indices_passive                   []
% 19.92/3.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.92/3.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.92/3.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.92/3.00  --sup_full_triv                         [TrivRules;PropSubs]
% 19.92/3.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.92/3.00  --sup_full_bw                           [BwDemod]
% 19.92/3.00  --sup_immed_triv                        [TrivRules]
% 19.92/3.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.92/3.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.92/3.00  --sup_immed_bw_main                     []
% 19.92/3.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.92/3.00  --sup_input_triv                        [Unflattening;TrivRules]
% 19.92/3.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.92/3.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.92/3.00  
% 19.92/3.00  ------ Combination Options
% 19.92/3.00  
% 19.92/3.00  --comb_res_mult                         3
% 19.92/3.00  --comb_sup_mult                         2
% 19.92/3.00  --comb_inst_mult                        10
% 19.92/3.00  
% 19.92/3.00  ------ Debug Options
% 19.92/3.00  
% 19.92/3.00  --dbg_backtrace                         false
% 19.92/3.00  --dbg_dump_prop_clauses                 false
% 19.92/3.00  --dbg_dump_prop_clauses_file            -
% 19.92/3.00  --dbg_out_stat                          false
% 19.92/3.00  
% 19.92/3.00  
% 19.92/3.00  
% 19.92/3.00  
% 19.92/3.00  ------ Proving...
% 19.92/3.00  
% 19.92/3.00  
% 19.92/3.00  % SZS status Theorem for theBenchmark.p
% 19.92/3.00  
% 19.92/3.00  % SZS output start CNFRefutation for theBenchmark.p
% 19.92/3.00  
% 19.92/3.00  fof(f4,axiom,(
% 19.92/3.00    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 19.92/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.92/3.00  
% 19.92/3.00  fof(f39,plain,(
% 19.92/3.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 19.92/3.00    inference(cnf_transformation,[],[f4])).
% 19.92/3.00  
% 19.92/3.00  fof(f5,axiom,(
% 19.92/3.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 19.92/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.92/3.00  
% 19.92/3.00  fof(f40,plain,(
% 19.92/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 19.92/3.00    inference(cnf_transformation,[],[f5])).
% 19.92/3.00  
% 19.92/3.00  fof(f60,plain,(
% 19.92/3.00    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1)) )),
% 19.92/3.00    inference(definition_unfolding,[],[f39,f40])).
% 19.92/3.00  
% 19.92/3.00  fof(f2,axiom,(
% 19.92/3.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 19.92/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.92/3.00  
% 19.92/3.00  fof(f17,plain,(
% 19.92/3.00    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 19.92/3.00    inference(ennf_transformation,[],[f2])).
% 19.92/3.00  
% 19.92/3.00  fof(f20,plain,(
% 19.92/3.00    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 19.92/3.00    inference(nnf_transformation,[],[f17])).
% 19.92/3.00  
% 19.92/3.00  fof(f34,plain,(
% 19.92/3.00    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 19.92/3.00    inference(cnf_transformation,[],[f20])).
% 19.92/3.00  
% 19.92/3.00  fof(f1,axiom,(
% 19.92/3.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 19.92/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.92/3.00  
% 19.92/3.00  fof(f31,plain,(
% 19.92/3.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 19.92/3.00    inference(cnf_transformation,[],[f1])).
% 19.92/3.00  
% 19.92/3.00  fof(f61,plain,(
% 19.92/3.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 19.92/3.00    inference(definition_unfolding,[],[f31,f40,f40])).
% 19.92/3.00  
% 19.92/3.00  fof(f32,plain,(
% 19.92/3.00    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 19.92/3.00    inference(cnf_transformation,[],[f20])).
% 19.92/3.00  
% 19.92/3.00  fof(f6,axiom,(
% 19.92/3.00    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 19.92/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.92/3.00  
% 19.92/3.00  fof(f41,plain,(
% 19.92/3.00    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 19.92/3.00    inference(cnf_transformation,[],[f6])).
% 19.92/3.00  
% 19.92/3.00  fof(f3,axiom,(
% 19.92/3.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.92/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.92/3.00  
% 19.92/3.00  fof(f16,plain,(
% 19.92/3.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 19.92/3.00    inference(rectify,[],[f3])).
% 19.92/3.00  
% 19.92/3.00  fof(f18,plain,(
% 19.92/3.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 19.92/3.00    inference(ennf_transformation,[],[f16])).
% 19.92/3.00  
% 19.92/3.00  fof(f21,plain,(
% 19.92/3.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 19.92/3.00    introduced(choice_axiom,[])).
% 19.92/3.00  
% 19.92/3.00  fof(f22,plain,(
% 19.92/3.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 19.92/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f21])).
% 19.92/3.00  
% 19.92/3.00  fof(f38,plain,(
% 19.92/3.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 19.92/3.00    inference(cnf_transformation,[],[f22])).
% 19.92/3.00  
% 19.92/3.00  fof(f14,conjecture,(
% 19.92/3.00    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 19.92/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.92/3.00  
% 19.92/3.00  fof(f15,negated_conjecture,(
% 19.92/3.00    ~! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 19.92/3.00    inference(negated_conjecture,[],[f14])).
% 19.92/3.00  
% 19.92/3.00  fof(f19,plain,(
% 19.92/3.00    ? [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <~> (X0 != X2 & r2_hidden(X0,X1)))),
% 19.92/3.00    inference(ennf_transformation,[],[f15])).
% 19.92/3.00  
% 19.92/3.00  fof(f27,plain,(
% 19.92/3.00    ? [X0,X1,X2] : (((X0 = X2 | ~r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 19.92/3.00    inference(nnf_transformation,[],[f19])).
% 19.92/3.00  
% 19.92/3.00  fof(f28,plain,(
% 19.92/3.00    ? [X0,X1,X2] : ((X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 19.92/3.00    inference(flattening,[],[f27])).
% 19.92/3.00  
% 19.92/3.00  fof(f29,plain,(
% 19.92/3.00    ? [X0,X1,X2] : ((X0 = X2 | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) & ((X0 != X2 & r2_hidden(X0,X1)) | r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))))) => ((sK2 = sK4 | ~r2_hidden(sK2,sK3) | ~r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4)))) & ((sK2 != sK4 & r2_hidden(sK2,sK3)) | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4)))))),
% 19.92/3.00    introduced(choice_axiom,[])).
% 19.92/3.00  
% 19.92/3.00  fof(f30,plain,(
% 19.92/3.00    (sK2 = sK4 | ~r2_hidden(sK2,sK3) | ~r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4)))) & ((sK2 != sK4 & r2_hidden(sK2,sK3)) | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4))))),
% 19.92/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f28,f29])).
% 19.92/3.00  
% 19.92/3.00  fof(f54,plain,(
% 19.92/3.00    sK2 = sK4 | ~r2_hidden(sK2,sK3) | ~r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4)))),
% 19.92/3.00    inference(cnf_transformation,[],[f30])).
% 19.92/3.00  
% 19.92/3.00  fof(f8,axiom,(
% 19.92/3.00    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 19.92/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.92/3.00  
% 19.92/3.00  fof(f46,plain,(
% 19.92/3.00    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 19.92/3.00    inference(cnf_transformation,[],[f8])).
% 19.92/3.00  
% 19.92/3.00  fof(f9,axiom,(
% 19.92/3.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 19.92/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.92/3.00  
% 19.92/3.00  fof(f47,plain,(
% 19.92/3.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 19.92/3.00    inference(cnf_transformation,[],[f9])).
% 19.92/3.00  
% 19.92/3.00  fof(f10,axiom,(
% 19.92/3.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 19.92/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.92/3.00  
% 19.92/3.00  fof(f48,plain,(
% 19.92/3.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 19.92/3.00    inference(cnf_transformation,[],[f10])).
% 19.92/3.00  
% 19.92/3.00  fof(f11,axiom,(
% 19.92/3.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 19.92/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.92/3.00  
% 19.92/3.00  fof(f49,plain,(
% 19.92/3.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 19.92/3.00    inference(cnf_transformation,[],[f11])).
% 19.92/3.00  
% 19.92/3.00  fof(f12,axiom,(
% 19.92/3.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 19.92/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.92/3.00  
% 19.92/3.00  fof(f50,plain,(
% 19.92/3.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 19.92/3.00    inference(cnf_transformation,[],[f12])).
% 19.92/3.00  
% 19.92/3.00  fof(f13,axiom,(
% 19.92/3.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 19.92/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.92/3.00  
% 19.92/3.00  fof(f51,plain,(
% 19.92/3.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 19.92/3.00    inference(cnf_transformation,[],[f13])).
% 19.92/3.00  
% 19.92/3.00  fof(f55,plain,(
% 19.92/3.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 19.92/3.00    inference(definition_unfolding,[],[f50,f51])).
% 19.92/3.00  
% 19.92/3.00  fof(f56,plain,(
% 19.92/3.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 19.92/3.00    inference(definition_unfolding,[],[f49,f55])).
% 19.92/3.00  
% 19.92/3.00  fof(f57,plain,(
% 19.92/3.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 19.92/3.00    inference(definition_unfolding,[],[f48,f56])).
% 19.92/3.00  
% 19.92/3.00  fof(f58,plain,(
% 19.92/3.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 19.92/3.00    inference(definition_unfolding,[],[f47,f57])).
% 19.92/3.00  
% 19.92/3.00  fof(f59,plain,(
% 19.92/3.00    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 19.92/3.00    inference(definition_unfolding,[],[f46,f58])).
% 19.92/3.00  
% 19.92/3.00  fof(f66,plain,(
% 19.92/3.00    sK2 = sK4 | ~r2_hidden(sK2,sK3) | ~r2_hidden(sK2,k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),
% 19.92/3.00    inference(definition_unfolding,[],[f54,f59])).
% 19.92/3.00  
% 19.92/3.00  fof(f52,plain,(
% 19.92/3.00    r2_hidden(sK2,sK3) | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4)))),
% 19.92/3.00    inference(cnf_transformation,[],[f30])).
% 19.92/3.00  
% 19.92/3.00  fof(f68,plain,(
% 19.92/3.00    r2_hidden(sK2,sK3) | r2_hidden(sK2,k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),
% 19.92/3.00    inference(definition_unfolding,[],[f52,f59])).
% 19.92/3.00  
% 19.92/3.00  fof(f7,axiom,(
% 19.92/3.00    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 19.92/3.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 19.92/3.00  
% 19.92/3.00  fof(f23,plain,(
% 19.92/3.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 19.92/3.00    inference(nnf_transformation,[],[f7])).
% 19.92/3.00  
% 19.92/3.00  fof(f24,plain,(
% 19.92/3.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 19.92/3.00    inference(rectify,[],[f23])).
% 19.92/3.00  
% 19.92/3.00  fof(f25,plain,(
% 19.92/3.00    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1))))),
% 19.92/3.00    introduced(choice_axiom,[])).
% 19.92/3.00  
% 19.92/3.00  fof(f26,plain,(
% 19.92/3.00    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK1(X0,X1) != X0 | ~r2_hidden(sK1(X0,X1),X1)) & (sK1(X0,X1) = X0 | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 19.92/3.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f24,f25])).
% 19.92/3.00  
% 19.92/3.00  fof(f42,plain,(
% 19.92/3.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 19.92/3.00    inference(cnf_transformation,[],[f26])).
% 19.92/3.00  
% 19.92/3.00  fof(f65,plain,(
% 19.92/3.00    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 19.92/3.00    inference(definition_unfolding,[],[f42,f59])).
% 19.92/3.00  
% 19.92/3.00  fof(f71,plain,(
% 19.92/3.00    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X0))) )),
% 19.92/3.00    inference(equality_resolution,[],[f65])).
% 19.92/3.00  
% 19.92/3.00  fof(f53,plain,(
% 19.92/3.00    sK2 != sK4 | r2_hidden(sK2,k4_xboole_0(sK3,k1_tarski(sK4)))),
% 19.92/3.00    inference(cnf_transformation,[],[f30])).
% 19.92/3.00  
% 19.92/3.00  fof(f67,plain,(
% 19.92/3.00    sK2 != sK4 | r2_hidden(sK2,k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))),
% 19.92/3.00    inference(definition_unfolding,[],[f53,f59])).
% 19.92/3.00  
% 19.92/3.00  fof(f43,plain,(
% 19.92/3.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 19.92/3.00    inference(cnf_transformation,[],[f26])).
% 19.92/3.00  
% 19.92/3.00  fof(f64,plain,(
% 19.92/3.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k5_enumset1(X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 19.92/3.00    inference(definition_unfolding,[],[f43,f59])).
% 19.92/3.00  
% 19.92/3.00  fof(f69,plain,(
% 19.92/3.00    ( ! [X3,X1] : (r2_hidden(X3,X1) | k5_enumset1(X3,X3,X3,X3,X3,X3,X3) != X1) )),
% 19.92/3.00    inference(equality_resolution,[],[f64])).
% 19.92/3.00  
% 19.92/3.00  fof(f70,plain,(
% 19.92/3.00    ( ! [X3] : (r2_hidden(X3,k5_enumset1(X3,X3,X3,X3,X3,X3,X3))) )),
% 19.92/3.00    inference(equality_resolution,[],[f69])).
% 19.92/3.00  
% 19.92/3.00  cnf(c_0,plain,
% 19.92/3.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 19.92/3.00      inference(cnf_transformation,[],[f60]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_3,plain,
% 19.92/3.00      ( ~ r2_hidden(X0,X1)
% 19.92/3.00      | r2_hidden(X0,X2)
% 19.92/3.00      | r2_hidden(X0,k5_xboole_0(X1,X2)) ),
% 19.92/3.00      inference(cnf_transformation,[],[f34]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_397,plain,
% 19.92/3.00      ( r2_hidden(X0,X1) != iProver_top
% 19.92/3.00      | r2_hidden(X0,X2) = iProver_top
% 19.92/3.00      | r2_hidden(X0,k5_xboole_0(X1,X2)) = iProver_top ),
% 19.92/3.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_2508,plain,
% 19.92/3.00      ( r2_hidden(X0,X1) != iProver_top
% 19.92/3.00      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top
% 19.92/3.00      | r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = iProver_top ),
% 19.92/3.00      inference(superposition,[status(thm)],[c_0,c_397]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_1,plain,
% 19.92/3.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 19.92/3.00      inference(cnf_transformation,[],[f61]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_5,plain,
% 19.92/3.00      ( r2_hidden(X0,X1)
% 19.92/3.00      | r2_hidden(X0,X2)
% 19.92/3.00      | ~ r2_hidden(X0,k5_xboole_0(X2,X1)) ),
% 19.92/3.00      inference(cnf_transformation,[],[f32]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_395,plain,
% 19.92/3.00      ( r2_hidden(X0,X1) = iProver_top
% 19.92/3.00      | r2_hidden(X0,X2) = iProver_top
% 19.92/3.00      | r2_hidden(X0,k5_xboole_0(X2,X1)) != iProver_top ),
% 19.92/3.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_2312,plain,
% 19.92/3.00      ( r2_hidden(X0,X1) = iProver_top
% 19.92/3.00      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top
% 19.92/3.00      | r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = iProver_top ),
% 19.92/3.00      inference(superposition,[status(thm)],[c_0,c_395]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_9,plain,
% 19.92/3.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
% 19.92/3.00      inference(cnf_transformation,[],[f41]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_391,plain,
% 19.92/3.00      ( r1_xboole_0(k4_xboole_0(X0,X1),X1) = iProver_top ),
% 19.92/3.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_594,plain,
% 19.92/3.00      ( r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) = iProver_top ),
% 19.92/3.00      inference(superposition,[status(thm)],[c_1,c_391]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_6,plain,
% 19.92/3.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X1) | ~ r2_hidden(X2,X0) ),
% 19.92/3.00      inference(cnf_transformation,[],[f38]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_394,plain,
% 19.92/3.00      ( r1_xboole_0(X0,X1) != iProver_top
% 19.92/3.00      | r2_hidden(X2,X1) != iProver_top
% 19.92/3.00      | r2_hidden(X2,X0) != iProver_top ),
% 19.92/3.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_2266,plain,
% 19.92/3.00      ( r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top
% 19.92/3.00      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 19.92/3.00      inference(superposition,[status(thm)],[c_594,c_394]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_586,plain,
% 19.92/3.00      ( k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) = k4_xboole_0(X0,X1) ),
% 19.92/3.00      inference(superposition,[status(thm)],[c_1,c_0]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_2314,plain,
% 19.92/3.00      ( r2_hidden(X0,X1) = iProver_top
% 19.92/3.00      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top
% 19.92/3.00      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) = iProver_top ),
% 19.92/3.00      inference(superposition,[status(thm)],[c_586,c_395]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_4288,plain,
% 19.92/3.00      ( r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top
% 19.92/3.00      | r2_hidden(X0,X1) = iProver_top ),
% 19.92/3.00      inference(global_propositional_subsumption,
% 19.92/3.00                [status(thm)],
% 19.92/3.00                [c_2312,c_2266,c_2314]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_4289,plain,
% 19.92/3.00      ( r2_hidden(X0,X1) = iProver_top
% 19.92/3.00      | r2_hidden(X0,k4_xboole_0(X1,X2)) != iProver_top ),
% 19.92/3.00      inference(renaming,[status(thm)],[c_4288]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_4300,plain,
% 19.92/3.00      ( r2_hidden(X0,X1) = iProver_top
% 19.92/3.00      | r2_hidden(X0,k4_xboole_0(X2,k4_xboole_0(X2,X1))) != iProver_top ),
% 19.92/3.00      inference(superposition,[status(thm)],[c_1,c_4289]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_5250,plain,
% 19.92/3.00      ( r2_hidden(X0,X1) != iProver_top
% 19.92/3.00      | r2_hidden(X0,X2) = iProver_top
% 19.92/3.00      | r2_hidden(X0,k4_xboole_0(X1,X2)) = iProver_top ),
% 19.92/3.00      inference(superposition,[status(thm)],[c_2508,c_4300]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_14,negated_conjecture,
% 19.92/3.00      ( ~ r2_hidden(sK2,k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
% 19.92/3.00      | ~ r2_hidden(sK2,sK3)
% 19.92/3.00      | sK2 = sK4 ),
% 19.92/3.00      inference(cnf_transformation,[],[f66]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_386,plain,
% 19.92/3.00      ( sK2 = sK4
% 19.92/3.00      | r2_hidden(sK2,k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))) != iProver_top
% 19.92/3.00      | r2_hidden(sK2,sK3) != iProver_top ),
% 19.92/3.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_80182,plain,
% 19.92/3.00      ( sK4 = sK2
% 19.92/3.00      | r2_hidden(sK2,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) = iProver_top
% 19.92/3.00      | r2_hidden(sK2,sK3) != iProver_top ),
% 19.92/3.00      inference(superposition,[status(thm)],[c_5250,c_386]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_145,plain,
% 19.92/3.00      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 19.92/3.00      theory(equality) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_827,plain,
% 19.92/3.00      ( ~ r2_hidden(X0,X1)
% 19.92/3.00      | r2_hidden(sK2,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 19.92/3.00      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) != X1
% 19.92/3.00      | sK2 != X0 ),
% 19.92/3.00      inference(instantiation,[status(thm)],[c_145]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_6753,plain,
% 19.92/3.00      ( ~ r2_hidden(X0,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 19.92/3.00      | r2_hidden(sK2,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 19.92/3.00      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 19.92/3.00      | sK2 != X0 ),
% 19.92/3.00      inference(instantiation,[status(thm)],[c_827]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_6756,plain,
% 19.92/3.00      ( ~ r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 19.92/3.00      | r2_hidden(sK2,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 19.92/3.00      | k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) != k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 19.92/3.00      | sK2 != sK4 ),
% 19.92/3.00      inference(instantiation,[status(thm)],[c_6753]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_16,negated_conjecture,
% 19.92/3.00      ( r2_hidden(sK2,k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
% 19.92/3.00      | r2_hidden(sK2,sK3) ),
% 19.92/3.00      inference(cnf_transformation,[],[f68]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_384,plain,
% 19.92/3.00      ( r2_hidden(sK2,k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))) = iProver_top
% 19.92/3.00      | r2_hidden(sK2,sK3) = iProver_top ),
% 19.92/3.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_4299,plain,
% 19.92/3.00      ( r2_hidden(sK2,sK3) = iProver_top ),
% 19.92/3.00      inference(superposition,[status(thm)],[c_384,c_4289]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_781,plain,
% 19.92/3.00      ( ~ r1_xboole_0(k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)
% 19.92/3.00      | ~ r2_hidden(sK2,X0)
% 19.92/3.00      | r2_hidden(sK2,sK3) ),
% 19.92/3.00      inference(resolution,[status(thm)],[c_6,c_16]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_1247,plain,
% 19.92/3.00      ( ~ r2_hidden(sK2,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 19.92/3.00      | r2_hidden(sK2,sK3) ),
% 19.92/3.00      inference(resolution,[status(thm)],[c_781,c_9]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_13,plain,
% 19.92/3.00      ( ~ r2_hidden(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | X0 = X1 ),
% 19.92/3.00      inference(cnf_transformation,[],[f71]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_626,plain,
% 19.92/3.00      ( ~ r2_hidden(sK2,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 19.92/3.00      | sK2 = sK4 ),
% 19.92/3.00      inference(instantiation,[status(thm)],[c_13]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_15,negated_conjecture,
% 19.92/3.00      ( r2_hidden(sK2,k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)))
% 19.92/3.00      | sK2 != sK4 ),
% 19.92/3.00      inference(cnf_transformation,[],[f67]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_782,plain,
% 19.92/3.00      ( ~ r1_xboole_0(k4_xboole_0(sK3,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)),X0)
% 19.92/3.00      | ~ r2_hidden(sK2,X0)
% 19.92/3.00      | sK2 != sK4 ),
% 19.92/3.00      inference(resolution,[status(thm)],[c_6,c_15]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_1441,plain,
% 19.92/3.00      ( ~ r2_hidden(sK2,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 19.92/3.00      | sK2 != sK4 ),
% 19.92/3.00      inference(resolution,[status(thm)],[c_782,c_9]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_1444,plain,
% 19.92/3.00      ( ~ r2_hidden(sK2,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 19.92/3.00      inference(global_propositional_subsumption,
% 19.92/3.00                [status(thm)],
% 19.92/3.00                [c_1247,c_626,c_1441]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_1446,plain,
% 19.92/3.00      ( r2_hidden(sK2,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) != iProver_top ),
% 19.92/3.00      inference(predicate_to_equality,[status(thm)],[c_1444]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_141,plain,( X0 = X0 ),theory(equality) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_851,plain,
% 19.92/3.00      ( sK2 = sK2 ),
% 19.92/3.00      inference(instantiation,[status(thm)],[c_141]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_142,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_629,plain,
% 19.92/3.00      ( sK4 != X0 | sK2 != X0 | sK2 = sK4 ),
% 19.92/3.00      inference(instantiation,[status(thm)],[c_142]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_850,plain,
% 19.92/3.00      ( sK4 != sK2 | sK2 = sK4 | sK2 != sK2 ),
% 19.92/3.00      inference(instantiation,[status(thm)],[c_629]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_147,plain,
% 19.92/3.00      ( X0 != X1
% 19.92/3.00      | X2 != X3
% 19.92/3.00      | X4 != X5
% 19.92/3.00      | X6 != X7
% 19.92/3.00      | X8 != X9
% 19.92/3.00      | X10 != X11
% 19.92/3.00      | X12 != X13
% 19.92/3.00      | k5_enumset1(X0,X2,X4,X6,X8,X10,X12) = k5_enumset1(X1,X3,X5,X7,X9,X11,X13) ),
% 19.92/3.00      theory(equality) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_152,plain,
% 19.92/3.00      ( k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4) = k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)
% 19.92/3.00      | sK4 != sK4 ),
% 19.92/3.00      inference(instantiation,[status(thm)],[c_147]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_12,plain,
% 19.92/3.00      ( r2_hidden(X0,k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) ),
% 19.92/3.00      inference(cnf_transformation,[],[f70]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_24,plain,
% 19.92/3.00      ( r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4)) ),
% 19.92/3.00      inference(instantiation,[status(thm)],[c_12]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(c_21,plain,
% 19.92/3.00      ( ~ r2_hidden(sK4,k5_enumset1(sK4,sK4,sK4,sK4,sK4,sK4,sK4))
% 19.92/3.00      | sK4 = sK4 ),
% 19.92/3.00      inference(instantiation,[status(thm)],[c_13]) ).
% 19.92/3.00  
% 19.92/3.00  cnf(contradiction,plain,
% 19.92/3.00      ( $false ),
% 19.92/3.00      inference(minisat,
% 19.92/3.00                [status(thm)],
% 19.92/3.00                [c_80182,c_6756,c_4299,c_1446,c_1444,c_851,c_850,c_152,
% 19.92/3.00                 c_24,c_21]) ).
% 19.92/3.00  
% 19.92/3.00  
% 19.92/3.00  % SZS output end CNFRefutation for theBenchmark.p
% 19.92/3.00  
% 19.92/3.00  ------                               Statistics
% 19.92/3.00  
% 19.92/3.00  ------ Selected
% 19.92/3.00  
% 19.92/3.00  total_time:                             2.378
% 19.92/3.00  
%------------------------------------------------------------------------------
